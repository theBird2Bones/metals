package scala.meta.internal.metals

import java.nio.file.Path
import java.nio.file.Paths
import java.util.Collections
import java.util.concurrent.ScheduledExecutorService
import java.{util => ju}

import scala.annotation.nowarn
import scala.annotation.tailrec
import scala.collection.concurrent.TrieMap
import scala.collection.mutable.ArrayBuffer
import scala.concurrent.ExecutionContextExecutorService
import scala.concurrent.Future
import scala.util.control.NonFatal

import scala.meta._
import scala.meta.inputs.Input
import scala.meta.inputs.Position
import scala.meta.internal
import scala.meta.internal.builds.SbtBuildTool
import scala.meta.internal.metals.CompilerOffsetParamsUtils
import scala.meta.internal.metals.CompilerRangeParamsUtils
import scala.meta.internal.metals.Compilers.PresentationCompilerKey
import scala.meta.internal.metals.MetalsEnrichments._
import scala.meta.internal.mtags.MD5
import scala.meta.internal.parsing.Trees
import scala.meta.internal.pc.LogMessages
import scala.meta.internal.pc.PcSymbolInformation
import scala.meta.internal.worksheets.WorksheetPcData
import scala.meta.internal.worksheets.WorksheetProvider
import scala.meta.internal.{semanticdb => s}
import scala.meta.io.AbsolutePath
import scala.meta.pc.AutoImportsResult
import scala.meta.pc.CancelToken
import scala.meta.pc.CodeActionId
import scala.meta.pc.CompletionItemPriority
import scala.meta.pc.HoverSignature
import scala.meta.pc.OffsetParams
import scala.meta.pc.PresentationCompiler
import scala.meta.pc.SymbolSearch
import scala.meta.pc.SyntheticDecorationsParams

import ch.epfl.scala.bsp4j.BuildTargetIdentifier
import ch.epfl.scala.bsp4j.CompileReport
import org.eclipse.lsp4j.CompletionItem
import org.eclipse.lsp4j.CompletionItemKind
import org.eclipse.lsp4j.CompletionList
import org.eclipse.lsp4j.CompletionParams
import org.eclipse.lsp4j.Diagnostic
import org.eclipse.lsp4j.DocumentHighlight
import org.eclipse.lsp4j.InitializeParams
import org.eclipse.lsp4j.InlayHint
import org.eclipse.lsp4j.InlayHintKind
import org.eclipse.lsp4j.InlayHintParams
import org.eclipse.lsp4j.ReferenceParams
import org.eclipse.lsp4j.RenameParams
import org.eclipse.lsp4j.SelectionRange
import org.eclipse.lsp4j.SelectionRangeParams
import org.eclipse.lsp4j.SemanticTokens
import org.eclipse.lsp4j.SemanticTokensParams
import org.eclipse.lsp4j.SignatureHelp
import org.eclipse.lsp4j.TextDocumentIdentifier
import org.eclipse.lsp4j.TextDocumentPositionParams
import org.eclipse.lsp4j.TextEdit
import org.eclipse.lsp4j.jsonrpc.messages.{Either => JEither}
import org.eclipse.lsp4j.{Position => LspPosition}
import org.eclipse.lsp4j.{Range => LspRange}
import org.eclipse.lsp4j.{debug => d}

/**
 * Manages lifecycle for presentation compilers in all build targets.
 *
 * We need a custom presentation compiler for each build target since
 * build targets can have different classpaths and compiler settings.
 */
class Compilers(
    workspace: AbsolutePath,
    config: ClientConfiguration,
    userConfig: () => UserConfiguration,
    buildTargets: BuildTargets,
    buffers: Buffers,
    search: SymbolSearch,
    embedded: Embedded,
    workDoneProgress: WorkDoneProgress,
    sh: ScheduledExecutorService,
    initializeParams: InitializeParams,
    excludedPackages: () => ExcludedPackagesHandler,
    scalaVersionSelector: ScalaVersionSelector,
    trees: Trees,
    mtagsResolver: MtagsResolver,
    sourceMapper: SourceMapper,
    worksheetProvider: WorksheetProvider,
    completionItemPriority: () => CompletionItemPriority,
)(implicit ec: ExecutionContextExecutorService, rc: ReportContext)
    extends Cancelable {

  val compilerConfiguration = new CompilerConfiguration(
    workspace,
    config,
    userConfig,
    buildTargets,
    buffers,
    embedded,
    sh,
    initializeParams,
    excludedPackages,
    trees,
    mtagsResolver,
    sourceMapper,
  )

  // HashMap

  import compilerConfiguration._

  private val outlineFilesProvider =
    new OutlineFilesProvider(buildTargets, buffers)

  // Not a TrieMap because we want to avoid loading duplicate compilers for the same build target.
  // Not a `j.u.c.ConcurrentHashMap` because it can deadlock in `computeIfAbsent` when the absent
  // function is expensive, which is the case here.
  val jcache: ju.Map[PresentationCompilerKey, MtagsPresentationCompiler] =
    Collections.synchronizedMap(
      new java.util.HashMap[PresentationCompilerKey, MtagsPresentationCompiler]
    )
  private val jworksheetsCache
      : ju.Map[AbsolutePath, MtagsPresentationCompiler] =
    Collections.synchronizedMap(
      new java.util.HashMap[AbsolutePath, MtagsPresentationCompiler]
    )

  private val worksheetsDigests = new TrieMap[AbsolutePath, String]()

  private val cache = jcache.asScala
  private def buildTargetPCFromCache(
      id: BuildTargetIdentifier
  ): Option[PresentationCompiler] =
    cache.get(PresentationCompilerKey.ScalaBuildTarget(id)).collect {
      case lazyPc if lazyPc != null => lazyPc.await
    }

  private val worksheetsCache = jworksheetsCache.asScala

  // The "fallback" compiler is used for source files that don't belong to a build target.
  private def fallbackCompiler: PresentationCompiler = {
    jcache
      .compute(
        PresentationCompilerKey.Default,
        (_, value) => {
          val scalaVersion =
            scalaVersionSelector.fallbackScalaVersion(isAmmonite = false)

          Option(value) match {
            case Some(lazyPc) =>
              val presentationCompiler = lazyPc.await
              if (presentationCompiler.scalaVersion() == scalaVersion) {
                lazyPc
              } else {
                presentationCompiler.shutdown()
                StandaloneCompiler(
                  scalaVersion,
                  search,
                  Nil,
                  completionItemPriority(),
                )
              }
            case None =>
              StandaloneCompiler(
                scalaVersion,
                search,
                Nil,
                completionItemPriority(),
              )
          }
        },
      )
      .await
  }

  def loadedPresentationCompilerCount(): Int =
    cache.values.count(_.await.isLoaded())

  override def cancel(): Unit = {
    Cancelable.cancelEach(cache.values)(_.shutdown())
    Cancelable.cancelEach(worksheetsCache.values)(_.shutdown())
    cache.clear()
    worksheetsCache.clear()
    worksheetsDigests.clear()
    outlineFilesProvider.clear()
  }

  def restartAll(): Unit = {
    val count = cache.size
    cancel()
    scribe.info(
      s"restarted ${count} presentation compiler${LogMessages.plural(count)}"
    )
  }

  def load(paths: Seq[AbsolutePath]): Future[Unit] =
    if (Testing.isEnabled) Future.successful(())
    else {
      Future {
        val targets = paths
          .filter(_.isScalaFilename)
          .flatMap(path => buildTargets.inverseSources(path).toList)
          .distinct
        targets.foreach { target =>
          loadCompiler(target).foreach { pc =>
            pc
              .hover(
                CompilerOffsetParams(
                  Paths.get("Main.scala").toUri(),
                  "object Ma\n",
                  "object Ma".length(),
                )
              )
              .thenApply(_.map(_.toLsp()))
          }
        }
      }
    }

  def didClose(path: AbsolutePath): Unit = {
    loadCompiler(path).foreach(_.didClose(path.toNIO.toUri()))
  }

  def didChange(path: AbsolutePath): Future[List[Diagnostic]] = {
    def originInput =
      path
        .toInputFromBuffers(buffers)

    loadCompiler(path)
      .map { pc =>
        val inputAndAdjust =
          if (
            path.isWorksheet && ScalaVersions.isScala3Version(
              pc.scalaVersion()
            )
          ) {
            WorksheetProvider.worksheetScala3AdjustmentsForPC(originInput)
          } else {
            None
          }

        val (input, adjust) = inputAndAdjust.getOrElse(
          originInput,
          AdjustedLspData.default,
        )

        outlineFilesProvider.didChange(pc.buildTargetId(), path)

        for {
          ds <-
            pc
              .didChange(
                CompilerVirtualFileParams(path.toNIO.toUri(), input.value)
              )
              .asScala
        } yield {
          ds.asScala.map(adjust.adjustDiagnostic).toList

        }
      }
      .getOrElse(Future.successful(Nil))
  }

  def didCompile(report: CompileReport): Unit = {
    val isSuccessful = report.getErrors == 0
    val isBestEffortCompilation =
      buildTargets
        .scalaTarget(report.getTarget)
        .map(_.isBestEffort)
        .getOrElse(false)
    buildTargetPCFromCache(report.getTarget).foreach { pc =>
      if (
        outlineFilesProvider.shouldRestartPc(
          report.getTarget,
          DidCompile(isSuccessful),
        )
      ) {
        pc.restart()
      }
    }

    outlineFilesProvider.onDidCompile(report.getTarget(), isSuccessful)

    if (isSuccessful || isBestEffortCompilation) {
      // Restart PC for all build targets that depend on this target since the classfiles
      // may have changed.
      for {
        target <- buildTargets.allInverseDependencies(report.getTarget)
        if target != report.getTarget
        if outlineFilesProvider.shouldRestartPc(target, InverseDependency)
        compiler <- buildTargetPCFromCache(target)
      } {
        compiler.restart()
      }
    }
  }

  def completionItemResolve(
      item: CompletionItem
  ): Future[CompletionItem] = {
    for {
      data <- item.data
      compiler <- buildTargetPCFromCache(new BuildTargetIdentifier(data.target))
    } yield compiler.completionItemResolve(item, data.symbol).asScala
  }.getOrElse(Future.successful(item))

  /**
   * Calculates completions for a expression evaluator at breakpointPosition
   *
   * @param path path to file containing ht ebreakpoint
   * @param breakpointPosition actual breakpoint position
   * @param token cancel token for the compiler
   * @param expression expression that is currently being types
   * @param isZeroBased whether the client supports starting at 0 or 1 index
   * @return
   */
  def debugCompletions(
      path: AbsolutePath,
      breakpointPosition: LspPosition,
      token: CancelToken,
      expression: d.CompletionsArguments,
      isZeroBased: Boolean,
  ): Future[Seq[d.CompletionItem]] = {

    /**
     * Find the offset of the cursor inside the modified expression.
     * We need it to give the compiler the right offset.
     *
     * @param modified modified expression with indentation inserted
     * @param indentation indentation of the current breakpoint
     * @return offset where the compiler should insert completions
     */
    def expressionOffset(modified: String, indentation: String) = {
      val line = expression.getLine()
      val column = expression.getColumn()
      modified.split("\n").zipWithIndex.take(line).foldLeft(0) {
        case (offset, (lineText, index)) =>
          if (index + 1 == line) {
            if (line > 1)
              offset + column + indentation.size - 1
            else
              offset + column - 1
          } else offset + lineText.size + 1
      }
    }
    loadCompiler(path)
      .map { compiler =>
        val input = path.toInputFromBuffers(buffers)
        breakpointPosition.toMeta(input) match {
          case Some(metaPos) =>
            val oldText = metaPos.input.text
            val lineStart = oldText.indexWhere(
              c => c != ' ' && c != '\t',
              metaPos.start + 1,
            )

            val indentationSize = lineStart - metaPos.start
            val indentationChar =
              if (oldText.lift(lineStart - 1).exists(_ == '\t')) '\t' else ' '
            val indentation = indentationChar.toString * indentationSize

            val expressionText =
              expression.getText().replace("\n", s"\n$indentation")

            val prev = oldText.substring(0, lineStart)
            val succ = oldText.substring(lineStart)
            // insert expression at the start of breakpoint's line and move the lines one down
            val modified = s"$prev;$expressionText\n$indentation$succ"

            val rangeEnd =
              lineStart + expressionOffset(expressionText, indentation) + 1

            /**
             * Calculate the start if insertText is used for item, which does not declare an exact start.
             */
            def insertStart = {
              var i = rangeEnd - 1
              while (modified.charAt(i).isLetterOrDigit) i -= 1
              if (isZeroBased) i else i + 1
            }

            val offsetParams =
              CompilerOffsetParams(
                path.toURI,
                modified,
                rangeEnd,
                token,
                outlineFilesProvider.getOutlineFiles(compiler.buildTargetId()),
              )

            val previousLines = expression
              .getText()
              .split("\n")

            // we need to adjust start to point at the start of the replacement in the expression
            val adjustStart =
              /* For multiple line we need to insert at the correct offset and
               * then adjust column by indentation that was added to the expression
               */
              if (previousLines.size > 1)
                previousLines
                  .take(expression.getLine() - 1)
                  .map(_.size + 1)
                  .sum - indentationSize
              // for one line we only need to adjust column with indentation + ; that was added to the expression
              else -(1 + indentationSize)

            compiler
              .complete(offsetParams)
              .asScala
              .map(list =>
                list.getItems.asScala.toSeq
                  .map(
                    toDebugCompletionItem(
                      _,
                      adjustStart,
                      Position.Range(
                        input.copy(value = modified),
                        insertStart,
                        rangeEnd,
                      ),
                    )
                  )
              )
          case None =>
            scribe.debug(s"$breakpointPosition was not found in $path ")
            Future.successful(Nil)
        }
      }
      .getOrElse(Future.successful(Nil))
  }

  def semanticTokens(
      params: SemanticTokensParams,
      token: CancelToken,
  ): Future[SemanticTokens] = {
    val emptyTokens = Collections.emptyList[Integer]();
    if (!userConfig().enableSemanticHighlighting) {
      Future { new SemanticTokens(emptyTokens) }
    } else {
      val path = params.getTextDocument.getUri.toAbsolutePath
      loadCompiler(path)
        .map { compiler =>
          val (input, _, adjust) =
            sourceAdjustments(
              params.getTextDocument().getUri(),
              compiler.scalaVersion(),
            )

          /**
           * Find the start that is actually contained in the file and not
           * in the added parts such as imports in sbt.
           *
           * @param line line within the adjusted source
           * @param character line within the adjusted source
           * @param remaining the rest of the tokens to analyze
           * @return the first found that should be contained with the rest
           */
          @tailrec
          def findCorrectStart(
              line: Integer,
              character: Integer,
              remaining: List[Integer],
          ): List[Integer] = {
            remaining match {
              case lineDelta :: charDelta :: next =>
                val newCharacter: Integer =
                  // only increase character delta if the same line
                  if (lineDelta == 0) character + charDelta
                  else charDelta

                val adjustedTokenPos = adjust.adjustPos(
                  new LspPosition(line + lineDelta, newCharacter),
                  adjustToZero = false,
                )
                if (
                  adjustedTokenPos.getLine() >= 0 &&
                  adjustedTokenPos.getCharacter() >= 0
                )
                  (adjustedTokenPos.getLine(): Integer) ::
                    (adjustedTokenPos.getCharacter(): Integer) :: next
                else
                  findCorrectStart(
                    line + lineDelta,
                    newCharacter,
                    next.drop(3),
                  )
              case _ => Nil
            }
          }

          def adjustForScala3Worksheet(tokens: List[Integer]): List[Integer] = {
            @tailrec
            @nowarn
            def loop(
                remaining: List[Integer],
                acc: List[List[Integer]],
                adjustColumnDelta: Int =
                  0, // after multiline string we need to adjust column delta of the next token in line
            ): List[Integer] = {
              remaining match {
                case Nil => acc.reverse.flatten
                // we need to remove additional indent
                case deltaLine :: deltaColumn :: len :: next
                    if deltaLine != 0 =>
                  if (deltaColumn - 2 >= 0) {
                    val adjustedColumn: Integer = deltaColumn - 2
                    val adjusted: List[Integer] =
                      List(deltaLine, adjustedColumn, len) ++ next.take(2)
                    loop(
                      next.drop(2),
                      adjusted :: acc,
                    )
                  }
                  // for multiline strings, we highlight the entire line inluding leading whitespace
                  // so we need to adjust the length after removing additional indent
                  else {
                    val deltaLen = deltaColumn - 2
                    val adjustedLen: Integer = Math.max(0, len + deltaLen)
                    val adjusted: List[Integer] =
                      List(deltaLine, deltaColumn, adjustedLen) ++ next.take(2)
                    loop(
                      next.drop(2),
                      adjusted :: acc,
                      deltaLen,
                    )
                  }
                case deltaLine :: deltaColumn :: next =>
                  val adjustedColumn: Integer = deltaColumn + adjustColumnDelta
                  val adjusted: List[Integer] =
                    List(deltaLine, adjustedColumn) ++ next.take(3)
                  loop(
                    next.drop(3),
                    adjusted :: acc,
                  )
              }
            }

            // Delta for first token was already adjusted in `findCorrectStart`
            loop(tokens.drop(5), List(tokens.take(5)))
          }

          val vFile =
            CompilerVirtualFileParams(
              path.toNIO.toUri(),
              input.text,
              token,
              outlineFilesProvider.getOutlineFiles(compiler.buildTargetId()),
            )
          val isScala3 = ScalaVersions.isScala3Version(compiler.scalaVersion())

          compiler
            .semanticTokens(vFile)
            .asScala
            .map { nodes =>
              val plist =
                try {
                  SemanticTokensProvider.provide(
                    nodes.asScala.toList,
                    vFile,
                    path,
                    isScala3,
                    trees,
                  )
                } catch {
                  case NonFatal(e) =>
                    scribe.error(
                      s"Failed to tokenize input for semantic tokens for $path",
                      e,
                    )
                    Nil
                }

              val tokens =
                findCorrectStart(0, 0, plist.toList)
              if (isScala3 && path.isWorksheet) {
                new SemanticTokens(adjustForScala3Worksheet(tokens).asJava)
              } else {
                new SemanticTokens(tokens.asJava)
              }
            }
        }
        .getOrElse(Future.successful(new SemanticTokens(emptyTokens)))
    }

  }

  def inlayHints(
      params: InlayHintParams,
      token: CancelToken,
  ): Future[ju.List[InlayHint]] = {
    withPCAndAdjustLsp(params) { (pc, pos, adjust) =>
      def inlayHintsFallback(
          params: SyntheticDecorationsParams
      ): Future[ju.List[InlayHint]] = {
        pc.syntheticDecorations(params)
          .asScala
          .map(
            _.map { d =>
              val hint = new InlayHint()
              hint.setPosition(d.range().getStart())
              hint.setLabel(d.label())
              val kind =
                if (d.kind() <= 2) InlayHintKind.Type
                else InlayHintKind.Parameter
              hint.setKind(kind)
              hint.setData(
                internal.pc.InlayHints
                  .toData(params.uri().toString(), List(Left("")))
              )
              hint
            }
          )
      }

      def adjustInlayHints(
          inlayHints: ju.List[InlayHint]
      ): ju.List[InlayHint] = {
        inlayHints.asScala
          .dropWhile { hint =>
            val adjusted =
              adjust.adjustPos(hint.getPosition(), adjustToZero = false)
            adjusted.getLine() < 0 || adjusted.getCharacter() < 0
          }
          .map { hint =>
            hint.setPosition(adjust.adjustPos(hint.getPosition()))
            InlayHintCompat.maybeFixInlayHintData(
              hint,
              params.getTextDocument().getUri(),
            )
          }
          .asJava
      }

      val rangeParams =
        CompilerRangeParamsUtils.fromPos(
          pos,
          token,
          outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
        )
      val options = userConfig().inlayHintsOptions
      val pcParams = CompilerInlayHintsParams(
        rangeParams,
        inferredTypes = options.inferredType,
        implicitParameters = options.implicitArguments,
        implicitConversions = options.implicitConversions,
        typeParameters = options.typeParameters,
        hintsInPatternMatch = options.hintsInPatternMatch,
      )

      pc
        .inlayHints(pcParams)
        .asScala
        .flatMap { hints =>
          if (hints.isEmpty) {
            inlayHintsFallback(pcParams.toSyntheticDecorationsParams)
              .map(adjustInlayHints)
          } else {
            Future.successful(adjustInlayHints(hints))
          }
        }
    }
      .getOrElse(Future.successful(Nil.asJava))
  }

  def completions(
      params: CompletionParams,
      token: CancelToken,
  ): Future[CompletionList] =
    withPCAndAdjustLsp(params) { (pc, pos, adjust) =>
      val outlineFiles =
        outlineFilesProvider.getOutlineFiles(pc.buildTargetId())
      val offsetParams =
        CompilerOffsetParamsUtils.fromPos(pos, token, outlineFiles)
      // pos -- is cursor pos
      scribe.info(s"about to pc.complete") // взывает к scala pres compiler

      pc.complete(offsetParams)
        .asScala
        .map { list =>
          scribe.info("[completions] insdie complete")
          doScalafixMagic(offsetParams, list) // todo: \forall plan
          adjust.adjustCompletionListInPlace(list)
          scribe.info(s"[completions] after adjustCompletionListInPlace")
          list
        }
    }.getOrElse(Future.successful(new CompletionList(Nil.asJava)))

  // todo: разделить случаи, когда подбирается импорт, а когда поиск метода
  def doScalafixMagic(
      offsetParams: OffsetParams,
      completionList: CompletionList,
  ): Option[Unit] = {
    scribe.info(s"Start examine completionList")
    // todo: посмотреть как годзик сделал сортировку импорта

    val suggestedImports =
      completionList.getItems.asScala.view
        .filter(
          _.getAdditionalTextEdits() ne null
        ) // должны быть только импорты. так как вставка импорта заменяет текущую строку, а через additional меняет импорт
        .map(_.getAdditionalTextEdits())
        .filterNot(_.isEmpty())

    scribe.info(s"Start examine completionList.additionalTextEdits")
    // scribe.info(s"suggestedImports: ${ suggestedImports.mkString("\n") }")

    scribe.info("Start collect imports")
    // val Some((globalImports, localImports)) =
    trees
      .get(offsetParams.uri.toAbsolutePath)
      .map(collectImports)
      .map {
        case (
              globalImports,
              localImports, // crap, нет необходимости
            ) =>
          scribe.info(s"End collect global imports")
          scribe.info(s"End collect local imports")

          // todo: попробовать утащить в ~/Developer
          /*
                1. логическкие два шага по реализации
                2. Найти Trees в CP,
           */

          scribe.info("Start organizeImports")

          val groups =
            suggestedImports.map { suggested =>
              val asImport = suggested.asScala
                .map(_.getNewText())
                .map { stringToImport(_) }
                .toSeq
                .head // todo: сомнительно
              // todo: попробовать pPrint

              val res = asImport -> organizeImports(asImport +: globalImports)
              // scribe.info(s"here is what organized: suggested: ${asImport}, rest: ${res}")
              res
            }.toList

          val token = globalImports.head.tokens.head

          val reevaluetedCompletions = groups.map { case suggested -> all =>
            suggested -> insertOrganizedImports(token, all)
          }

          val mappings =
            completionList
              .getItems()
              .asScala
              .toList
              .map(ci =>
                s"${ci.getDetail().trim()}.${ci.getFilterText()}" -> ci
              )
              .toMap

          reevaluetedCompletions.foldLeft(mappings) {
            case (map, imports -> repr) =>
              val maybeKey =
                imports.toString.replace("`", "").replace("import ", "").trim()
              scribe.info(s"Here is maybeKey: |${maybeKey}|")
              map.get(maybeKey).fold(scribe.info("key not found")) {
                textEditToFix =>
                  // scribe.info(s"textEditToFix before fix: ${textEditToFix}")
                  textEditToFix
                    .setAdditionalTextEdits(
                      List(
                        new TextEdit(
                          new LspRange(
                            // token.pos,
                            new LspPosition(
                              token.pos.startLine,
                              token.pos.startColumn,
                            ), {
                              val lastImportToken =
                                globalImports.last.tokens.last.pos
                              new LspPosition(
                                lastImportToken.startLine,
                                lastImportToken.endColumn,
                              )
                            },
                          ),
                          repr,
                        )
                      ).asJava
                    )
                  // scribe.info(s"textEditToFix after fix: ${textEditToFix}")
              }
              map
          }
          scribe.info("End organizeImports")
      }
  }

  def stringToImport(rawImport: String): Import = {
    import scala.meta._
    scribe.info(s"rawImport: |${rawImport}|")
    val rawSplitted = rawImport.replace("import", "").trim().split('.').toList
    scribe.info(s"rawImport after split: |${rawSplitted.map(el => s"|$el|")}|")
    val importPart = rawSplitted.dropRight(1)
    scribe.info(s"rawSplitted: ${rawSplitted}")

    val importees = rawSplitted.takeRight(1).map(rn => Importee.Name(Name(rn)))
    scribe.info(s"importees: ${importees}")

    val importTerm = importPart match {
      case h :: t =>
        t.foldLeft(Term.Name(h): Term.Ref) { case (acc, rhs) =>
          Term.Select(acc, Term.Name(rhs))
        }
      case _ => ???
    }
    scribe.info(s"importTerm: ${importTerm}")
    Import(List(Importer(importTerm, importees)))
  }

  private def insertOrganizedImports(
      token: Token,
      importGroups: Seq[ImportGroup],
  ): String = {
    val prettyPrintedGroups = importGroups.map {
      case ImportGroup(index, imports) =>
        index -> prettyPrintImportGroup(imports)
    }

    val blankLines = {
      // Indices of all blank lines configured in `OrganizeImports.groups`, either automatically or
      // manually.
      val blankLineIndices = matchers.zipWithIndex.collect {
        case (ImportMatcher.`---`, index) => index
      }.toSet

      // Checks each pair of adjacent import groups. Inserts a blank line between them if necessary.
      importGroups map (_.index) sliding 2 filter (_.length == 2) flatMap {
        case Seq(lhs, rhs) =>
          val hasBlankLine = blankLineIndices exists (i => lhs < i && i < rhs)
          if (hasBlankLine) Some((lhs + 1) -> "") else None
      }
    }

    val withBlankLines = (prettyPrintedGroups ++ blankLines)
      .sortBy { case (index, _) => index }
      .map { case (_, lines) => lines }
      .mkString("\n")

    // Global imports within curly-braced packages must be indented accordingly, e.g.:
    //
    //   package foo {
    //     package bar {
    //       import baz
    //       import qux
    //     }
    //   }
    val indented = withBlankLines.linesIterator.zipWithIndex.map {
      // The first line will be inserted at an already indented position.
      case (line, 0) => line
      case (line, _) if line.isEmpty => line
      case (line, _) => " " * token.pos.startColumn + line
    }

    indented mkString "\n"
  }

  private def prettyPrintImportGroup(group: Seq[Importer]): String =
    group
      .map(i => "import " + importerSyntax(i))
      .mkString("\n")

  @tailrec private def collectImports(
      tree: Tree
  ): (Seq[Import], Seq[Import]) = {
    def extractImports(stats: Seq[Stat]): (Seq[Import], Seq[Import]) = {
      val (importStats, otherStats) = stats.span(_.is[Import])
      val globalImports = importStats.map { case i: Import => i }
      val localImports = otherStats.flatMap(_.collect { case i: Import => i })
      (globalImports, localImports)
    }

    tree match {
      case Source(Seq(p: Pkg)) => collectImports(p)
      case Pkg(_, Seq(p: Pkg)) => collectImports(p)
      case Source(stats) => extractImports(stats)
      case Pkg(_, stats) => extractImports(stats)
      case _ => (Nil, Nil)
    }
  }

  private def organizeImports(imports: Seq[Import]) = {
    // val noUnused = imports.map(_.importers) решили не убирать неиспользуемое.
    // .flatMap()
    // todo: читать конфиг скалафикса.

    // буду считать, что есть только полностью определенные импорты.
    val fullyQualifiedImporters =
      imports.flatMap(_.importers) // .partition(isFullyQualified(_))
    scribe.info(s"receive fullyQualifiedImporters: ${fullyQualifiedImporters}")

    val grouped = groupImporters(fullyQualifiedImporters)
    // scribe.info(s"receive groupImporters: ${grouped}")
    grouped
  }

  val fxConfig: Configs.OrganizeImportsConfig =
    Configs.OrganizeImportsConfig.default
      .copy(
        groups = Seq(
          "re:javax?\\.",
          "scala.",
          "scala.meta.",
          "*",
        )
      ) // todo: Подгружать автоматом
  private val matchers = buildImportMatchers(fxConfig)
  private val wildcardGroupIndex: Int = matchers indexOf ImportMatcher.*

  private def buildImportMatchers(
      config: Configs.OrganizeImportsConfig
  ): Seq[ImportMatcher] = {
    import ImportMatcher._
    val withWildcard = {
      val parsed = config.groups map parse
      // The wildcard group should always exist. Appends one at the end if omitted.
      if (parsed contains *) parsed else parsed :+ *
    }

    // Inserts a blank line marker between adjacent import groups when `blankLines` is `Auto`.
    config.blankLines match {
      case BlankLines.Manual => withWildcard
      case BlankLines.Auto => withWildcard.flatMap(_ :: --- :: Nil)
    }
  }

  private def groupImporters(
      importers: Seq[Importer]
  ) = {
    val intermidiate = importers
      .groupBy(matchImportGroup)
      .mapValues(deduplicateImportees)
      .mapValues(organizeImportGroup)
      .map { case (index, imports) =>
        ImportGroup(index, imports)
      }
      .toSeq
      .sortBy(_.index)

    intermidiate
  }

  private def matchImportGroup(importer: Importer): Int = {
    val matchedGroups = matchers
      .map(_ matches importer)
      .zipWithIndex
      .filter { case (length, _) => length > 0 }
    if (matchedGroups.isEmpty) wildcardGroupIndex
    else {
      val (_, index) = matchedGroups.maxBy { case (length, _) => length }
      index
    }
  }

  import ImporterXtenstion._
  private def deduplicateImportees(importers: Seq[Importer]): Seq[Importer] = {
    import scala.collection.mutable
    // Scalameta `Tree` nodes do not provide structural equality comparisons, here we pretty-print
    // them and compare the string results.
    val seenImportees = mutable.Set.empty[(String, String)]

    importers.flatMap { importer =>
      importer.filterImportees { importee =>
        importee.is[Importee.Wildcard] || importee.is[Importee.GivenAll] ||
        seenImportees.add(importee.syntax -> importer.ref.syntax)
      }
    }
  }

  private def organizeImportGroup(importers: Seq[Importer]): Seq[Importer] = {
    val importeesSorted =
      locally {
        fxConfig.groupedImports match {
          // case GroupedImports.Merge =>
          //   mergeImporters(diagnostics)(importers, aggressive = false)
          // case GroupedImports.AggressiveMerge =>
          //   mergeImporters(diagnostics)(importers, aggressive = true)
          // case GroupedImports.Explode =>
          //   explodeImportees(importers)
          // case GroupedImports.Keep =>
          //   importers
          case _ => importers
        }
      }.view
        .map(coalesceImportees)
        .map(sortImportees)
        .toSeq

    locally {
      fxConfig.importsOrder match {
        case ImportsOrder.Ascii =>
          importeesSorted.sortBy(i => importerSyntax(i.copy()))
        case ImportsOrder.SymbolsFirst =>
          sortImportersSymbolsFirst(importeesSorted)
        case ImportsOrder.Keep => importeesSorted
      }
    }
  }

  private def coalesceImportees(importer: Importer): Importer = {
    val Importees(names, renames, unimports, givens, _, _) = importer.importees

    fxConfig.coalesceToWildcardImportThreshold
      .filter(importer.importees.length > _)
      // Skips if there's no `Name`s or `Given`s. `Rename`s and `Unimport`s cannot be coalesced.
      .filterNot(_ => names.isEmpty && givens.isEmpty)
      .map {
        case _ if givens.isEmpty => renames ++ unimports :+ Importee.Wildcard()
        case _ if names.isEmpty => renames ++ unimports :+ Importee.GivenAll()
        case _ =>
          renames ++ unimports :+ Importee.GivenAll() :+ Importee.Wildcard()
      }
      .map(importees => importer.copy(importees = importees))
      .getOrElse(importer)
  }

  private def sortImportees(importer: Importer): Importer = {
    import ImportSelectorsOrder._

    // The Scala language spec allows an import expression to have at most one final wildcard, which
    // can only appears in the last position.
    val (wildcards, others) =
      importer.importees partition (i =>
        i.is[Importee.Wildcard] || i.is[Importee.GivenAll]
      )

    val orderedImportees = fxConfig.importSelectorsOrder match {
      case Ascii =>
        Seq(others, wildcards) map (_.sortBy(_.syntax)) reduce (_ ++ _)
      case SymbolsFirst =>
        Seq(others, wildcards) map sortImporteesSymbolsFirst reduce (_ ++ _)
      case Keep =>
        importer.importees
    }

    // Checks whether importees of the input importer are already sorted. If yes, we should return
    // the original importer to preserve the original source level formatting.
    val alreadySorted =
      fxConfig.importSelectorsOrder == Keep ||
        (importer.importees corresponds orderedImportees) { (lhs, rhs) =>
          lhs.syntax == rhs.syntax
        }

    if (alreadySorted) importer else importer.copy(importees = orderedImportees)
  }

  private def sortImporteesSymbolsFirst(
      importees: List[Importee]
  ): List[Importee] = {
    val symbols = ArrayBuffer.empty[Importee]
    val lowerCases = ArrayBuffer.empty[Importee]
    val upperCases = ArrayBuffer.empty[Importee]

    importees.foreach {
      case i if i.syntax.head.isLower => lowerCases += i
      case i if i.syntax.head.isUpper => upperCases += i
      case i => symbols += i
    }

    List(symbols, lowerCases, upperCases) flatMap (_ sortBy (_.syntax))
  }

  private def importerSyntax(importer: Importer): String =
    importer.pos match {
      case pos: Position.Range =>
        // Position found, implies that `importer` was directly parsed from the source code. Rewrite
        // importees to ensure they follow the target dialect. For importers with a single importee,
        // strip enclosing braces if they exist (or add/preserve them for Rename & Unimport on Scala 2).

        val syntax = new StringBuilder(pos.text)

        def patchSyntax(
            t: Tree,
            newSyntax: String,
        ) = {
          val start = t.pos.start - pos.start
          syntax.replace(start, t.pos.end - pos.start, newSyntax)

          if (importer.importees.length == 1) {
            val end = t.pos.start - pos.start + newSyntax.length
            (
              syntax.take(start).lastIndexOf('{'),
              syntax.indexOf('}', end),
              importer.isCurlyBraced,
            ) match {
              case (-1, -1, true) =>
                // braces required but not detected
                syntax.append('}')
                syntax.insert(start, '{')
              case (opening, closing, false)
                  if opening != -1 && closing != -1 =>
                // braces detected but not required
                syntax.delete(end, closing + 1)
                syntax.delete(opening, start)
              case _ =>
            }
          }
        }

        // traverse & patch backwards to avoid shifting indices
        importer.importees.reverse.foreach {
          case i @ Importee.Rename(_, _) =>
            patchSyntax(i, i.copy().syntax)
          case i @ Importee.Unimport(_) =>
            patchSyntax(i, i.copy().syntax)
          case i @ Importee.Wildcard() =>
            patchSyntax(i, i.copy().syntax)
          case i =>
            patchSyntax(i, i.syntax)
        }

        syntax.toString

      case Position.None =>
        // Position not found, implies that `importer` is derived from certain existing import
        // statement(s). Pretty-prints it.
        val syntax = importer.syntax

        // HACK: The Scalafix pretty-printer decides to add spaces after open and
        // before close braces in imports with multiple importees, i.e., `import a.{
        // b, c }` instead of `import a.{b, c}`. On the other hand, renames are
        // pretty-printed without the extra spaces, e.g., `import a.{b => c}`. This
        // behavior is not customizable and makes ordering imports by ASCII order
        // complicated.
        //
        // This function removes the unwanted spaces as a workaround. In cases where
        // users do want the inserted spaces, Scalafmt should be used after running
        // the `OrganizeImports` rule.

        // NOTE: We need to check whether the input importer is curly braced first and then replace
        // the first "{ " and the last " }" if any. Naive string replacement is insufficient, e.g.,
        // a quoted-identifier like "`{ d }`" may cause broken output.
        (importer.isCurlyBraced, syntax lastIndexOfSlice " }") match {
          case (_, -1) =>
            syntax
          case (true, index) =>
            syntax.patch(index, "}", 2).replaceFirst("\\{ ", "{")
          case _ =>
            syntax
        }
    }

  private def sortImportersSymbolsFirst(
      importers: Seq[Importer]
  ): Seq[Importer] =
    importers.sortBy { importer =>
      // See the comment marked with "issues/84" for why a `.copy()` is needed.
      val syntax = importer.copy().syntax

      importer match {
        case Importer(_, Importee.Wildcard() :: Nil) =>
          val wildcardSyntax = Importee.Wildcard().syntax
          syntax.patch(
            syntax.lastIndexOfSlice(s".$wildcardSyntax"),
            ".\u0001",
            2,
          )

        case _ if importer.isCurlyBraced =>
          syntax
            .replaceFirst("[{]", "\u0002")
            .patch(syntax.lastIndexOf("}"), "\u0002", 1)

        case _ => syntax
      }
    }
  /////////////////////////// classes
  private case class ImportGroup(index: Int, imports: Seq[Importer])

  object ImporterXtenstion {
    implicit class ImporterExtension(importer: Importer) {
      def isCurlyBraced: Boolean = {
        val importees @ Importees(_, renames, unimports, _, _, _) =
          importer.importees

        importees.length > 1 ||
        ((
          renames.length == 1 ||
            unimports.length == 1
        ) // &&
        // !targetDialect.allowAsForImportRename
        )
      }

      /**
       * Returns an `Importer` with all the `Importee`s that are selected from the
       * input `Importer` and satisfy a predicate. If all the `Importee`s are
       * selected, the input `Importer` instance is returned to preserve the
       * original source level formatting. If none of the `Importee`s are
       * selected, returns a `None`.
       */
      def filterImportees(f: Importee => Boolean): Option[Importer] = {
        val filtered = importer.importees filter f
        if (filtered.length == importer.importees.length) Some(importer)
        else if (filtered.isEmpty) None
        else Some(importer.copy(importees = filtered))
      }
    }
  }

  /**
   * Categorizes a list of `Importee`s into the following four groups:
   *
   *   - Names, e.g., `Seq`, `Option`, etc.
   *   - Renames, e.g., `{Long => JLong}`, `Duration as D`, etc.
   *   - Unimports, e.g., `{Foo => _}` or `Foo as _`.
   *   - Givens, e.g., `given Foo`.
   *   - GivenAll, i.e., `given`.
   *   - Wildcard, i.e., `_` or `*`.
   */
  object Importees {
    def unapply(importees: Seq[Importee]): Option[
      (
          List[Importee.Name],
          List[Importee.Rename],
          List[Importee.Unimport],
          List[Importee.Given],
          Option[Importee.GivenAll],
          Option[Importee.Wildcard],
      )
    ] = {
      val names = ArrayBuffer.empty[Importee.Name]
      val renames = ArrayBuffer.empty[Importee.Rename]
      val givens = ArrayBuffer.empty[Importee.Given]
      val unimports = ArrayBuffer.empty[Importee.Unimport]
      var maybeWildcard: Option[Importee.Wildcard] = None
      var maybeGivenAll: Option[Importee.GivenAll] = None

      importees foreach {
        case i: Importee.Wildcard => maybeWildcard = Some(i)
        case i: Importee.Unimport => unimports += i
        case i: Importee.Rename => renames += i
        case i: Importee.Name => names += i
        case i: Importee.Given => givens += i
        case i: Importee.GivenAll => maybeGivenAll = Some(i)
      }

      Option(
        (
          names.toList,
          renames.toList,
          unimports.toList,
          givens.toList,
          maybeGivenAll,
          maybeWildcard,
        )
      )
    }
  }

///////////////////////////////////////////////

  def autoImports(
      params: TextDocumentPositionParams,
      name: String,
      findExtensionMethods: Boolean,
      token: CancelToken,
  ): Future[ju.List[AutoImportsResult]] = {
    scribe.info("gonna autoImports")
    withPCAndAdjustLsp(params) { (pc, pos, adjust) =>
      pc.autoImports(
        name,
        CompilerOffsetParamsUtils.fromPos(
          pos,
          token,
          outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
        ),
        findExtensionMethods,
      ).asScala
        .map { list =>
          list.map(adjust.adjustImportResult)
          list
        }
    }
  }.getOrElse(Future.successful(Nil.asJava))

  def insertInferredType(
      params: TextDocumentPositionParams,
      token: CancelToken,
  ): Future[ju.List[TextEdit]] = {
    withPCAndAdjustLsp(params) { (pc, pos, adjust) =>
      val offset =
        CompilerOffsetParamsUtils.fromPos(
          pos,
          token,
          outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
        )
      val result =
        if (
          pc.supportedCodeActions()
            .contains(CodeActionId.InsertInferredType)
        )
          pc.codeAction(
            offset,
            CodeActionId.InsertInferredType,
            ju.Optional.empty(),
          )
        else
          pc.insertInferredType(offset)

      result.asScala
        .map { edits =>
          adjust.adjustTextEdits(edits)
        }
    }
  }.getOrElse(Future.successful(Nil.asJava))

  def inlineEdits(
      params: TextDocumentPositionParams,
      token: CancelToken,
  ): Future[ju.List[TextEdit]] =
    withPCAndAdjustLsp(params) { (pc, pos, adjust) =>
      val offsetParams = CompilerOffsetParamsUtils.fromPos(
        pos,
        token,
        outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
      )
      val result =
        if (
          pc.supportedCodeActions()
            .contains(CodeActionId.InlineValue)
        )
          pc.codeAction(
            offsetParams,
            CodeActionId.InlineValue,
            ju.Optional.empty(),
          )
        else
          pc.inlineValue(offsetParams)

      result.asScala
        .map { edits =>
          adjust.adjustTextEdits(edits)
        }
    }.getOrElse(Future.successful(Nil.asJava))

  def documentHighlight(
      params: TextDocumentPositionParams,
      token: CancelToken,
  ): Future[ju.List[DocumentHighlight]] = {
    withPCAndAdjustLsp(params) { (pc, pos, adjust) =>
      pc.documentHighlight(
        CompilerOffsetParamsUtils.fromPos(
          pos,
          token,
          outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
        )
      ).asScala
        .map { highlights =>
          adjust.adjustDocumentHighlight(highlights)
        }
    }
  }.getOrElse(Future.successful(Nil.asJava))

  def references(
      params: ReferenceParams,
      token: CancelToken,
      additionalAdjust: AdjustRange,
  ): Future[List[ReferencesResult]] = {
    withPCAndAdjustLsp(params) { case (pc, pos, adjust) =>
      val requestParams = new internal.pc.PcReferencesRequest(
        CompilerOffsetParamsUtils.fromPos(pos, token),
        params.getContext().isIncludeDeclaration(),
        JEither.forLeft(pos.start),
      )
      pc.references(requestParams)
        .asScala
        .map(
          _.asScala
            .map(
              adjust.adjustReferencesResult(
                _,
                additionalAdjust,
                requestParams.file.text(),
              )
            )
            .toList
        )
    }
  }.getOrElse(Future.successful(Nil))

  def references(
      id: BuildTargetIdentifier,
      searchFiles: List[AbsolutePath],
      includeDefinition: Boolean,
      symbols: List[String],
      additionalAdjust: AdjustRange,
      isCancelled: () => Boolean,
  ): Future[List[ReferencesResult]] = {
    // we filter only Scala files, since `references` for Java are not implemented
    val filteredFiles = searchFiles.filter(_.isScala)
    val results =
      if (symbols.isEmpty || filteredFiles.isEmpty) Nil
      else
        withUncachedCompiler(id) { compiler =>
          for {
            searchFile <- filteredFiles
            if !isCancelled()
          } yield {
            val uri = searchFile.toURI
            val (input, _, adjust) =
              sourceAdjustments(uri.toString(), compiler.scalaVersion())
            val requestParams = new internal.pc.PcReferencesRequest(
              CompilerVirtualFileParams(uri, input.text),
              includeDefinition,
              JEither.forRight(symbols.head),
              symbols.tail.asJava,
            )
            compiler
              .references(requestParams)
              .asScala
              .map(
                _.asScala
                  .map(
                    adjust
                      .adjustReferencesResult(_, additionalAdjust, input.text)
                  )
                  .toList
              )
          }
        }
          .getOrElse(Nil)

    Future.sequence(results).map(_.flatten)
  }

  def extractMethod(
      doc: TextDocumentIdentifier,
      range: LspRange,
      extractionPos: LspPosition,
      token: CancelToken,
  ): Future[ju.List[TextEdit]] = {
    withPCAndAdjustLsp(doc.getUri(), range, extractionPos) {
      (pc, metaRange, metaExtractionPos, adjust) =>
        val rangeParams = CompilerRangeParamsUtils.fromPos(
          metaRange,
          token,
          outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
        )
        val extractionOffsetParams =
          CompilerOffsetParamsUtils.fromPos(metaExtractionPos, token)
        val result =
          if (
            pc.supportedCodeActions()
              .contains(CodeActionId.ImplementAbstractMembers)
          )
            pc.codeAction(
              rangeParams,
              CodeActionId.ExtractMethod,
              ju.Optional.of(extractionOffsetParams),
            )
          else
            pc.extractMethod(
              rangeParams,
              extractionOffsetParams,
            )

        result.asScala
          .map { edits =>
            adjust.adjustTextEdits(edits)
          }
    }
  }.getOrElse(Future.successful(Nil.asJava))

  def convertToNamedArguments(
      position: TextDocumentPositionParams,
      argIndices: ju.List[Integer],
      token: CancelToken,
  ): Future[ju.List[TextEdit]] = {
    withPCAndAdjustLsp(position) { (pc, pos, adjust) =>
      val offset =
        CompilerOffsetParamsUtils.fromPos(
          pos,
          token,
          outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
        )
      val result =
        if (
          pc.supportedCodeActions()
            .contains(CodeActionId.ConvertToNamedArguments)
        )
          pc.codeAction(
            offset,
            CodeActionId.ConvertToNamedArguments,
            ju.Optional.of(argIndices),
          )
        else
          pc.convertToNamedArguments(offset, argIndices)

      result.asScala
        .map { edits =>
          adjust.adjustTextEdits(edits)
        }
    }
  }.getOrElse(Future.successful(Nil.asJava))

  def implementAbstractMembers(
      params: TextDocumentPositionParams,
      token: CancelToken,
  ): Future[ju.List[TextEdit]] = {
    withPCAndAdjustLsp(params) { (pc, pos, adjust) =>
      val offsetParams = CompilerOffsetParamsUtils.fromPos(
        pos,
        token,
        outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
      )

      val result =
        if (
          pc.supportedCodeActions()
            .contains(CodeActionId.ImplementAbstractMembers)
        )
          pc.codeAction(
            offsetParams,
            CodeActionId.ImplementAbstractMembers,
            None.asJava,
          )
        else
          pc.implementAbstractMembers(offsetParams)

      result.asScala
        .map { edits =>
          adjust.adjustTextEdits(edits)
        }
    }
  }.getOrElse(Future.successful(Nil.asJava))

  def codeAction(
      params: TextDocumentPositionParams,
      token: CancelToken,
      codeActionId: String,
      codeActionPayload: Option[Object],
  ): Future[ju.List[TextEdit]] = {
    withPCAndAdjustLsp(params) { (pc, pos, adjust) =>
      pc.codeAction(
        CompilerOffsetParamsUtils.fromPos(
          pos,
          token,
          outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
        ),
        codeActionId,
        codeActionPayload.asJava,
      ).asScala
        .map { edits =>
          adjust.adjustTextEdits(edits)
        }
    }
  }.getOrElse(Future.successful(Nil.asJava))

  def supportedCodeActions(path: AbsolutePath): ju.List[String] = {
    loadCompiler(path).map { pc =>
      pc.supportedCodeActions()
    }
  }.getOrElse(Nil.asJava)

  def hover(
      params: HoverExtParams,
      token: CancelToken,
  ): Future[Option[HoverSignature]] = {
    withPCAndAdjustLsp(params) { (pc, pos, adjust) =>
      pc.hover(
        CompilerRangeParamsUtils.offsetOrRange(
          pos,
          token,
          outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
        )
      ).asScala
        .map(_.asScala.map { hover => adjust.adjustHoverResp(hover) })
    }
  }.getOrElse(Future.successful(None))

  def prepareRename(
      params: TextDocumentPositionParams,
      token: CancelToken,
  ): Future[ju.Optional[LspRange]] = {
    withPCAndAdjustLsp(params) { (pc, pos, adjust) =>
      pc.prepareRename(
        CompilerRangeParamsUtils.offsetOrRange(
          pos,
          token,
          outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
        )
      ).asScala
        .map { range =>
          range.map(adjust.adjustRange(_))
        }
    }
  }.getOrElse(Future.successful(None.asJava))

  def rename(
      params: RenameParams,
      token: CancelToken,
  ): Future[ju.List[TextEdit]] = {
    withPCAndAdjustLsp(params) { (pc, pos, adjust) =>
      pc.rename(
        CompilerRangeParamsUtils.offsetOrRange(
          pos,
          token,
          outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
        ),
        params.getNewName(),
      ).asScala
        .map { edits =>
          adjust.adjustTextEdits(edits)
        }
    }
  }.getOrElse(Future.successful(Nil.asJava))

  def definition(
      params: TextDocumentPositionParams,
      token: CancelToken,
  ): Future[DefinitionResult] = {
    definition(params = params, token = token, findTypeDef = false)
  }

  def typeDefinition(
      params: TextDocumentPositionParams,
      token: CancelToken,
  ): Future[DefinitionResult] = {
    definition(params = params, token = token, findTypeDef = true)
  }

  def info(
      path: AbsolutePath,
      symbol: String,
  ): Future[Option[PcSymbolInformation]] = {
    loadCompiler(path, forceScala = true)
      .map(
        _.info(symbol).asScala
          .map(_.asScala.map(PcSymbolInformation.from))
      )
      .getOrElse(Future(None))
  }

  def info(
      id: BuildTargetIdentifier,
      symbol: String,
  ): Future[Option[PcSymbolInformation]] = {
    loadCompiler(id)
      .map(
        _.info(symbol).asScala
          .map(_.asScala.map(PcSymbolInformation.from))
      )
      .getOrElse(Future(None))
  }

  private def definition(
      params: TextDocumentPositionParams,
      token: CancelToken,
      findTypeDef: Boolean,
  ): Future[DefinitionResult] =
    withPCAndAdjustLsp(params) { (pc, pos, adjust) =>
      val params = CompilerOffsetParamsUtils.fromPos(
        pos,
        token,
        outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
      )
      val defResult =
        if (findTypeDef) pc.typeDefinition(params)
        else
          pc.definition(CompilerOffsetParamsUtils.fromPos(pos, token))
      defResult.asScala
        .map { c =>
          adjust.adjustLocations(c.locations())
          val definitionPaths = c
            .locations()
            .map { loc =>
              loc.getUri().toAbsolutePath
            }
            .asScala
            .toSet

          val definitionPath = if (definitionPaths.size == 1) {
            Some(definitionPaths.head)
          } else {
            None
          }
          DefinitionResult(
            c.locations(),
            c.symbol(),
            definitionPath,
            None,
            c.symbol(),
          )
        }
    }.getOrElse(Future.successful(DefinitionResult.empty))

  def signatureHelp(
      params: TextDocumentPositionParams,
      token: CancelToken,
  ): Future[SignatureHelp] =
    withPCAndAdjustLsp(params) { (pc, pos, _) =>
      pc.signatureHelp(
        CompilerOffsetParamsUtils.fromPos(
          pos,
          token,
          outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
        )
      ).asScala
    }.getOrElse(Future.successful(new SignatureHelp()))

  def selectionRange(
      params: SelectionRangeParams,
      token: CancelToken,
  ): Future[ju.List[SelectionRange]] = {
    withPCAndAdjustLsp(params) { (pc, positions) =>
      val offsetPositions: ju.List[OffsetParams] =
        positions.map(
          CompilerOffsetParamsUtils.fromPos(
            _,
            token,
            outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
          )
        )
      pc.selectionRange(offsetPositions).asScala
    }.getOrElse(Future.successful(Nil.asJava))
  }

  def getTasty(
      buildTargetId: BuildTargetIdentifier,
      path: AbsolutePath,
  ): Option[Future[String]] = {
    loadCompiler(buildTargetId).map(
      _.getTasty(
        path.toURI,
        config.isHttpEnabled(),
      ).asScala
    )
  }

  /**
   * Gets presentation compiler for a file.
   * @param path for which presentation compiler should be loaded,
   *             resolves build target based on this file
   * @param forceScala if should use Scala pc for `.java` files that are in a Scala build target,
   *                   useful when Scala pc can handle Java files and Java pc implementation of a feature is missing
   */
  def loadCompiler(
      path: AbsolutePath,
      forceScala: Boolean = false,
  ): Option[PresentationCompiler] = {

    def fromBuildTarget: Option[PresentationCompiler] = {
      val target = buildTargets
        .inverseSources(path)

      target match {
        case None =>
          val tmpDirectory = workspace.resolve(Directories.tmp)
          val scalaVersion =
            scalaVersionSelector.fallbackScalaVersion(isAmmonite = false)
          if (!path.toNIO.startsWith(tmpDirectory.toNIO))
            scribe.info(
              s"no build target found for $path. Using presentation compiler with project's scala-library version: ${scalaVersion}"
            )
          Some(fallbackCompiler)
        case Some(value) =>
          if (path.isScalaFilename) loadCompiler(value)
          else if (path.isJavaFilename && forceScala)
            loadCompiler(value)
              .orElse(Some(loadJavaCompiler(value)))
          else if (path.isJavaFilename) Some(loadJavaCompiler(value))
          else None
      }
    }

    if (!path.isScalaFilename && !path.isJavaFilename) None
    else if (path.isWorksheet)
      loadWorksheetCompiler(path).orElse(fromBuildTarget)
    else fromBuildTarget
  }

  def loadWorksheetCompiler(
      path: AbsolutePath
  ): Option[PresentationCompiler] = {
    worksheetProvider.getWorksheetPCData(path).flatMap { data =>
      maybeRestartWorksheetPresentationCompiler(path, data)
      worksheetsCache.get(path).map(_.await)
    }
  }

  private def maybeRestartWorksheetPresentationCompiler(
      path: AbsolutePath,
      data: WorksheetPcData,
  ): Unit = {
    val previousDigest = worksheetsDigests.getOrElse(path, "")
    if (data.digest != previousDigest) {
      worksheetsDigests.put(path, data.digest)
      restartWorksheetPresentationCompiler(
        path,
        data.classpath,
        data.dependencies,
      )
    }
  }

  private def restartWorksheetPresentationCompiler(
      path: AbsolutePath,
      classpath: List[Path],
      sources: List[Path],
  ): Unit = {
    val created: Option[Unit] = for {
      targetId <- buildTargets.inverseSources(path)
      scalaTarget <- buildTargets.scalaTarget(targetId)
      scalaVersion = scalaTarget.scalaVersion
      mtags <- {
        val result = mtagsResolver.resolve(scalaVersion)
        if (result.isEmpty) {
          scribe.warn(s"unsupported Scala ${scalaVersion}")
        }
        result
      }
    } yield {
      jworksheetsCache.put(
        path,
        workDoneProgress.trackBlocking(
          s"${config.icons().sync}Loading worksheet presentation compiler"
        ) {
          ScalaLazyCompiler.forWorksheet(
            scalaTarget,
            mtags,
            classpath,
            sources,
            search,
            completionItemPriority(),
          )
        },
      )
    }

    created.getOrElse {
      jworksheetsCache.put(
        path, {
          val scalaVersion =
            scalaVersionSelector.fallbackScalaVersion(isAmmonite = false)
          StandaloneCompiler(
            scalaVersion,
            classpath,
            sources,
            Some(search),
            completionItemPriority(),
          )
        },
      )
    }
  }

  private def loadJavaCompiler(
      targetId: BuildTargetIdentifier
  ): PresentationCompiler = {
    jcache
      .computeIfAbsent(
        PresentationCompilerKey.JavaBuildTarget(targetId),
        { _ =>
          workDoneProgress.trackBlocking(
            s"${config.icons().sync}Loading presentation compiler"
          ) {
            JavaLazyCompiler(targetId, search, completionItemPriority())
          }
        },
      )
      .await
  }

  private def loadCompiler(
      targetId: BuildTargetIdentifier
  ): Option[PresentationCompiler] =
    withKeyAndDefault(targetId) { case (key, getCompiler) =>
      Option(jcache.computeIfAbsent(key, { _ => getCompiler() }).await)
    }

  private def withKeyAndDefault[T](
      targetId: BuildTargetIdentifier
  )(
      f: (PresentationCompilerKey, () => MtagsPresentationCompiler) => Option[T]
  ): Option[T] = {
    buildTargets.scalaTarget(targetId).flatMap { scalaTarget =>
      val scalaVersion = scalaTarget.scalaVersion
      mtagsResolver.resolve(scalaVersion) match {
        case Some(mtags) =>
          def default() =
            workDoneProgress.trackBlocking(
              s"${config.icons().sync}Loading presentation compiler"
            ) {
              // есть референс на сёрч
              ScalaLazyCompiler(
                scalaTarget,
                mtags,
                search,
                completionItemPriority(),
              )
            }
          val key =
            PresentationCompilerKey.ScalaBuildTarget(scalaTarget.info.getId)
          f(key, default)
        case None =>
          scribe.warn(s"unsupported Scala ${scalaTarget.scalaVersion}")
          None
      }
    }
  }

  private def withUncachedCompiler[T](
      targetId: BuildTargetIdentifier
  )(f: PresentationCompiler => T): Option[T] =
    withKeyAndDefault(targetId) { case (key, getCompiler) =>
      val (out, shouldShutdown) = Option(jcache.get(key))
        .map((_, false))
        .getOrElse((getCompiler(), true))
      if (shouldShutdown)
        scribe.debug(s"starting uncached presentation compiler for $targetId")
      val compiler = Option(out.await)
      val result = compiler.map(f)
      if (shouldShutdown) compiler.foreach(_.shutdown())
      result
    }

  private def withPCAndAdjustLsp[T](
      params: SelectionRangeParams
  )(
      fn: (PresentationCompiler, ju.List[Position]) => T
  ): Option[T] = {
    val path = params.getTextDocument.getUri.toAbsolutePath
    loadCompiler(path).map { compiler =>
      val input = path
        .toInputFromBuffers(buffers)
        .copy(path = params.getTextDocument.getUri)

      val positions =
        params.getPositions().asScala.flatMap(_.toMeta(input)).asJava

      fn(compiler, positions)
    }
  }

  private def withPCAndAdjustLsp[T](
      params: TextDocumentPositionParams
  )(
      fn: (PresentationCompiler, Position, AdjustLspData) => T
  ): Option[T] = {
    val path = params.getTextDocument.getUri.toAbsolutePath
    loadCompiler(path).flatMap { compiler =>
      val (input, pos, adjust) =
        sourceAdjustments(
          params,
          compiler.scalaVersion(),
        )
      pos
        .toMeta(input)
        .map(metaPos => fn(compiler, metaPos, adjust))
    }
  }

  private def withPCAndAdjustLsp[T](
      params: InlayHintParams
  )(
      fn: (PresentationCompiler, Position, AdjustLspData) => T
  ): Option[T] = {
    val path = params.getTextDocument.getUri.toAbsolutePath
    loadCompiler(path).flatMap { case compiler =>
      val (input, pos, adjust) =
        sourceAdjustments(
          params,
          compiler.scalaVersion(),
        )
      pos
        .toMeta(input)
        .map(metaPos => fn(compiler, metaPos, adjust))
    }
  }

  private def withPCAndAdjustLsp[T](
      uri: String,
      range: LspRange,
      extractionPos: LspPosition,
  )(
      fn: (
          PresentationCompiler,
          Position,
          Position,
          AdjustLspData,
      ) => T
  ): Option[T] = {
    val path = uri.toAbsolutePath
    loadCompiler(path).flatMap { compiler =>
      val (input, adjustRequest, adjustResponse) =
        sourceAdjustments(
          uri,
          compiler.scalaVersion(),
        )
      for {
        metaRange <- new LspRange(
          adjustRequest(range.getStart()),
          adjustRequest(range.getEnd()),
        ).toMeta(input)
        metaExtractionPos <- adjustRequest(extractionPos).toMeta(input)
      } yield fn(
        compiler,
        metaRange,
        metaExtractionPos,
        adjustResponse,
      )
    }
  }

  private def withPCAndAdjustLsp[T](
      params: HoverExtParams
  )(
      fn: (
          PresentationCompiler,
          Position,
          AdjustLspData,
      ) => T
  ): Option[T] = {

    val path = params.textDocument.getUri.toAbsolutePath
    loadCompiler(path).flatMap { compiler =>
      if (params.range != null) {
        val (input, range, adjust) = sourceAdjustments(
          params,
          compiler.scalaVersion(),
        )
        range.toMeta(input).map(fn(compiler, _, adjust))

      } else {
        val positionParams =
          new TextDocumentPositionParams(
            params.textDocument,
            params.getPosition,
          )
        val (input, pos, adjust) = sourceAdjustments(
          positionParams,
          compiler.scalaVersion(),
        )
        pos.toMeta(input).map(fn(compiler, _, adjust))
      }
    }
  }

  private def sourceAdjustments(
      params: TextDocumentPositionParams,
      scalaVersion: String,
  ): (Input.VirtualFile, LspPosition, AdjustLspData) = {
    val (input, adjustRequest, adjustResponse) = sourceAdjustments(
      params.getTextDocument().getUri(),
      scalaVersion,
    )
    (input, adjustRequest(params.getPosition()), adjustResponse)
  }

  private def sourceAdjustments(
      params: InlayHintParams,
      scalaVersion: String,
  ): (Input.VirtualFile, LspRange, AdjustLspData) = {
    val (input, adjustRequest, adjustResponse) = sourceAdjustments(
      params.getTextDocument.getUri(),
      scalaVersion,
    )
    val start = params.getRange.getStart()
    val end = params.getRange.getEnd()
    val newRange = new LspRange(adjustRequest(start), adjustRequest(end))
    (input, newRange, adjustResponse)
  }

  private def sourceAdjustments(
      params: HoverExtParams,
      scalaVersion: String,
  ): (Input.VirtualFile, LspRange, AdjustLspData) = {
    val (input, adjustRequest, adjustResponse) = sourceAdjustments(
      params.textDocument.getUri(),
      scalaVersion,
    )
    val start = params.range.getStart()
    val end = params.range.getEnd()
    val newRange = new LspRange(adjustRequest(start), adjustRequest(end))
    (input, newRange, adjustResponse)
  }

  private def sourceAdjustments(
      uri: String,
      scalaVersion: String,
  ): (Input.VirtualFile, LspPosition => LspPosition, AdjustLspData) = {
    val path = uri.toAbsolutePath
    sourceMapper.pcMapping(path, scalaVersion)
  }

  private def toDebugCompletionType(
      kind: CompletionItemKind
  ): d.CompletionItemType = {
    kind match {
      case CompletionItemKind.Constant => d.CompletionItemType.VALUE
      case CompletionItemKind.Value => d.CompletionItemType.VALUE
      case CompletionItemKind.Keyword => d.CompletionItemType.KEYWORD
      case CompletionItemKind.Class => d.CompletionItemType.CLASS
      case CompletionItemKind.TypeParameter => d.CompletionItemType.CLASS
      case CompletionItemKind.Operator => d.CompletionItemType.FUNCTION
      case CompletionItemKind.Field => d.CompletionItemType.FIELD
      case CompletionItemKind.Method => d.CompletionItemType.METHOD
      case CompletionItemKind.Unit => d.CompletionItemType.UNIT
      case CompletionItemKind.Enum => d.CompletionItemType.ENUM
      case CompletionItemKind.Interface => d.CompletionItemType.INTERFACE
      case CompletionItemKind.Constructor => d.CompletionItemType.CONSTRUCTOR
      case CompletionItemKind.Folder => d.CompletionItemType.FILE
      case CompletionItemKind.Module => d.CompletionItemType.MODULE
      case CompletionItemKind.EnumMember => d.CompletionItemType.ENUM
      case CompletionItemKind.Snippet => d.CompletionItemType.SNIPPET
      case CompletionItemKind.Function => d.CompletionItemType.FUNCTION
      case CompletionItemKind.Color => d.CompletionItemType.COLOR
      case CompletionItemKind.Text => d.CompletionItemType.TEXT
      case CompletionItemKind.Property => d.CompletionItemType.PROPERTY
      case CompletionItemKind.Reference => d.CompletionItemType.REFERENCE
      case CompletionItemKind.Variable => d.CompletionItemType.VARIABLE
      case CompletionItemKind.Struct => d.CompletionItemType.MODULE
      case CompletionItemKind.File => d.CompletionItemType.FILE
      case _ => d.CompletionItemType.TEXT
    }
  }

  private def toDebugCompletionItem(
      item: CompletionItem,
      adjustStart: Int,
      insertTextPosition: Position.Range,
  ): d.CompletionItem = {
    val debugItem = new d.CompletionItem()
    debugItem.setLabel(item.getLabel())
    val (newText, range) = Option(item.getTextEdit()).map(_.asScala) match {
      case Some(Left(textEdit)) =>
        (textEdit.getNewText, textEdit.getRange)
      case Some(Right(insertReplace)) =>
        (insertReplace.getNewText, insertReplace.getReplace)
      case None =>
        Option(item.getInsertText()).orElse(Option(item.getLabel())) match {
          case Some(text) =>
            (text, insertTextPosition.toLsp)
          case None =>
            throw new RuntimeException(
              "Completion item does not contain expected data"
            )
        }
    }
    val start = range.getStart().getCharacter + adjustStart

    val length = range.getEnd().getCharacter() - range.getStart().getCharacter()
    debugItem.setLength(length)

    // remove snippets, since they are not supported in DAP
    val fullText = newText.replaceAll("\\$[1-9]+", "")

    val selection = fullText.indexOf("$0")

    // Find the spot for the cursor
    if (selection >= 0) {
      debugItem.setSelectionStart(selection)
    }

    debugItem.setDetail(item.getDetail())
    debugItem.setText(fullText.replace("$0", ""))
    debugItem.setStart(start)
    debugItem.setType(toDebugCompletionType(item.getKind()))
    debugItem.setSortText(item.getFilterText())
    debugItem
  }

  def semanticdbTextDocument(
      source: AbsolutePath,
      text: String,
  ): s.TextDocument = {
    val pc = loadCompiler(source).getOrElse(fallbackCompiler)

    val (prependedLinesSize, modifiedText) =
      Option
        .when(source.isSbt)(
          buildTargets
            .sbtAutoImports(source)
        )
        .flatten
        .fold((0, text))(imports =>
          (imports.size, SbtBuildTool.prependAutoImports(text, imports))
        )

    // NOTE(olafur): it's unfortunate that we block on `semanticdbTextDocument`
    // here but to avoid it we would need to refactor the `Semanticdbs` trait,
    // which requires more effort than it's worth.
    val params = new CompilerVirtualFileParams(
      source.toURI,
      modifiedText,
      token = EmptyCancelToken,
      outlineFiles = outlineFilesProvider.getOutlineFiles(pc.buildTargetId()),
    )
    val bytes = pc
      .semanticdbTextDocument(params)
      .get(
        config.initialConfig.compilers.timeoutDelay,
        config.initialConfig.compilers.timeoutUnit,
      )
    val textDocument = {
      val doc = s.TextDocument.parseFrom(bytes)
      if (doc.text.isEmpty()) doc.withText(text)
      else doc
    }
    if (prependedLinesSize > 0)
      cleanupAutoImports(textDocument, text, prependedLinesSize)
    else textDocument
  }

  private def cleanupAutoImports(
      document: s.TextDocument,
      originalText: String,
      linesSize: Int,
  ): s.TextDocument = {

    def adjustRange(range: s.Range): Option[s.Range] = {
      val nextStartLine = range.startLine - linesSize
      val nextEndLine = range.endLine - linesSize
      if (nextEndLine >= 0) {
        val nextRange = range.copy(
          startLine = nextStartLine,
          endLine = nextEndLine,
        )
        Some(nextRange)
      } else None
    }

    val adjustedOccurences =
      document.occurrences.flatMap { occurence =>
        occurence.range
          .flatMap(adjustRange)
          .map(r => occurence.copy(range = Some(r)))
      }

    val adjustedDiagnostic =
      document.diagnostics.flatMap { diagnostic =>
        diagnostic.range
          .flatMap(adjustRange)
          .map(r => diagnostic.copy(range = Some(r)))
      }

    val adjustedSynthetic =
      document.synthetics.flatMap { synthetic =>
        synthetic.range
          .flatMap(adjustRange)
          .map(r => synthetic.copy(range = Some(r)))
      }

    s.TextDocument(
      schema = document.schema,
      uri = document.uri,
      text = originalText,
      md5 = MD5.compute(originalText),
      language = document.language,
      symbols = document.symbols,
      occurrences = adjustedOccurences,
      diagnostics = adjustedDiagnostic,
      synthetics = adjustedSynthetic,
    )
  }

}

object Compilers {

  sealed trait PresentationCompilerKey
  object PresentationCompilerKey {
    final case class ScalaBuildTarget(id: BuildTargetIdentifier)
        extends PresentationCompilerKey
    final case class JavaBuildTarget(id: BuildTargetIdentifier)
        extends PresentationCompilerKey
    case object Default extends PresentationCompilerKey
  }

}
