package scala.meta.internal.pc

import scala.reflect.internal.FatalError

import scala.meta.internal.mtags.MtagsEnrichments._

trait AutoImports { this: MetalsGlobal =>

  def doLocateImportContext(
      pos: Position,
      autoImport: Option[AutoImportPosition] = None
  ): Context = {
    try
      doLocateContext(
        autoImport.fold(pos)(i => pos.focus.withPoint(i.offset))
      )
    catch {
      case _: FatalError =>
        (for {
          unit <- getUnit(pos.source)
          tree <- unit.contexts.headOption
        } yield tree.context).getOrElse(NoContext)
    }
  }

  def isImportPosition(pos: Position): Boolean =
    findLastVisitedParentTree(pos).exists(_.isInstanceOf[Import])

  def notPackageObject(pkg: PackageDef): Boolean =
    pkg.stats.exists {
      case ModuleDef(_, name, _) => name.toString != "package"
      case _ => true
    }

  def autoImportPosition(
      pos: Position,
      text: String
  ): Option[AutoImportPosition] = {
    findLastVisitedParentTree(pos) match {
      case Some(_: Import) => None
      case _ =>
        def forScalaSource =
          for {
            pkg <- lastVisitedParentTrees.collectFirst {
              case pkg: PackageDef if notPackageObject(pkg) => pkg
            }
            if pkg.symbol != rootMirror.EmptyPackage ||
              pkg.stats.headOption.exists(_.isInstanceOf[Import])
          } yield {
            val lastImportOpt = pkg.stats
              .takeWhile(_.isInstanceOf[Import])
              .lastOption
            scribe.info(s"lastImportOpt: ${lastImportOpt}")
            val padTop = lastImportOpt.isEmpty
            val lastImportOrPkg = lastImportOpt.getOrElse(pkg.pid)
            scribe.info(s"lastImportOrPkg: ${lastImportOrPkg}")
            // here is pos creation
            scribe.info(s"what is pos: ${pos}")
            scribe.info(s"what is pos.source: ${pos.source}")
            scribe.info(
              s"what is lastImportOrPkg.pos.focusEnd: ${lastImportOrPkg.pos.focusEnd}"
            )

            // from this generates final position. Fixes should be here, i guess

            // entire file
            // scribe.info(s"here is text inside autoImportPosition: '''${text}'''")

            // maybe not here
            // todo: try hack here position after getting position and scalafix.fix collect imports
            val aipos =
              new AutoImportPosition(
                // offset is int by chars from file beginning
                pos.source.lineToOffset(lastImportOrPkg.pos.focusEnd.line),
                text,
                padTop
              )
            scribe.info(s"here is autoImportPosition: ${aipos}")
            aipos
          }

        def forScript(isAmmonite: Boolean) = {
          val startScriptOffest = {
            if (isAmmonite)
              ScriptFirstImportPosition.ammoniteScStartOffset(text)
            else ScriptFirstImportPosition.scalaCliScStartOffset(text)
          }

          val scriptModuleDefAndPos =
            startScriptOffest.flatMap { offset =>
              val startPos = pos.withStart(offset).withEnd(offset)
              lastVisitedParentTrees
                .collectFirst {
                  case mod: ModuleDef if mod.pos.overlaps(startPos) => mod
                }
                .map(mod => (mod, offset))
            }

          val moduleDefAndPos = scriptModuleDefAndPos.orElse(
            lastVisitedParentTrees
              .collectFirst { case mod: ModuleDef => mod }
              .map(mod => (mod, 0))
          )
          for {
            (obj, firstImportOffset) <- moduleDefAndPos
          } yield {
            val lastImportOpt = obj.impl.body.iterator
              .dropWhile {
                case d: DefDef => d.name.decoded == "<init>"
                case _ => false
              }
              .takeWhile(_.isInstanceOf[Import])
              .lastOption

            val offset = lastImportOpt
              .map(_.pos.focusEnd.line)
              .map(pos.source.lineToOffset)
              .getOrElse(firstImportOffset)
            new AutoImportPosition(
              offset,
              text,
              padTop = false
            )
          }
        }

        def fileStart =
          AutoImportPosition(
            ScriptFirstImportPosition.infer(text),
            0,
            padTop = false
          )

        val path = pos.source.path
        val scriptPos =
          if (path.isAmmoniteGeneratedFile) forScript(isAmmonite = true)
          else if (path.isScalaCLIGeneratedFile) forScript(isAmmonite = false)
          else None

        scribe.info(
          s"here is sources, scriptPos ${scriptPos}, forScalaSource: ${forScalaSource}, fileStart:${fileStart}"
        )
        scriptPos
          .orElse(forScalaSource)
          .orElse(Some(fileStart))
    }
  }

}
