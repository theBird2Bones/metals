package scala.meta.internal.pc

import java.nio.file.Files
import java.nio.file.Paths
import java.nio.file.StandardOpenOption
import java.{util => ju}

import scala.collection.Seq
import scala.collection.immutable.HashMap
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.ArrayBuffer
import scala.{meta => m}

import scala.meta.internal.jdk.CollectionConverters._
import scala.meta.classifiers._
import scala.meta.inputs._
import scala.meta.internal.metals.PcQueryContext
import scala.meta.io.AbsolutePath
import scala.meta.pc
import scala.meta.pc.SymbolDocumentation

import org.eclipse.{lsp4j => l}
import scala.util.matching.Regex
import scala.meta.XtensionSyntax

trait OrganizedImports {

  def sort(
      next: m.Import,
      globals: List[m.Import]
  ): String /*List[m.Import]*/ = {
    val groups = groupImporters(
      (next :: globals)
        .flatMap(_.importers)
    )

    insertOrganizedImports(groups)

  }

  private def groupImporters(
      importers: Seq[m.Importer]
  ): Seq[ImportGroup] = {
    importers
      .groupBy(matchImportGroup(_)) // Groups imports by importer prefix.
      .mapValues(
        deduplicateImportees _ andThen organizeImportGroup
      )
      .map { case (index, imports) => ImportGroup(index, imports) }
      .toSeq
      .sortBy(_.index)
  }

  private def matchImportGroup(importer: m.Importer): Int = {
    val matchedGroups = matchers
      .map(_.matches(importer))
      .zipWithIndex
      .filter { case (length, _) => length > 0 }

    if (matchedGroups.isEmpty) wildcardGroupIndex
    else {
      val (_, index) = matchedGroups.maxBy { case (length, _) => length }
      index
    }
  }

  private def deduplicateImportees(
      importers: Seq[m.Importer]
  ): Seq[m.Importer] = {
    // Scalameta `Tree` nodes do not provide structural equality comparisons, here we pretty-print
    // them and compare the string results.
    val seenImportees = mutable.Set.empty[(String, String)]

    importers flatMap { importer =>
      importer filterImportees { importee =>
        importee.is[m.Importee.Wildcard] || importee.is[m.Importee.GivenAll] ||
        seenImportees.add(importee.syntax -> importer.ref.syntax)
      }
    }
  }

  // def filterImportees(f: m.Importee => Boolean): Option[m.Importer] = {
  //   val filtered = importer.importees filter f
  //   if (filtered.length == importer.importees.length) Some(importer)
  //   else if (filtered.isEmpty) None
  //   else Some(importer.copy(importees = filtered))
  // }

  private def organizeImportGroup(
      importers: Seq[m.Importer]
  ): Seq[m.Importer] = {
    val importeesSorted = locally {
      config.groupedImports match {
        // case GroupedImports.Merge =>
        //   mergeImporters(diagnostics)(importers, aggressive = false)
        // case GroupedImports.AggressiveMerge =>
        //   mergeImporters(diagnostics)(importers, aggressive = true)
        // case GroupedImports.Explode =>
        //   explodeImportees(importers)
        case GroupedImports.Keep => // todo: implement all
          importers
      }
    } map (coalesceImportees _ andThen sortImportees)

    config.importsOrder match {
      // https://github.com/liancheng/scalafix-organize-imports/issues/84: The Scalameta `Tree` node pretty-printer
      // checks whether the node originates directly from the parser. If yes, the original source
      // code text is returned, and may interfere imports sort order. The `.copy()` call below
      // erases the source position information so that the pretty-printer would actually
      // pretty-print an `Importer` into a single line.
      case ImportsOrder.Ascii =>
        importeesSorted sortBy (i => importerSyntax(i.copy()))
      case ImportsOrder.SymbolsFirst =>
        sortImportersSymbolsFirst(importeesSorted)
      case ImportsOrder.Keep =>
        importeesSorted
    }
  }

  private def sortImportersSymbolsFirst(
      importers: Seq[m.Importer]
  ): Seq[m.Importer] = {
    importers.sortBy { importer =>
      // See the comment marked with "issues/84" for why a `.copy()` is needed.
      val syntax = importer.copy().syntax

      importer match {
        case m.Importer(_, m.Importee.Wildcard() :: Nil) =>
          val wildcardSyntax = m.Importee.Wildcard().syntax
          syntax.patch(
            syntax.lastIndexOfSlice(s".$wildcardSyntax"),
            ".\u0001",
            2
          )

        case _ if importer.isCurlyBraced =>
          syntax
            .replaceFirst("[{]", "\u0002")
            .patch(syntax.lastIndexOf("}"), "\u0002", 1)

        case _ => syntax
      }
    }
  }

  private def coalesceImportees(importer: m.Importer): m.Importer = {
    val Importees(names, renames, unimports, givens, _, _) = importer.importees

    config.coalesceToWildcardImportThreshold
      .filter(importer.importees.length > _)
      // Skips if there's no `Name`s or `Given`s. `Rename`s and `Unimport`s cannot be coalesced.
      .filterNot(_ => names.isEmpty && givens.isEmpty)
      .map {
        case _ if givens.isEmpty =>
          renames ++ unimports :+ m.Importee.Wildcard()
        case _ if names.isEmpty => renames ++ unimports :+ m.Importee.GivenAll()
        case _ =>
          renames ++ unimports :+ m.Importee.GivenAll() :+ m.Importee.Wildcard()
      }
      .map(importees => importer.copy(importees = importees))
      .getOrElse(importer)
  }

  private def sortImportees(importer: m.Importer): m.Importer = {
    import ImportSelectorsOrder._

    // The Scala language spec allows an import expression to have at most one final wildcard, which
    // can only appears in the last position.
    val (wildcards, others) =
      importer.importees partition (i =>
        i.is[m.Importee.Wildcard] || i.is[m.Importee.GivenAll]
      )

    val orderedImportees = config.importSelectorsOrder match {
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
      config.importSelectorsOrder == Keep ||
        (importer.importees corresponds orderedImportees) { (lhs, rhs) =>
          lhs.syntax == rhs.syntax
        }

    if (alreadySorted) importer else importer.copy(importees = orderedImportees)
  }

  private def sortImporteesSymbolsFirst(
      importees: List[m.Importee]
  ): List[m.Importee] = {
    val symbols = ArrayBuffer.empty[m.Importee]
    val lowerCases = ArrayBuffer.empty[m.Importee]
    val upperCases = ArrayBuffer.empty[m.Importee]

    importees.foreach {
      case i if i.syntax.head.isLower => lowerCases += i
      case i if i.syntax.head.isUpper => upperCases += i
      case i => symbols += i
    }

    List(symbols, lowerCases, upperCases) flatMap (_ sortBy (_.syntax))
  }
  private def importerSyntax(importer: m.Importer): String = {
    importer.pos match {
      case pos: m.Position.Range =>
        // Position found, implies that `importer` was directly parsed from the source code. Rewrite
        // importees to ensure they follow the target dialect. For importers with a single importee,
        // strip enclosing braces if they exist (or add/preserve them for Rename & Unimport on Scala 2).

        val syntax = new StringBuilder(pos.text)

        def patchSyntax(
            t: m.Tree,
            newSyntax: String
        ) = {
          val start = t.pos.start - pos.start
          syntax.replace(start, t.pos.end - pos.start, newSyntax)

          if (importer.importees.length == 1) {
            val end = t.pos.start - pos.start + newSyntax.length
            (
              syntax.take(start).lastIndexOf('{'),
              syntax.indexOf('}', end),
              importer.isCurlyBraced
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
          case i @ m.Importee.Rename(_, _) =>
            patchSyntax(i, i.copy().syntax)
          case i @ m.Importee.Unimport(_) =>
            patchSyntax(i, i.copy().syntax)
          case i @ m.Importee.Wildcard() =>
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
  }

  private def insertOrganizedImports(
      importGroups: Seq[ImportGroup]
  ): String = {
    val prettyPrintedGroups = importGroups.map {
      case ImportGroup(index, imports) =>
        index -> prettyPrintImportGroup(imports)
    }

    val blankLines = {
      // Indices of all blank lines configured in `OrganizeImports.groups`, either automatically or
      // manually.
      val blankLineIndices = matchers.zipWithIndex.collect {
        case (ImportMatcher.---, index) => index
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
      // case (line, _) => " " * token.pos.startColumn + line
    }
    indented.mkString("\n")
    // Patch.addLeft(token, indented mkString "\n")
  }
  private def prettyPrintImportGroup(group: Seq[m.Importer]): String = {
    group
      .map(i => "import " + importerSyntax(i))
      .mkString("\n")
  }

  val config = OrganizeImportsConfig()

  private val matchers = buildImportMatchers(config)
  private val wildcardGroupIndex: Int = matchers indexOf ImportMatcher.*
  private def buildImportMatchers(
      config: OrganizeImportsConfig
  ): Seq[ImportMatcher] = {
    val withWildcard = {
      val parsed = config.groups map ImportMatcher.parse
      // The wildcard group should always exist. Appends one at the end if omitted.
      if (parsed contains ImportMatcher.*) parsed else parsed :+ ImportMatcher.*
    }

    // Inserts a blank line marker between adjacent import groups when `blankLines` is `Auto`.
    config.blankLines match {
      case BlankLines.Manual => withWildcard
      case BlankLines.Auto =>
        withWildcard.flatMap(_ :: ImportMatcher.--- :: Nil)
    }
  }

  implicit private class ImporterExtension(importer: m.Importer) {

    /**
     * Checks whether the `Importer` should be curly-braced when pretty-printed.
     */
    def isCurlyBraced: Boolean = {
      val importees @ Importees(_, renames, unimports, _, _, _) =
        importer.importees

      importees.length > 1 ||
      ((renames.length == 1 || unimports.length == 1)
      // && !targetDialect.allowAsForImportRename
      )
    }

    /**
     * Returns an `Importer` with all the `Importee`s that are selected from the
     * input `Importer` and satisfy a predicate. If all the `Importee`s are
     * selected, the input `Importer` instance is returned to preserve the
     * original source level formatting. If none of the `Importee`s are
     * selected, returns a `None`.
     */
    def filterImportees(f: m.Importee => Boolean): Option[m.Importer] = {
      val filtered = importer.importees filter f
      if (filtered.length == importer.importees.length) Some(importer)
      else if (filtered.isEmpty) None
      else Some(importer.copy(importees = filtered))
    }

    /** Returns true if the `Importer` contains a standalone wildcard. */
    def hasWildcard: Boolean = {
      val Importees(_, _, unimports, _, _, wildcard) = importer.importees
      unimports.isEmpty && wildcard.nonEmpty
    }

    /** Returns true if the `Importer` contains a standalone given wildcard. */
    def hasGivenAll: Boolean = {
      val Importees(_, _, unimports, _, givenAll, _) = importer.importees
      unimports.isEmpty && givenAll.nonEmpty
    }
  }
  implicit class XtensionClassifiable[T: Classifiable](x: T) {
    type C[U] = Classifier[T, U]

    def is[U](implicit c: C[U]): Boolean = c(x)
    def isNot[U](implicit c: C[U]): Boolean = !c(x)

    def isAnyOf(cs: C[_]*): Boolean = cs.exists(_(x))

    def isAny[U1, U2](implicit c1: C[U1], c2: C[U2]): Boolean = c1(x) || c2(x)

    def isAny[U1, U2, U3](implicit c1: C[U1], c2: C[U2], c3: C[U3]): Boolean =
      c1(x) || c2(x) ||
        c3(x)

    def isAny[U1, U2, U3, U4](implicit
        c1: C[U1],
        c2: C[U2],
        c3: C[U3],
        c4: C[U4]
    ): Boolean =
      c1(x) || c2(x) || c3(x) || c4(x)
  }
}

private case class ImportGroup(index: Int, imports: Seq[m.Importer])

final case class OrganizeImportsConfig(
    blankLines: BlankLines = BlankLines.Auto,
    coalesceToWildcardImportThreshold: Option[Int] = None,
    expandRelative: Boolean = false,
    groupExplicitlyImportedImplicitsSeparately: Boolean = false,
    groupedImports: GroupedImports = GroupedImports.Explode,
    groups: Seq[String] = Seq(
      "*",
      "re:(javax?|scala)\\."
    ),
    importSelectorsOrder: ImportSelectorsOrder = ImportSelectorsOrder.Ascii,
    importsOrder: ImportsOrder = ImportsOrder.Ascii,
    preset: Preset = Preset.DEFAULT,
    removeUnused: Boolean = true,
    targetDialect: TargetDialect = TargetDialect.StandardLayout
)

sealed trait BlankLines

object BlankLines {
  case object Auto extends BlankLines
  case object Manual extends BlankLines

  def all: List[BlankLines] =
    List(Auto, Manual)

  // implicit def reader: ConfDecoder[BlankLines] =
  //   ReaderUtil.fromMap(all.map(x => x.toString -> x).toMap)

  // implicit def writer: ConfEncoder[BlankLines] =
  //   ConfEncoder.instance(v => Conf.Str(v.toString))
}

sealed trait GroupedImports

object GroupedImports {
  case object AggressiveMerge extends GroupedImports
  case object Merge extends GroupedImports
  case object Explode extends GroupedImports
  case object Keep extends GroupedImports

  def all: List[GroupedImports] =
    List(AggressiveMerge, Merge, Explode, Keep)

  // implicit def reader: ConfDecoder[GroupedImports] =
  //   ReaderUtil.fromMap(all.map(x => x.toString -> x).toMap)

  // implicit def writer: ConfEncoder[GroupedImports] =
  //   ConfEncoder.instance(v => Conf.Str(v.toString))
}

sealed trait ImportSelectorsOrder

object ImportSelectorsOrder {
  case object Ascii extends ImportSelectorsOrder
  case object SymbolsFirst extends ImportSelectorsOrder
  case object Keep extends ImportSelectorsOrder

  def all: List[ImportSelectorsOrder] =
    List(Ascii, SymbolsFirst, Keep)

  // implicit def reader: ConfDecoder[ImportSelectorsOrder] =
  //   ReaderUtil.fromMap(all.map(x => x.toString -> x).toMap)

  // implicit def writer: ConfEncoder[ImportSelectorsOrder] =
  //   ConfEncoder.instance(v => Conf.Str(v.toString))
}

sealed trait ImportsOrder

object ImportsOrder {
  case object Ascii extends ImportsOrder
  case object SymbolsFirst extends ImportsOrder
  case object Keep extends ImportsOrder

  def all: List[ImportsOrder] =
    List(Ascii, SymbolsFirst, Keep)

  // implicit def reader: ConfDecoder[ImportsOrder] =
  //   ReaderUtil.fromMap(all.map(x => x.toString -> x).toMap)

  // implicit def writer: ConfEncoder[ImportsOrder] =
  //   ConfEncoder.instance(v => Conf.Str(v.toString))
}

sealed trait Preset

object Preset {
  case object DEFAULT extends Preset
  case object INTELLIJ_2020_3 extends Preset

  def all: List[Preset] =
    List(DEFAULT, INTELLIJ_2020_3)

  // implicit def reader: ConfDecoder[Preset] =
  //   ReaderUtil.fromMap(all.map(x => x.toString -> x).toMap)

  // implicit def writer: ConfEncoder[Preset] =
  //   ConfEncoder.instance(v => Conf.Str(v.toString))
}

sealed trait TargetDialect
object TargetDialect {
  case object Auto extends TargetDialect
  case object Scala2 extends TargetDialect
  case object Scala3 extends TargetDialect
  case object StandardLayout extends TargetDialect

  def all: List[TargetDialect] =
    List(Auto, Scala2, Scala3, StandardLayout)

  // implicit def reader: ConfDecoder[TargetDialect] =
  //   ReaderUtil.fromMap(all.map(x => x.toString -> x).toMap)

  // implicit def writer: ConfEncoder[TargetDialect] =
  //   ConfEncoder.instance(v => Conf.Str(v.toString))
}

sealed trait ImportMatcher {
  def matches(i: m.Importer): Int
}

object ImportMatcher {
  def parse(pattern: String): ImportMatcher =
    pattern match {
      case p if p startsWith "re:" => RE(new Regex(p stripPrefix "re:"))
      case "---" => ---
      case "*" => *
      case p => PlainText(p)
    }

  case class RE(pattern: Regex) extends ImportMatcher {
    override def matches(i: m.Importer): Int =
      pattern findPrefixMatchOf i.syntax map (_.end) getOrElse 0
  }

  case class PlainText(pattern: String) extends ImportMatcher {
    override def matches(i: m.Importer): Int =
      if (i.syntax startsWith pattern) pattern.length else 0
  }

  case object * extends ImportMatcher {
    // The wildcard matcher matches nothing. It is special-cased at the end of the import group
    // matching process.
    def matches(importer: m.Importer): Int = 0
  }

  case object --- extends ImportMatcher {
    // Blank line matchers are pseudo matchers matching nothing. They are special-cased at the end
    // of the import group matching process.
    override def matches(i: m.Importer): Int = 0
  }
}
object Importees {
  def unapply(importees: Seq[m.Importee]): Option[
    (
        List[m.Importee.Name],
        List[m.Importee.Rename],
        List[m.Importee.Unimport],
        List[m.Importee.Given],
        Option[m.Importee.GivenAll],
        Option[m.Importee.Wildcard]
    )
  ] = {
    val names = ArrayBuffer.empty[m.Importee.Name]
    val renames = ArrayBuffer.empty[m.Importee.Rename]
    val givens = ArrayBuffer.empty[m.Importee.Given]
    val unimports = ArrayBuffer.empty[m.Importee.Unimport]
    var maybeWildcard: Option[m.Importee.Wildcard] = None
    var maybeGivenAll: Option[m.Importee.GivenAll] = None

    importees foreach {
      case i: m.Importee.Wildcard => maybeWildcard = Some(i)
      case i: m.Importee.Unimport => unimports += i
      case i: m.Importee.Rename => renames += i
      case i: m.Importee.Name => names += i
      case i: m.Importee.Given => givens += i
      case i: m.Importee.GivenAll => maybeGivenAll = Some(i)
    }

    Option(
      (
        names.toList,
        renames.toList,
        unimports.toList,
        givens.toList,
        maybeGivenAll,
        maybeWildcard
      )
    )
  }
}
