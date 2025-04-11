package scala.meta.internal.metals

import java.util.Properties

import scala.meta.internal.jdk.CollectionConverters._
import scala.meta.internal.pc.PresentationCompilerConfigImpl
import scala.meta.io.AbsolutePath
import scala.meta.pc.PresentationCompilerConfig.OverrideDefFormat

import org.eclipse.lsp4j.DidChangeWatchedFilesRegistrationOptions
import org.eclipse.lsp4j.FileSystemWatcher
import org.eclipse.lsp4j.jsonrpc.messages.Either
import metaconfig._
import metaconfig.generic._
import scala.reflect.ClassTag
import scala.meta.Importer
import scala.util.matching.Regex

object Configs {

  final case class GlobSyntaxConfig(value: String) {
    import GlobSyntaxConfig._
    def isUri: Boolean = this == uri
    def isVscode: Boolean = this == vscode
    def registrationOptions(
        workspace: AbsolutePath
    ): DidChangeWatchedFilesRegistrationOptions = {
      val root: String =
        if (isVscode) workspace.toString()
        else workspace.toURI.toString.stripSuffix("/")
      new DidChangeWatchedFilesRegistrationOptions(
        (List(
          new FileSystemWatcher(Either.forLeft(s"$root/*.sbt")),
          new FileSystemWatcher(Either.forLeft(s"$root/pom.xml")),
          new FileSystemWatcher(Either.forLeft(s"$root/*.sc")),
          new FileSystemWatcher(Either.forLeft(s"$root/*?.gradle")),
          new FileSystemWatcher(Either.forLeft(s"$root/*.gradle.kts")),
          new FileSystemWatcher(Either.forLeft(s"$root/project/*.{scala,sbt}")),
          new FileSystemWatcher(
            Either.forLeft(s"$root/project/project/*.{scala,sbt}")
          ),
          new FileSystemWatcher(
            Either.forLeft(s"$root/project/build.properties")
          ),
          new FileSystemWatcher(
            Either.forLeft(s"$root/.metals/.reports/bloop/*/*")
          ),
          new FileSystemWatcher(Either.forLeft(s"$root/**/.bsp/*.json")),
        ) ++ bazelPaths(root)).asJava
      )
    }

    def bazelPaths(root: String): List[FileSystemWatcher] =
      List(
        new FileSystemWatcher(Either.forLeft(s"$root/**/BUILD")),
        new FileSystemWatcher(Either.forLeft(s"$root/**/BUILD.bazel")),
        new FileSystemWatcher(Either.forLeft(s"$root/WORKSPACE")),
        new FileSystemWatcher(Either.forLeft(s"$root/WORKSPACE.bazel")),
        new FileSystemWatcher(Either.forLeft(s"$root/**/*.bzl")),
        new FileSystemWatcher(Either.forLeft(s"$root/*.bazelproject")),
      )
  }

  object GlobSyntaxConfig {
    def uri = new GlobSyntaxConfig("uri")
    def vscode = new GlobSyntaxConfig("vscode")
    def default =
      new GlobSyntaxConfig(
        System.getProperty("metals.glob-syntax", uri.value)
      )
    def fromString(value: String): Option[GlobSyntaxConfig] =
      value match {
        case "vscode" => Some(vscode)
        case "uri" => Some(uri)
        case _ => None
      }
  }

  object CompilersConfig {
    def apply(
        props: Properties = System.getProperties
    ): PresentationCompilerConfigImpl = {
      PresentationCompilerConfigImpl(
        debug =
          MetalsServerConfig.binaryOption("metals.pc.debug", default = false),
        _parameterHintsCommand =
          Option(props.getProperty("metals.signature-help.command")),
        _completionCommand =
          Option(props.getProperty("metals.completion.command")),
        overrideDefFormat =
          props.getProperty("metals.override-def-format") match {
            case "unicode" => OverrideDefFormat.Unicode
            case "ascii" => OverrideDefFormat.Ascii
            case _ => OverrideDefFormat.Ascii
          },
        isCompletionItemDetailEnabled = MetalsServerConfig.binaryOption(
          "metals.completion-item.detail",
          default = true,
        ),
        isCompletionItemDocumentationEnabled = MetalsServerConfig.binaryOption(
          "metals.completion-item.documentation",
          default = true,
        ),
        isHoverDocumentationEnabled = MetalsServerConfig.binaryOption(
          "metals.hover.documentation",
          default = true,
        ),
        snippetAutoIndent = MetalsServerConfig.binaryOption(
          "metals.snippet-auto-indent",
          default = true,
        ),
        isSignatureHelpDocumentationEnabled = MetalsServerConfig.binaryOption(
          "metals.signature-help.documentation",
          default = true,
        ),
        isCompletionItemResolve = MetalsServerConfig.binaryOption(
          "metals.completion-item.resolve",
          default = true,
        ),
      )
    }
  }

  final case class OrganizeImportsConfig(
      blankLines: BlankLines = BlankLines.Auto,
      coalesceToWildcardImportThreshold: Option[Int] = None,
      expandRelative: Boolean = false,
      groupExplicitlyImportedImplicitsSeparately: Boolean = false,
      groupedImports: GroupedImports = GroupedImports.Explode,
      groups: Seq[String] = Seq(
        "*",
        "re:(javax?|scala)\\.",
      ),
      importSelectorsOrder: ImportSelectorsOrder = ImportSelectorsOrder.Ascii,
      importsOrder: ImportsOrder = ImportsOrder.Ascii,
      preset: Preset = Preset.DEFAULT,
      removeUnused: Boolean = true,
      targetDialect: TargetDialect = TargetDialect.StandardLayout,
  )

  object OrganizeImportsConfig {
    val default: OrganizeImportsConfig = OrganizeImportsConfig()

    implicit val surface: Surface[OrganizeImportsConfig] =
      deriveSurface
    implicit val encoder: ConfEncoder[OrganizeImportsConfig] =
      deriveEncoder
    implicit val decoder: ConfDecoder[OrganizeImportsConfig] =
      deriveDecoder(default)

    val presets: Map[Preset, OrganizeImportsConfig] = Map(
      Preset.DEFAULT -> OrganizeImportsConfig(),
      Preset.INTELLIJ_2020_3 -> OrganizeImportsConfig(
        coalesceToWildcardImportThreshold = Some(5),
        groupedImports = GroupedImports.Merge,
      ),
    )
  }

}

sealed trait ImportsOrder

object ImportsOrder {
  case object Ascii extends ImportsOrder
  case object SymbolsFirst extends ImportsOrder
  case object Keep extends ImportsOrder

  def all: List[ImportsOrder] =
    List(Ascii, SymbolsFirst, Keep)

  implicit def reader: ConfDecoder[ImportsOrder] =
    ReaderUtil.fromMap(all.map(x => x.toString -> x).toMap)

  implicit def writer: ConfEncoder[ImportsOrder] =
    ConfEncoder.instance(v => Conf.Str(v.toString))
}

sealed trait ImportSelectorsOrder

object ImportSelectorsOrder {
  case object Ascii extends ImportSelectorsOrder
  case object SymbolsFirst extends ImportSelectorsOrder
  case object Keep extends ImportSelectorsOrder

  def all: List[ImportSelectorsOrder] =
    List(Ascii, SymbolsFirst, Keep)

  implicit def reader: ConfDecoder[ImportSelectorsOrder] =
    ReaderUtil.fromMap(all.map(x => x.toString -> x).toMap)

  implicit def writer: ConfEncoder[ImportSelectorsOrder] =
    ConfEncoder.instance(v => Conf.Str(v.toString))
}

sealed trait GroupedImports

object GroupedImports {
  case object AggressiveMerge extends GroupedImports
  case object Merge extends GroupedImports
  case object Explode extends GroupedImports
  case object Keep extends GroupedImports

  def all: List[GroupedImports] =
    List(AggressiveMerge, Merge, Explode, Keep)

  implicit def reader: ConfDecoder[GroupedImports] =
    ReaderUtil.fromMap(all.map(x => x.toString -> x).toMap)

  implicit def writer: ConfEncoder[GroupedImports] =
    ConfEncoder.instance(v => Conf.Str(v.toString))
}

sealed trait BlankLines

object BlankLines {
  case object Auto extends BlankLines
  case object Manual extends BlankLines

  def all: List[BlankLines] =
    List(Auto, Manual)

  implicit def reader: ConfDecoder[BlankLines] =
    ReaderUtil.fromMap(all.map(x => x.toString -> x).toMap)

  implicit def writer: ConfEncoder[BlankLines] =
    ConfEncoder.instance(v => Conf.Str(v.toString))
}

sealed trait Preset

object Preset {
  case object DEFAULT extends Preset
  case object INTELLIJ_2020_3 extends Preset

  def all: List[Preset] =
    List(DEFAULT, INTELLIJ_2020_3)

  implicit def reader: ConfDecoder[Preset] =
    ReaderUtil.fromMap(all.map(x => x.toString -> x).toMap)

  implicit def writer: ConfEncoder[Preset] =
    ConfEncoder.instance(v => Conf.Str(v.toString))
}

sealed trait TargetDialect
object TargetDialect {
  case object Auto extends TargetDialect
  case object Scala2 extends TargetDialect
  case object Scala3 extends TargetDialect
  case object StandardLayout extends TargetDialect

  def all: List[TargetDialect] =
    List(Auto, Scala2, Scala3, StandardLayout)

  implicit def reader: ConfDecoder[TargetDialect] =
    ReaderUtil.fromMap(all.map(x => x.toString -> x).toMap)

  implicit def writer: ConfEncoder[TargetDialect] =
    ConfEncoder.instance(v => Conf.Str(v.toString))
}

object ReaderUtil {
  // Poor mans coproduct reader
  def fromMap[T: ClassTag](
      m: Map[String, T],
      additionalMessage: PartialFunction[String, String] = PartialFunction.empty,
  ): ConfDecoder[T] =
    ConfDecoder.instance[T] { case Conf.Str(x) =>
      m.get(x) match {
        case Some(y) =>
          Configured.Ok(y)
        case None =>
          val available = m.keys.mkString(", ")
          val extraMsg = additionalMessage.applyOrElse(x, (_: String) => "")
          val msg =
            s"Unknown input '$x'. Expected one of: $available. $extraMsg"
          Configured.NotOk(ConfError.message(msg))
      }
    }
}

sealed trait ImportMatcher {
  def matches(i: Importer): Int
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
    import scala.meta.XtensionSyntax
    override def matches(i: Importer): Int =
      pattern findPrefixMatchOf i.syntax map (_.end) getOrElse 0
  }

  case class PlainText(pattern: String) extends ImportMatcher {
    import scala.meta.XtensionSyntax
    override def matches(i: Importer): Int =
      if (i.syntax startsWith pattern) pattern.length else 0
  }

  case object * extends ImportMatcher {
    // The wildcard matcher matches nothing. It is special-cased at the end of the import group
    // matching process.
    def matches(importer: Importer): Int = 0
  }

  case object --- extends ImportMatcher {
    // Blank line matchers are pseudo matchers matching nothing. They are special-cased at the end
    // of the import group matching process.
    override def matches(i: Importer): Int = 0
  }
}
