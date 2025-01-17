package scala.meta.internal.metals

import java.nio.file.Files
import java.util.zip.ZipEntry
import java.util.zip.ZipOutputStream

import scala.meta.internal.metals.doctor.TargetsInfoProvider
import scala.meta.internal.mtags.MtagsEnrichments._
import scala.meta.io.AbsolutePath

case class FolderReportsZippper(
    targetsInfoProvider: TargetsInfoProvider,
    reportContext: StdReportContext,
) {

  def crateReportReadme(): AbsolutePath = {
    val path = AbsolutePath(reportContext.reportsDir.resolve("READ_ME.md"))
    if (Files.notExists(path.toNIO)) {
      path.writeText(
        s"""|Please attach `${StdReportContext.ZIP_FILE_NAME}` to your GitHub issue.
            |Reports zip URI: ${reportContext.reportsDir.resolve(StdReportContext.ZIP_FILE_NAME).toUri}
            |""".stripMargin
      )
    }
    path
  }

  def buildTargetInfo(id: String): String = {
    val text = targetsInfoProvider
      .getTargetsInfoForReports()
      .zipWithIndex
      .map { case (info, ind) =>
        s"""|#### $ind
            |${info.toList.map { case (key, value) => s"$key: $value" }.mkString("\n")}
            |""".stripMargin
      }
      .mkString("\n")
    s"""|### Build targets for folder: $id
        |$text
        |""".stripMargin
  }
}

object ZipReportsProvider {

  def storeBuildTargetsInfo(
      folders: List[FolderReportsZippper]
  ): FileToZip = {
    val text = folders.zipWithIndex
      .map { case (folder, ind) =>
        folder.buildTargetInfo(ind.toString())
      }
      .mkString("\n")
    FileToZip("build-targets-info.md", text.getBytes())
  }

  def zip(folders: List[FolderReportsZippper]): AbsolutePath = {
    val buildTargersFile = storeBuildTargetsInfo(folders)
    zipReports(folders, List(buildTargersFile))
    folders.head.crateReportReadme()
  }

  private def zipReports(
      folders: List[FolderReportsZippper],
      additionalToZip: List[FileToZip],
  ): AbsolutePath = {
    val reportsDir = folders.head.reportContext.reportsDir
    Files.createDirectories(reportsDir)
    val path = AbsolutePath(reportsDir.resolve(StdReportContext.ZIP_FILE_NAME))
    val zipOut = new ZipOutputStream(Files.newOutputStream(path.toNIO))

    for {
      (folder, id) <- folders.zipWithIndex
      reportsProvider <- folder.reportContext.allToZip
      report <- reportsProvider.getReports()
    } {
      val zipEntry = new ZipEntry(s"$id-${report.name}")
      zipOut.putNextEntry(zipEntry)
      zipOut.write(Files.readAllBytes(report.toPath))
    }

    for {
      toZip <- additionalToZip
    } {
      val zipEntry = new ZipEntry(toZip.name)
      zipOut.putNextEntry(zipEntry)
      zipOut.write(toZip.text)
    }

    zipOut.close()

    path
  }
}

case class FileToZip(name: String, text: Array[Byte])
