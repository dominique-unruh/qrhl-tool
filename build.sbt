import java.io.PrintWriter
import java.nio.file.Files

import NativePackagerHelper._
import org.apache.commons.compress.archivers.tar.TarArchiveInputStream
import sbt.Keys.update
import sbt.io.Using

import scala.collection.mutable.ListBuffer
import scala.sys.process.Process

name := "qrhl"

version := "0.5"

scalaVersion := "2.12.11"

scalacOptions += "-deprecation"

//enablePlugins(LibisabellePlugin)

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.1"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5" % "test"
libraryDependencies += "org.rogach" %% "scallop" % "3.1.2"

//isabelleSessions in Compile := Seq("QRHL")
//isabelleSourceFilter := (- ".*") && (- "*~")
//isabelleSourceFilter := (- "*") // effectively disables the collection of Isabelle sources by sbt-libisabelle

libraryDependencies += "info.hupel" % "multi-isabelle" % "0.1.4" // TODO remove

libraryDependencies ++= { val version = "1.1.0-RC3"; Seq(
  "info.hupel" %% "libisabelle" % version,
  "info.hupel" %% "libisabelle-setup" % version,
  "info.hupel" %% "pide-package" % version
) }

def extractJar(update : UpdateReport, name : String, target : File): Unit = {
  val jar = update
    .select(configurationFilter("compile"))
    .filter(_.name.startsWith(name))
    .filter(_.name.endsWith(".jar"))
    .head
  IO.unzip(jar,target)
  ()
}

assemblyMergeStrategy in assembly := {
  case PathList(ps @ _*) if ps.last == ".files" => MergeStrategy.discard
  case x => (assemblyMergeStrategy in assembly).value(x)
}

lazy val extractLibisabelleProtocol = taskKey[Unit]("Extract libisabelle Protocol session")
val libisabelleExtractPath = "target/downloads/libisabelle"
val classyExtractPath = "target/downloads/classy"
val multiIsabelleExtractPath = "target/downloads/multi-isabelle"
managedResources in Compile := (managedResources in Compile).dependsOn(extractLibisabelleProtocol).value

extractLibisabelleProtocol := {
  val up = (update in Compile).value
  extractJar(up, "libisabelle_", baseDirectory.value / libisabelleExtractPath)
  extractJar(up, "classy-", baseDirectory.value / classyExtractPath)
  extractJar(up, "multi-isabelle-", baseDirectory.value / multiIsabelleExtractPath)
}

//val afpUrl = "https://downloads.sourceforge.net/project/afp/afp-Isabelle2017/afp-2018-01-12.tar.gz"
//val afpUrl = "https://bitbucket.org/isa-afp/afp-devel/get/7c585d0056e3.tar.gz"
val afpUrl = "https://isabelle.sketis.net/repos/afp-2019/archive/1a623915bf3f.tar.gz"
val afpExtractPath = "target/downloads/afp"

lazy val downloadAFP = taskKey[Unit]("Download the AFP")
managedResources in Compile := (managedResources in Compile).dependsOn(downloadAFP).value

downloadAFP := {
  import scala.sys.process._

  val extractPath = baseDirectory.value / afpExtractPath

  if (!extractPath.exists()) {
    println("Downloading AFP.")
    try {
      extractPath.mkdirs()
      print ( ( new URL(afpUrl) #> Process(List("tar", "xz", "--strip-components=1"), cwd = extractPath) ).!! )
    } catch {
      case e : Throwable =>
        print("Removing "+extractPath)
        IO.delete(extractPath)
        throw e
    }
  }
}

lazy val extractIsabelle = taskKey[Unit]("Extract Isabelle distribution directory")
managedResources in Compile := (managedResources in Compile).dependsOn(extractIsabelle).value
extractIsabelle := {
  import scala.sys.process._
  val extractPath = baseDirectory.value / "Isabelle2019-RC4"
  if (!extractPath.exists) {
    println("Extracting Isabelle")
    try {
      print((Process(List("tar", "xf", "Isabelle2019-RC4-linux-no-heaps.tar.xz"), cwd = baseDirectory.value)).!!)
    } catch {
      case e: Throwable =>
        print("Removing " + extractPath)
        IO.delete(extractPath)
        throw e
    }
  }
}

val pgUrl = "https://github.com/ProofGeneral/PG/archive/a7894708e924be6c3968054988b50da7f6c02c6b.tar.gz"
val pgPatch = "src/proofgeneral/proof-site.el.patch"
val pgExtractPath = "target/downloads/PG"
lazy val downloadPG = taskKey[Unit]("Download ProofGeneral")
managedResources in Compile := (managedResources in Compile).dependsOn(downloadPG).value

downloadPG := {
  import scala.sys.process._
  val extractPath = baseDirectory.value / pgExtractPath

  if (!extractPath.exists()) {
    println("Downloading ProofGeneral.")
    try {
      extractPath.mkdirs()
      print ( ( new URL(pgUrl) #> Process(List("tar", "xz", "--strip-components=1"), cwd = extractPath) ).!! )
      print ( ( (baseDirectory.value / pgPatch) #> Process(List("patch", "generic/proof-site.el"), cwd = extractPath) ).!! )
      print ( ( (baseDirectory.value / pgPatch) #> Process(List("cp", "-a", "src/proofgeneral", pgExtractPath + "/qrhl"), cwd = baseDirectory.value) ).!! )
    } catch {
      case e : Throwable =>
        print("Removing "+extractPath)
        IO.delete(extractPath)
        throw e
    }
  }
}


lazy val makeGITREVISION = taskKey[Unit]("Create GITREVISION")
makeGITREVISION := {
  (baseDirectory.value / "target").mkdir()
  if ((baseDirectory.value / ".git").exists())
    Process(List("bash","-c","( git describe --tags --long --always --dirty --broken && git describe --always --all ) > target/GITREVISION")).!!
  else {
    val pr = new PrintWriter(baseDirectory.value / "target" / "GITREVISION")
    pr.println("Not built from a GIT worktree.")
    pr.close()
  }
}
managedResources in Compile := (managedResources in Compile).dependsOn(makeGITREVISION).value

// https://mvnrepository.com/artifact/org.slf4j/slf4j-simple
libraryDependencies += "org.slf4j" % "slf4j-simple" % "1.7.25"
libraryDependencies += "org.jline" % "jline" % "3.6.2"

//import sbtassembly.AssemblyPlugin.defaultShellScript
//assemblyOption in assembly := (assemblyOption in assembly).value.copy(prependShellScript = Some(defaultShellScript))
mainClass in assembly := Some("qrhl.Main")
//assemblyJarName in assembly := "qrhl.jar"
assemblyOutputPath in assembly := baseDirectory.value / "qrhl.jar"
test in assembly := {}

enablePlugins(JavaAppPackaging)

mappings in Universal ++=
  List("proofgeneral.sh", "run-isabelle.sh", "README.md", "LICENSE").
    map { f => baseDirectory.value / f -> f }

mappings in Universal ++= {
  val base = baseDirectory.value
  val dirs = base / "isabelle-thys" +++ base / "examples"
  val Isabelle_files = (base / "Isabelle2019-RC4" allPaths)
  val files = dirs ** ("*.thy" || "*.ML" || "ROOT" || "ROOTS" || "*.qrhl" || "root.tex" || "root.bib") +++ Isabelle_files
  val excluded = List("isabelle-thys/Test.thy", "examples/TestEx.thy", "examples/test.qrhl", "isabelle-thys/Scratch.thy", "Isabelle2019-RC4/contrib/polyml-5.8/src/compile")
  val files2 = files.filter { f => ! excluded.exists(e => f.getPath.endsWith(e)) }
  val excludedPat = List(".*examples/test.*\\.qrhl")
  val files3 = files2.filter { f => ! excludedPat.exists(e => f.getPath.matches(e)) }
  files3 pair relativeTo(base)
}

mappings in Universal ++= {
  val base = baseDirectory.value
  val files = base / "isabelle-afp" * (- ("*~" || "link-afp.sh")) ** (- "*~")
//  println("FILES",files)
  files pair relativeTo(base)
}

mappings in Universal += (baseDirectory.value / "doc" / "manual.pdf" -> "manual.pdf")
mappings in Universal += (baseDirectory.value / "target" / "GITREVISION" -> "GITREVISION")

mappings in Universal ++= directory("PG")

//javaOptions in Universal += "-Dfile.encoding=UTF-8" // Doesn't seem to work

// Without this, updateSbtClassifiers fails (and that breaks Intelli/J support)
resolvers += Resolver.bintrayIvyRepo("sbt","sbt-plugin-releases")

// To avoid that several tests simultaneously try to download Isabelle
parallelExecution in Test := false

javaOptions in Universal += "-J-Xss10m"
