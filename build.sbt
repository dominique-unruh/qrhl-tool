import java.nio.file.Files

import NativePackagerHelper._
import org.apache.commons.compress.archivers.tar.TarArchiveInputStream
import sbt.Keys.update
import sbt.io.Using

import scala.collection.mutable.ListBuffer
import scala.sys.process.Process

name := "qrhl"

version := "0.3alpha"

scalaVersion := "2.12.6"

scalacOptions += "-deprecation"

//enablePlugins(LibisabellePlugin)

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.1"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5" % "test"
libraryDependencies += "org.rogach" %% "scallop" % "3.1.2"

//isabelleSessions in Compile := Seq("QRHL")
//isabelleSourceFilter := (- ".*") && (- "*~")
//isabelleSourceFilter := (- "*") // effectively disables the collection of Isabelle sources by sbt-libisabelle

libraryDependencies ++= { val version = "1.0.0"; Seq(
  "info.hupel" %% "libisabelle" % version,
  "info.hupel" %% "libisabelle-setup" % version,
  "info.hupel" %% "pide-package" % version
) }

def extractJar(update : UpdateReport, name : String, target : File) = {
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
managedResources in Compile := (managedResources in Compile).dependsOn(extractLibisabelleProtocol).value

extractLibisabelleProtocol := {
  val up = (update in Compile).value
  extractJar(up, "libisabelle_", baseDirectory.value / libisabelleExtractPath)
  extractJar(up, "classy-", baseDirectory.value / classyExtractPath)
}


//val afpUrl = "https://downloads.sourceforge.net/project/afp/afp-Isabelle2017/afp-2018-01-12.tar.gz"
val afpUrl = "https://bitbucket.org/isa-afp/afp-2018/get/015ec037f36d.tar.gz"
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
  List("proofgeneral.sh", "proofgeneral.bat", "run-isabelle.sh", "run-isabelle.bat", "README.md").
    map { f => baseDirectory.value / f -> f }

mappings in Universal ++= {
  val base = baseDirectory.value
  val dirs = base / "isabelle-thys" +++ base / "examples"
  val files = dirs ** ("*.thy" || "*.ML" || "ROOT" || "ROOTS" || "*.qrhl")
  files pair relativeTo(base)
}

mappings in Universal ++= {
  val base = baseDirectory.value
  val files = base / "isabelle-afp" * (- ("*~" || "link-afp.sh")) ** (- "*~")
//  println("FILES",files)
  files pair relativeTo(base)
}

mappings in Universal += (baseDirectory.value / ".." / "queasycrypt" / "trunk" / "manual.pdf" -> "manual.pdf")

mappings in Universal ++= directory("PG")

//javaOptions in Universal += "-Dfile.encoding=UTF-8" // Doesn't seem to work

// Without this, updateSbtClassifiers fails (and that breaks Intelli/J support)
resolvers += Resolver.bintrayIvyRepo("sbt","sbt-plugin-releases")

// To avoid that several tests simultaneously try to download Isabelle
parallelExecution in Test := false
