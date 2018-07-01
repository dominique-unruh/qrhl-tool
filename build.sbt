import java.nio.file.Files

import NativePackagerHelper._
import org.apache.commons.compress.archivers.tar.TarArchiveInputStream
import sbt.io.Using

import scala.sys.process.Process

name := "qrhl"

version := "0.3alpha"

scalaVersion := "2.12.5"

scalacOptions += "-deprecation"

enablePlugins(LibisabellePlugin)

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.1"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5" % "test"
libraryDependencies += "org.rogach" %% "scallop" % "3.1.2"

isabelleVersions := Seq(Version.Stable("2018-RC0")) // TODO 2018
isabelleSessions in Compile := Seq("QRHL")
isabelleSourceFilter := (- ".*") && (- "*~")

libraryDependencies ++= { val version = "1.0.0-RC1"; Seq( // TODO 2018
  "info.hupel" %% "libisabelle" % version,
  "info.hupel" %% "libisabelle-setup" % version,
  "info.hupel" %% "pide-package" % version
) }

//val afpUrl = "https://downloads.sourceforge.net/project/afp/afp-Isabelle2017/afp-2018-01-12.tar.gz"
val afpUrl = "https://bitbucket.org/isa-afp/afp-devel/get/7f9c8aca53e8.tar.gz" // TODO 2018
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
mappings in Universal ++= Seq(
    "proofgeneral.sh", "proofgeneral.bat", "run-isabelle.sh", "run-isabelle.bat",
    "examples/prg-enc-rorcpa.qrhl", "examples/prg-enc-indcpa.qrhl", "examples/PrgEnc.thy", "README.md",
    "examples/equality.qrhl", "examples/example.qrhl", "examples/Example.thy", "examples/rnd.qrhl",
    "examples/teleport.qrhl", "examples/Teleport.thy", "examples/teleport-terse.qrhl", "examples/Teleport_Terse.thy",
    "examples/Code_Example.thy", "examples/chsh.ec", "examples/Chsh.thy"
  ).map { f => baseDirectory.value / f -> f }
  
mappings in Universal ++= Seq(
	 baseDirectory.value / ".." / "manual.pdf" -> "manual.pdf")
	 

//javaOptions in Universal += "-Dfile.encoding=UTF-8" // Doesn't seem to work
mappings in Universal ++= directory("PG")


// Without this, updateSbtClassifiers fails (and this breaks Intelli/J support)
resolvers += Resolver.bintrayIvyRepo("sbt","sbt-plugin-releases")

// To avoid that several tests simultaneously try to download Isabelle
parallelExecution in Test := false
