import java.io.PrintWriter

import NativePackagerHelper._

import scala.sys.process.Process

lazy val root = (project in file("."))
  .dependsOn(RootProject(file("../scala-isabelle")))

name := "qrhl"

version := "0.6alpha"

scalaVersion := "2.13.3"

scalacOptions += "-deprecation"

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.2" % "test"
libraryDependencies += "org.rogach" %% "scallop" % "3.5.1"
// https://mvnrepository.com/artifact/commons-codec/commons-codec
libraryDependencies += "commons-codec" % "commons-codec" % "1.15"
// https://mvnrepository.com/artifact/org.log4s/log4s
libraryDependencies += "org.log4s" %% "log4s" % "1.8.2"
// https://mvnrepository.com/artifact/org.slf4j/slf4j-simple
libraryDependencies += "org.slf4j" % "slf4j-simple" % "1.7.30"
libraryDependencies += "org.jline" % "jline" % "3.16.0"

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

lazy val makeQrhlToolConf = taskKey[Unit]("Create default qrhl-tool.conf")
makeQrhlToolConf := {
  val file = baseDirectory.value / "qrhl-tool.conf"
  if (!file.exists()) {
    println("Creating qrhl-tool.conf")
    val pr = new PrintWriter(file)
    pr.println("# This file is for local development. The distribution will get a copy of qrhl-tool.conf.dist instead.")
    pr.println()
    pr.println("isabelle-home = /opt/Isabelle2019")
    pr.close()
  }
}
managedResources in Compile := (managedResources in Compile).dependsOn(makeQrhlToolConf).value

mainClass in assembly := Some("qrhl.Main")
assemblyOutputPath in assembly := baseDirectory.value / "qrhl.jar"
test in assembly := {}

enablePlugins(JavaAppPackaging)

mappings in Universal ++=
  List("proofgeneral.sh", "run-isabelle.sh", "README.md", "LICENSE").
    map { f => baseDirectory.value / f -> f }

mappings in Universal ++= {
  val base = baseDirectory.value
  val dirs = base / "isabelle-thys" +++ base / "examples"
  val files = dirs ** ("*.thy" || "*.ML" || "ROOT" || "ROOTS" || "*.qrhl" || "root.tex" || "root.bib")
  val excluded = List("isabelle-thys/Test.thy", "examples/TestEx.thy", "examples/test.qrhl", "isabelle-thys/Scratch.thy")
  val files2 = files.filter { f => ! excluded.exists(e => f.getPath.endsWith(e)) }
  val excludedPat = List(".*examples/test.*\\.qrhl")
  val files3 = files2.filter { f => ! excludedPat.exists(e => f.getPath.matches(e)) }
  files3 pair relativeTo(base)
}

mappings in Universal += (baseDirectory.value / "doc" / "manual.pdf" -> "manual.pdf")
mappings in Universal += (baseDirectory.value / "target" / "GITREVISION" -> "GITREVISION")
mappings in Universal += (baseDirectory.value / "qrhl-tool.conf.dist" -> "qrhl-tool.conf")

mappings in Universal ++= directory("PG")

// Without this, updateSbtClassifiers fails (and that breaks Intelli/J support)
resolvers += Resolver.bintrayIvyRepo("sbt","sbt-plugin-releases")

// To avoid that several tests simultaneously try to build Isabelle
parallelExecution in Test := false

javaOptions in Universal += "-J-Xss10m"
