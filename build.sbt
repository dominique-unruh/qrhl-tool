import java.io.PrintWriter
import NativePackagerHelper.*

import scala.sys.process.Process
import java.nio.file.Files
import scala.util.Using

Global / onChangedBuildSource := ReloadOnSourceChanges

lazy val root = (project in file("."))
  .dependsOn(RootProject(file("scala-isabelle")))
  .dependsOn(hashedcomputation)

lazy val hashedcomputation = (project in file("hashedcomputation")).settings(
  scalaVersion := "2.13.16",
  resolvers += Resolver.bintrayIvyRepo("sbt","sbt-plugin-releases"),
  libraryDependencies += "org.log4s" %% "log4s" % "1.8.2",
  // Needed so that logging works in "sbt test"
  libraryDependencies += "org.slf4j" % "slf4j-simple" % "1.7.30" % Test,
//  libraryDependencies += "com.google.guava" % "guava" % "30.0-jre",
  libraryDependencies += "org.jetbrains" % "annotations" % "20.1.0",
  libraryDependencies += "commons-codec" % "commons-codec" % "1.15",
  libraryDependencies += "com.lihaoyi" %% "sourcecode" % "0.1.9",
  libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value,
  libraryDependencies += "com.vladsch.flexmark" % "flexmark-all" % "0.62.2" % Test, // Required by scala-test for HTML output
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % Test,
  libraryDependencies += "org.apache.commons" % "commons-lang3" % "3.12.0" % Test
)
  .dependsOn(RootProject(file("scala-isabelle"))) // Only for access to SharedCleaner. Can remove this if we use a different SharedCleaner



name := "qrhl"

version := Using.resource(scala.io.Source.fromFile("version"))(_.mkString.trim)

scalaVersion := "2.13.16"

scalacOptions += "-deprecation"

//libraryDependencies += "de.unruh" %% "scala-isabelle" % "0.1.0"
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2"
libraryDependencies += "com.vladsch.flexmark" % "flexmark-all" % "0.62.2" % Test // Required by scala-test for HTML output
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % Test
libraryDependencies += "org.rogach" %% "scallop" % "3.5.1"
libraryDependencies += "org.slf4j" % "slf4j-simple" % "1.7.30"
libraryDependencies += "org.jline" % "jline" % "3.16.0"
libraryDependencies += "com.lihaoyi" %% "sourcecode" % "0.1.9"


lazy val makeGITREVISION = taskKey[Unit]("Create GITREVISION")
makeGITREVISION := {
  (baseDirectory.value / "target").mkdir()

  val text = try {
    val builder = new org.eclipse.jgit.storage.file.FileRepositoryBuilder()
    val repo = builder.findGitDir().build()
    val git = new org.eclipse.jgit.api.Git(repo)
    val describe1 = git.describe.setTags(true).setLong(true).setAlways(true).call()
    val describe2 = git.describe.setAlways(true).setAll(true).call()
    val clean = git.status.call().isClean
    s"$describe1\n$describe2${if (clean) "" else "\n(modified working copy)"}"
  } catch {
    case _ : Exception => "Git revision was not known during build time."
  }

  val pr = new PrintWriter(baseDirectory.value / "target" / "GITREVISION")
  pr.print(text)
  pr.close()
}
Compile / managedResources := (Compile / managedResources).dependsOn(makeGITREVISION).value

val isabelleVersion = Files.readString(file("src/main/resources/qrhl/isabellex/isabelleVersion").toPath)
val isabelleHome = file(s"/opt/Isabelle$isabelleVersion")

assembly / mainClass := Some("qrhl.Main")
assembly / assemblyOutputPath := baseDirectory.value / "qrhl.jar"
assembly / test := {}

Universal / javaOptions += "-Dfile.encoding=UTF-8" // This is important when running in ProofGeneral: Communication via stdin/out is done in UTF-8, but by default Java encodes stdin/out according to locale settings

enablePlugins(JavaAppPackaging)

Universal / mappings ++=
  List("proofgeneral.sh", "proofgeneral.ps1", "isabelle.sh", "isabelle.ps1", "README.md", "LICENSE", "qrhl-tool.conf.sample").
    map { f => baseDirectory.value / f -> f }

Universal / mappings ++= {
  val base = baseDirectory.value
  val dirs = base / "isabelle-thys" +++ base / "examples"
  val files = dirs ** ("*.thy" || "*.ML" || "ROOT" || "ROOTS" || "*.qrhl" || "root.tex" || "root.bib" || "empty" || "WHAT_IS_THIS")
  val excluded = List("isabelle-thys/Test.thy", "examples/TestEx.thy", "examples/test.qrhl", "isabelle-thys/Scratch.thy")
  val files2 = files.filter { f => ! excluded.exists(e => f.getPath.endsWith(e)) }
  val excludedPat = List(".*examples/test.*\\.qrhl")
  val files3 = files2.filter { f => ! excludedPat.exists(e => f.getPath.matches(e)) }
  files3 pair relativeTo(base)
}

Universal / mappings += (baseDirectory.value / "doc" / "manual.pdf" -> "manual.pdf")
Universal / mappings += (baseDirectory.value / "target" / "GITREVISION" -> "GITREVISION")

Universal / mappings ++= directory("proofgeneral")

// Without this, updateSbtClassifiers fails (and that breaks Intelli/J support)
resolvers += Resolver.bintrayIvyRepo("sbt","sbt-plugin-releases")
resolvers ++= Resolver.sonatypeOssRepos("snapshots")

// To avoid that several tests simultaneously try to build Isabelle
Test / parallelExecution := false
Test / run / javaOptions += "-Dorg.slf4j.simpleLogger.defaultLogLevel=debug"

test := (Test / test).dependsOn(hashedcomputation / Test / test).value

Universal / javaOptions += "-J-Xss10m"

// This needs to be run manually (because it is slow and rarely needed)
lazy val createIsabelleNames = taskKey[Unit]("(Re)create isabellex/IsabelleNames.scala")
createIsabelleNames := {
  val isabelleCommand = (isabelleHome / "bin/isabelle").toString
  val isabellexDir = ((Compile / scalaSource).value / "qrhl" / "isabellex").toString
  // /opt/Isabelle2021/bin/isabelle export -d . -O src/main/scala/qrhl/isabellex/ -x QRHL.Scala:IsabelleNames.scala -p 1 QRHL-Scala
  Process(List(isabelleCommand, "export", "-d", ".", "-O", isabellexDir, "-x", "QRHL.Scala:IsabelleNames.scala", "-p", "1", "QRHL-Scala")).!!
}

// adapted from https://stackoverflow.com/a/67937807/2646248
assembly / assemblyMergeStrategy := {
  case PathList("module-info.class") => MergeStrategy.discard
  case path if path.endsWith("/module-info.class") => MergeStrategy.discard
  case other =>
    val oldStrategy = (assembly / assemblyMergeStrategy).value
    oldStrategy(other)
}


/*

Steps when releasing a release/release candidate:

 - git checkout release-candidate
 - If this is the first RC for a new release, reset release-candidate to master
 - Edit version in Makefile, build.sbt
 - git commit
 - git tag vXXX (XXX is the version)
 - sbt clean
 - sbt test
 - ./test.sh in pq-fo-verify
 - make qrhl.zip
 - git push
 - wait for github runner tests to succeed
 - git push origin vXXX
 - Create a new release here: https://github.com/dominique-unruh/qrhl-tool/releases/new
 - git cherry master -v
 - git checkout master
 - cherry pick changes from release-candidate branch
 - Edit gh-pages branch
 - Update hksu-verification, edit README, test it, tag it

 */