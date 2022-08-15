import java.io.PrintWriter
import NativePackagerHelper._

import scala.sys.process.Process

Global / onChangedBuildSource := ReloadOnSourceChanges

lazy val root = (project in file("."))
  .dependsOn(RootProject(file("scala-isabelle")))
  .dependsOn(hashedcomputation)

lazy val hashedcomputation = (project in file("hashedcomputation")).settings(
  scalaVersion := "2.13.3",
  resolvers += Resolver.bintrayIvyRepo("sbt","sbt-plugin-releases"),
  // https://mvnrepository.com/artifact/org.log4s/log4s
  libraryDependencies += "org.log4s" %% "log4s" % "1.8.2",
  // Needed so that logging works in "sbt test"
  libraryDependencies += "org.slf4j" % "slf4j-simple" % "1.7.30" % Test,
//  libraryDependencies += "com.google.guava" % "guava" % "30.0-jre",
  libraryDependencies += "org.jetbrains" % "annotations" % "20.1.0",
  // https://mvnrepository.com/artifact/commons-codec/commons-codec
  libraryDependencies += "commons-codec" % "commons-codec" % "1.15",
  libraryDependencies += "com.lihaoyi" %% "sourcecode" % "0.1.9",
  libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value,
  libraryDependencies += "com.vladsch.flexmark" % "flexmark-all" % "0.62.2" % Test, // Required by scala-test for HTML output
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % Test,
  libraryDependencies += "org.apache.commons" % "commons-lang3" % "3.12.0" % Test
)
  .dependsOn(RootProject(file("scala-isabelle"))) // Only for access to SharedCleaner. Can remove this if we use a different SharedCleaner



name := "qrhl"

version := "snapshot"

scalaVersion := "2.13.3"

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
managedResources in Compile := (managedResources in Compile).dependsOn(makeGITREVISION).value

val isabelleHome = file("/opt/Isabelle2021-1")

mainClass in assembly := Some("qrhl.Main")
assemblyOutputPath in assembly := baseDirectory.value / "qrhl.jar"
test in assembly := {}

javaOptions in Universal += "-Dfile.encoding=UTF-8" // This is important when running in ProofGeneral: Communication via stdin/out is done in UTF-8, but by default Java encodes stdin/out according to locale settings

enablePlugins(JavaAppPackaging)

mappings in Universal ++=
  List("proofgeneral.sh", /*"proofgeneral.bat",*/ "run-isabelle.sh", "run-isabelle.bat", "README.md", "LICENSE", "qrhl-tool.conf.sample").
    map { f => baseDirectory.value / f -> f }

mappings in Universal ++= {
  val base = baseDirectory.value
  val dirs = base / "isabelle-thys" +++ base / "examples"
  val files = dirs ** ("*.thy" || "*.ML" || "ROOT" || "ROOTS" || "*.qrhl" || "root.tex" || "root.bib" || "empty" || "WHAT_IS_THIS")
  val excluded = List("isabelle-thys/Test.thy", "examples/TestEx.thy", "examples/test.qrhl", "isabelle-thys/Scratch.thy")
  val files2 = files.filter { f => ! excluded.exists(e => f.getPath.endsWith(e)) }
  val excludedPat = List(".*examples/test.*\\.qrhl")
  val files3 = files2.filter { f => ! excludedPat.exists(e => f.getPath.matches(e)) }
  files3 pair relativeTo(base)
}

mappings in Universal += (baseDirectory.value / "doc" / "manual.pdf" -> "manual.pdf")
mappings in Universal += (baseDirectory.value / "target" / "GITREVISION" -> "GITREVISION")

mappings in Universal ++= directory("proofgeneral")

// Without this, updateSbtClassifiers fails (and that breaks Intelli/J support)
resolvers += Resolver.bintrayIvyRepo("sbt","sbt-plugin-releases")
resolvers += Resolver.sonatypeRepo("snapshots")

// To avoid that several tests simultaneously try to build Isabelle
parallelExecution in Test := false
Test / run / javaOptions += "-Dorg.slf4j.simpleLogger.defaultLogLevel=debug"

test := (Test / test).dependsOn(hashedcomputation / Test / test).value

javaOptions in Universal += "-J-Xss10m"

// This needs to be run manually (because it is slow and rarely needed)
lazy val createIsabelleNames = taskKey[Unit]("(Re)create isabellex/IsabelleNames.scala")
createIsabelleNames := {
  val isabelleCommand = (isabelleHome / "bin/isabelle").toString
  val isabellexDir = (scalaSource.in(Compile).value / "qrhl" / "isabellex").toString
  // /opt/Isabelle2021/bin/isabelle export -d . -O src/main/scala/qrhl/isabellex/ -x QRHL.Scala:IsabelleNames.scala -p 1 QRHL-Scala
  Process(List(isabelleCommand, "export", "-d", ".", "-O", isabellexDir, "-x", "QRHL.Scala:IsabelleNames.scala", "-p", "1", "QRHL-Scala")).!!
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
 - git checkout master
 - cherry pick changes from release-candidate branch
 - Edit gh-pages branch
 - Update hksu-verification, edit README, test it, tag it

 */