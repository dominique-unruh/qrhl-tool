import NativePackagerHelper._

name := "qrhl"

version := "0.1alpha"

scalaVersion := "2.12.4"

enablePlugins(LibisabellePlugin)

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.6"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.3" % "test" // TODO 3.0.4
libraryDependencies += "org.rogach" %% "scallop" % "3.1.1"

isabelleVersions := Seq(Version.Stable("2017"))
isabelleSessions in Compile := Seq("QRHL")
//isabelleSources := Seq(baseDirectory.value / "src/main/isabelle")

//unmanagedResourceDirectories in Compile += baseDirectory.value / "src/main/isabelle"

libraryDependencies ++= { val version = "0.9.2"; Seq(
  "info.hupel" %% "libisabelle" % version,
  "info.hupel" %% "libisabelle-setup" % version,
  "info.hupel" %% "pide-package" % version
) }
//libraryDependencies += "info.hupel.afp" % "afp-2017" % "1.1.20171130"

val afpUrl = "https://downloads.sourceforge.net/project/afp/afp-Isabelle2017/afp-2017-11-23.tar.gz"

lazy val downloadAFP = taskKey[Unit]("Download the AFP and extract it to target/downloads/afp")
downloadAFP := {
  val path = "target/downloads/afp"
  if(java.nio.file.Files.notExists(new File(path).toPath())) {
    println("Path does not exist, downloading...")
    IO.unzipURL(new URL(afpUrl), new File(path))
  } else {
    println("Path exists, no need to download.")
  }
}


// https://mvnrepository.com/artifact/org.slf4j/slf4j-simple
libraryDependencies += "org.slf4j" % "slf4j-simple" % "1.7.25"
libraryDependencies += "org.jline" % "jline" % "3.5.1"

//import sbtassembly.AssemblyPlugin.defaultShellScript
//assemblyOption in assembly := (assemblyOption in assembly).value.copy(prependShellScript = Some(defaultShellScript))
mainClass in assembly := Some("qrhl.Main")
//assemblyJarName in assembly := "qrhl.jar"
assemblyOutputPath in assembly := baseDirectory.value / "qrhl.jar"
test in assembly := {}

enablePlugins(JavaAppPackaging)
mappings in Universal ++= Seq(
    "proofgeneral.sh", "proofgeneral.bat", "run-isabelle.sh", "run-isabelle.bat",
    "prg-enc-rorcpa.qrhl", "prg-enc-indcpa.qrhl", "PrgEnc.thy", "README.md",
    "equality.qrhl", "example.qrhl", "Example.thy", "rnd.qrhl"
  ).map { f =>
  baseDirectory.value / f -> f
}
//javaOptions in Universal += "-Dfile.encoding=UTF-8" // Doesn't seem to work
mappings in Universal ++= directory("PG")


// Without this, updateSbtClassifiers fails (and this breaks Intelli/J support)
resolvers += Resolver.bintrayIvyRepo("sbt","sbt-plugin-releases")

// To avoid that several tests simultaneously try to download Isabelle
parallelExecution in Test := false
