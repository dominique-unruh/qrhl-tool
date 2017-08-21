import NativePackagerHelper._

name := "qrhl"

version := "0.1alpha"

scalaVersion := "2.12.2"

enablePlugins(LibisabellePlugin)

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.6"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.3" % "test"
libraryDependencies += "org.rogach" %% "scallop" % "3.0.3"

isabelleVersions := Seq("2016-1")
isabelleSessions in Compile := Seq("QRHL")
//isabelleSources := Seq(baseDirectory.value / "src/main/isabelle/.libisabelle")

//unmanagedResourceDirectories in Compile += baseDirectory.value / "src/main/isabelle"

libraryDependencies ++= { val version = "0.9.0"; Seq(
  "info.hupel" %% "libisabelle" % version,
  "info.hupel" %% "libisabelle-setup" % version,
  "info.hupel" %% "pide-package" % version
) }

// https://mvnrepository.com/artifact/org.slf4j/slf4j-simple
libraryDependencies += "org.slf4j" % "slf4j-simple" % "1.7.25"
libraryDependencies += "org.jline" % "jline" % "3.3.0"



//import sbtassembly.AssemblyPlugin.defaultShellScript
//assemblyOption in assembly := (assemblyOption in assembly).value.copy(prependShellScript = Some(defaultShellScript))
mainClass in assembly := Some("qrhl.Main")
//assemblyJarName in assembly := "qrhl.jar"
assemblyOutputPath in assembly := baseDirectory.value / "qrhl.jar"
test in assembly := {}

enablePlugins(JavaAppPackaging)
mappings in Universal ++= Seq(
    "proofgeneral.sh", "proofgeneral.bat", "run-isabelle.sh", "run-isabelle.bat",
    "prg-enc-rorcpa.qrhl", "prg-enc-indcpa.qrhl", "PrgEnc.thy", "teleport.qrhl", "README.md"
  ).map { f =>
  baseDirectory.value / f -> f
}
//javaOptions in Universal += "-Dfile.encoding=UTF-8" // Doesn't seem to work
mappings in Universal ++= directory("PG")


//lazy val mkBinary = taskKey[Unit]("Packages the binary")
//
//mkBinary := {
//  assembly.value
//}