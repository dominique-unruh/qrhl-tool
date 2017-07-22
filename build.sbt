name := "tool"

version := "1.0"

scalaVersion := "2.12.2"

enablePlugins(LibisabellePlugin)

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.6"

isabelleVersions := Seq("2016-1")
isabelleSessions in Compile := Seq("QRHL")
//isabelleSources := Seq(baseDirectory.value / "src/main/isabelle/.libisabelle")

//unmanagedResourceDirectories in Compile += baseDirectory.value / "src/main/isabelle"

libraryDependencies ++= Seq(
  "info.hupel" %% "libisabelle" % "0.8.0", // TODO 0.8.3
  "info.hupel" %% "libisabelle-setup" % "0.8.0",
  "info.hupel" %% "pide-package" % "0.8.0"
)

// https://mvnrepository.com/artifact/org.slf4j/slf4j-simple
libraryDependencies += "org.slf4j" % "slf4j-simple" % "1.7.25" % "test"
libraryDependencies += "org.jline" % "jline" % "3.3.0"
