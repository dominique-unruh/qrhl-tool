import hashedcomputation.filesystem.{FingerprintedDirectorySnapshot, OutdatedSnapshotException, RootsDirectory}
import org.scalatest.funsuite.AnyFunSuite
import qrhl.UserException
import qrhl.isabellex.IsabelleX

import scala.collection.JavaConverters._
import scala.collection.immutable.ListSet
import qrhl.Utils.ListSetUtils
import qrhl.isabellex.IsabelleX.globalIsabelle.intT
import qrhl.toplevel.ToplevelTest.emptyState
import qrhl.toplevel.{DeclareVariableCommand, IncludeCommand, Toplevel, ToplevelTest}

import java.nio.file.{Files, Paths}

object Test0 {
  def main(args: Array[String]): Unit = {
    val root = RootsDirectory()
    var fs = FingerprintedDirectorySnapshot(root)

    var ok = false

    while (!ok) {
      try {
        fs = FingerprintedDirectorySnapshot(root)
        fs.getFile(Paths.get("/tmp/proofs/games.qrhl"))
        ok = true
      } catch {
        case e: OutdatedSnapshotException =>
          println(e)
      }
    }

    val path = Paths.get("/tmp/proofs/games.qrhl")
    print(fs.getFile(path))
  }
}

class Test0 extends AnyFunSuite {
/*
  test ("tmp") {
    val examples = Paths.get("examples")
    val thy = examples.resolve("TMP.thy")
    Files.writeString(thy,
    """theory TMP
      |  imports Main
      |begin
      |
      |lemma testlemma1: "1=1" by simp
      |lemma testlemma2: True by simp
      |lemmas testlemma = testlemma1
      |
      |end
      |""".stripMargin)
    val include = examples.resolve("include.qrhl")
    Files.writeString(include, "isabelle TMP.\n")
//    Files.deleteIfExists(include)
//    Files.writeString(include, "")
    val tl = Toplevel.makeToplevelFromState(emptyState, errorWhenUnfinished = false)

//    tl.execCmd(IncludeCommand("include.qrhl"))
    tl.execCmd("""include "include.qrhl"""")
    println(s"###### CONTEXT: ${System.identityHashCode(tl.state.isabelle.context)}")
    tl.execCmd("lemma True")
    println(s"###### CONTEXT: ${System.identityHashCode(tl.state.isabelle.context)}")

    println("================ RULE TESTLEMMA #1 ==============")
    assertThrows[UserException] {
      tl.execCmd("rule testlemma")
    }
    println(s"###### CONTEXT: ${System.identityHashCode(tl.state.isabelle.context)}")

    Files.writeString(thy,
      """theory TMP
        |  imports Main
        |begin
        |
        |lemma testlemma1: "1=1" by simp
        |lemma testlemma2: True by simp
        |lemmas testlemma = testlemma2
        |
        |end
        |""".stripMargin)
    Thread.sleep(1000)
    println("================ RULE TESTLEMMA #2 ==============")
    println(s"###### CONTEXT: ${System.identityHashCode(tl.state.isabelle.context)}")
    tl.execCmd("print refl")
    println(s"###### CONTEXT: ${System.identityHashCode(tl.state.isabelle.context)}")
    tl.execCmd("rule testlemma")
    println(s"###### CONTEXT: ${System.identityHashCode(tl.state.isabelle.context)}")

  }
*/
}