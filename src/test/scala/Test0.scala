import hashedcomputation.filesystem.{FingerprintedDirectorySnapshot, OutdatedSnapshotException, RootsDirectory}
import org.scalatest.funsuite.AnyFunSuite
import qrhl.isabellex.IsabelleX

import scala.collection.JavaConverters._
import scala.collection.immutable.ListSet
import qrhl.Utils.ListSetUtils
import qrhl.isabellex.IsabelleX.globalIsabelle.intT
import qrhl.toplevel.{DeclareVariableCommand, ToplevelTest}

import java.nio.file.Paths

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
  test("tmp") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    try {
      tl.execCmd("quantum var rho : program_state")
    } catch {
      case e: Throwable => println(e)
    }
    println("\n\n\n\n\n RETRY ***********\n\n\n")
//    val state2 = tl.state.declareAmbientVariable("x", intT)
//    tl.execCmd("ambient var x : int")
    tl.execCmd(DeclareVariableCommand("x", intT, true, false))
  }
*/
}