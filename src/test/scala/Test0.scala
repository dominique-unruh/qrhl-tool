import org.scalatest.funsuite.AnyFunSuite
import qrhl.isabellex.IsabelleX

import scala.collection.JavaConverters._
import scala.collection.immutable.ListSet
import qrhl.Utils.ListSetUtils
import qrhl.isabellex.IsabelleX.globalIsabelle.intT
import qrhl.toplevel.{DeclareVariableCommand, ToplevelTest}

object Test0 {
  def main(args: Array[String]): Unit = {
    val l1 = ListSet(1,2,3)
    val l2 = ListSet(4,5,6)
    for (x <- l2) println(x)
    val l = l1 +++ l2
    println(l)
    println(ListSet.empty +++ l2)
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