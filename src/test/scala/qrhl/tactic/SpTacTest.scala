package qrhl.tactic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.toplevel.{TacticCommand, ToplevelTest}

class SpTacTest extends AnyFunSuite {
  test("SpTac well-typed (assign)") {
    val toplevel = ToplevelTest.makeToplevelWithTheory()
    toplevel.run(
      """
        |classical var q : bit.
        |qrhl {top} q <- 0; ~ q <- 0; {top}.
      """.stripMargin)
    toplevel.execCmd(TacticCommand(WpTac(left=1,right=0)))
    toplevel.execCmd(TacticCommand(WpTac(left=0,right=1)))
    val goals = toplevel.state.goal
    println(goals)
    assert(goals.length==1)
    goals.head.checkWelltyped(toplevel.state.isabelle)
  }
}
