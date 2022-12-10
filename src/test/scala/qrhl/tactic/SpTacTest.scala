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
    toplevel.execCmd(TacticCommand(SpTac(left = 1, right = 0)))
    val goals = toplevel.state.goal
    println(goals)
    assert(goals.length == 1)
    for (goal <- goals)
      goal.checkWelltyped(toplevel.state.isabelle)
  }

  test("SpTac well-typed (qinit)") {
    val toplevel = ToplevelTest.makeToplevelWithTheory()
    toplevel.run(
      """
      |quantum var q : bit.
      |qrhl {top} q <q ket 0; ~ q <q ket 1; {top}.
      """.stripMargin)
    toplevel.execCmd(TacticCommand(SpTac(left = 1, right = 0)))
    val goals = toplevel.state.goal
    println(goals)
    assert(goals.length == 3)
    for (goal <- goals)
      goal.checkWelltyped(toplevel.state.isabelle)
  }
}
