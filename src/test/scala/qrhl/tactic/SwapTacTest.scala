package qrhl.tactic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.toplevel.{TacticCommand, ToplevelTest}
import ToplevelTest.output
import qrhl.{DenotationalEqSubgoal, QRHLSubgoal}

class SwapTacTest extends AnyFunSuite {
  test("subprogram") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.run(
      """classical var b : bit.
        |classical var x : int.
        |classical var y : int.
        |quantum var Q : bit.
        |qrhl {undefined} b <- measure Q with computational_basis; b <- measure Q with computational_basis; x <- y+1; ~ skip; {undefined}.
        |""".stripMargin)
    val cmd = tl.state.parseCommand("swap left 2 1 subprograms second: { b <- measure Q with computational_basis; }")
    println(cmd)
    val TacticCommand(tactic : SwapTac) = cmd
    println(tactic)
    val subgoals = tactic.apply(tl.state, tl.state.goal.head)
    println(subgoals)
    assert(subgoals.length == 2)
    val List(deneq : DenotationalEqSubgoal, qrhl : QRHLSubgoal) = subgoals
    deneq.checkWelltyped(tl.state.isabelle)
    qrhl.checkWelltyped(tl.state.isabelle)
    assert(deneq.left.toString == "{ b <- measure Q with computational_basis; b <- measure Q with computational_basis; }")
    assert(deneq.right.toString == "{ b <- measure Q with computational_basis; b <- measure Q with computational_basis; }")
    assert(qrhl.left.toString == "{ b <- measure Q with computational_basis; x <- y + 1; b <- measure Q with computational_basis; }")
    assert(qrhl.right.toString == "{}")
  }
}
