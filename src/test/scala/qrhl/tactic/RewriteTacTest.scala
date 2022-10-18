package qrhl.tactic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.{DenotationalEqSubgoal, QRHLSubgoal}
import qrhl.logic.{Assign, Block, Call}
import qrhl.tactic.RewriteTac.{All, Code, Subseq}
import qrhl.toplevel.{TacticCommand, ToplevelTest}

import java.io.{PrintStream, PrintWriter}

class RewriteTacTest extends AnyFunSuite {
  test("rewrite lines by code") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.run(
      """classical var x : int.
        |classical var y : int.
        |program P := { x <- 3; y <- 2; }.
        |qrhl {Cla[x1 = 0]} x <- 1; y <- 2; x <-3; ~ skip; {Cla[x1 = 1]}.
        |""".stripMargin)
    val tactic = RewriteTac(
      RewriteTac.Subseq(left = true, start = 2, end = 3),
      RewriteTac.Code(Block(Call("P")))
    )
    implicit val output: PrintWriter = new PrintWriter(System.out)
    val subgoals = tactic.apply(tl.state, tl.state.goal.head)
    println(subgoals)

    assert(subgoals.length == 2)
    val Seq(subgoal1 : DenotationalEqSubgoal, subgoal2 : QRHLSubgoal) = subgoals

    assert(subgoal1.left.toString == "{ y <- 2; x <- 3; }")
    assert(subgoal1.right.toString == "call P;")
    assert(subgoal1.assumptions.isEmpty)

    assert(subgoal2.left.toString == "{ x <- 1; call P; }")
    assert(subgoal2.right.toString == "{}")
    assert(subgoal2.pre.toString == "ℭ\uD835\uDD29\uD835\uDD1E[x1 = 0]")
    assert(subgoal2.post.toString == "ℭ\uD835\uDD29\uD835\uDD1E[x1 = 1]")
    assert(subgoal2.assumptions.isEmpty)
  }

  test("rewrite all by lines") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.run(
      """classical var x : int.
        |classical var y : int.
        |qrhl {Cla[x1 = 0]} x <- 1; y <- 2; x <-3; ~ x <- 99; {Cla[x1 = 1]}.
        |""".stripMargin)
    val tactic = RewriteTac(
      All(left = false),
      RewriteTac.Subseq(left = true, 1, 2)
    )
    implicit val output: PrintWriter = new PrintWriter(System.out)
    val subgoals = tactic.apply(tl.state, tl.state.goal.head)
    println(subgoals)

    assert(subgoals.length == 2)
    val Seq(subgoal1: DenotationalEqSubgoal, subgoal2: QRHLSubgoal) = subgoals

    assert(subgoal1.left.toString == "x <- 99;")
    assert(subgoal1.right.toString == "{ x <- 1; y <- 2; }")
    assert(subgoal1.assumptions.isEmpty)

    assert(subgoal2.left.toString == "{ x <- 1; y <- 2; x <- 3; }")
    assert(subgoal2.right.toString == "{ x <- 1; x <- 2;}")
    assert(subgoal2.pre.toString == "ℭ\uD835\uDD29\uD835\uDD1E[x1 = 0]")
    assert(subgoal2.post.toString == "ℭ\uD835\uDD29\uD835\uDD1E[x1 = 1]")
    assert(subgoal2.assumptions.isEmpty)
  }

  test("parse") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    assert(tl.state.parseCommand("rewrite left -> right") ==
      TacticCommand(RewriteTac(All(true), All(false))))
    assert(tl.state.parseCommand("rewrite left 2-3 -> { }") ==
      TacticCommand(RewriteTac(Subseq(left = true, 2, 3), Code(Block.empty))))
    assert(tl.state.parseCommand("rewrite left 2-3 -> right 2-3") ==
      TacticCommand(RewriteTac(Subseq(left = true, 2, 3), Subseq(left = false, 2, 3))))
  }
}
