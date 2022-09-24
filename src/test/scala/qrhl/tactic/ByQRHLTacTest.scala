package qrhl.tactic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.QRHLSubgoal
import qrhl.logic.{Block, Call}
import qrhl.toplevel.{GoalCommand, Toplevel, ToplevelTest}

class ByQRHLTacTest extends AnyFunSuite {
  test("works with Pr") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : bit")
    tl.execCmd("ambient var rho : program_state")
    tl.execCmd("program p := { skip; }")
    tl.execCmd("lemma xxx: Pr[x=1:p(rho)] <= Pr[x=1:p(rho)]")
    tl.execCmd("byqrhl")
    assert(tl.state.goal.length == 1)
    tl.state.goal.head.checkWelltyped(tl.state.isabelle)
  }

  test("lhs is 1") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : bit")
    tl.execCmd("ambient var rho : program_state")
    tl.execCmd("program p := { skip; }")
    tl.execCmd("lemma xxx: Pr[x=1:p(rho)] <= 1")
    tl.execCmd("byqrhl")

    tl.state.goal.head.checkWelltyped(tl.state.isabelle)
    assert(tl.state.goal.length == 1)
    val subgoal = tl.state.goal.head.asInstanceOf[QRHLSubgoal]

    println(subgoal.right.getClass)
    println(subgoal.right.statements)

    assert(subgoal.right == Block.empty)
    assert(subgoal.post.toString == "ℭ\uD835\uDD29\uD835\uDD1E[x1 = 1 ⟶ True]")
  }

  test("denotational equivalence") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : bit")
    tl.execCmd("quantum var q : bit")
    tl.execCmd("program p1 := { x <- x+1; }")
    tl.execCmd("program p2 := { on q apply hadamard; }")
    tl.execCmd("lemma xxx: denotation p1 = denotation p2")
    tl.execCmd("byqrhl")

    tl.state.goal.head.checkWelltyped(tl.state.isabelle)
    assert(tl.state.goal.length == 1)
    val subgoal = tl.state.goal.head.asInstanceOf[QRHLSubgoal]

    println(subgoal.right.getClass)
    println(subgoal.right.statements)

    assert(subgoal.pre.toString == "ℭ\uD835\uDD29\uD835\uDD1E[x1 = x2] ⊓ ⟦q1⟧ ≡\uD835\uDD2E ⟦q2⟧")
    assert(subgoal.post == subgoal.pre)
    assert(subgoal.left == Block(Call("p1")))
    assert(subgoal.right == Block(Call("p2")))
  }
}
