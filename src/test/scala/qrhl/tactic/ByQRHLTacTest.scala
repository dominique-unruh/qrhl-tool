package qrhl.tactic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.QRHLSubgoal
import qrhl.logic.Block
import qrhl.toplevel.{GoalCommand, Toplevel, ToplevelTest}

class ByQRHLTacTest extends AnyFunSuite {
  test("works with Pr") {
    val tl = Toplevel.makeToplevelWithTheory()
    tl.execCmd("classical var x : bit")
    tl.execCmd("ambient var rho : program_state")
    tl.execCmd("program p := { skip; }")
    tl.execCmd("lemma xxx: Pr[x=1:p(rho)] <= Pr[x=1:p(rho)]")
    tl.execCmd("byqrhl")
    assert(tl.state.goal.length == 1)
    tl.state.goal.head.checkWelltyped(tl.state.isabelle)
  }

  test("lhs is 1") {
    val tl = Toplevel.makeToplevelWithTheory()
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

//  test("works with PrOld") {
//    val tl = ToplevelTest.makeToplevel()
//    tl.execCmd("classical var x : bit")
//    tl.execCmd("ambient var rho : program_state")
//    tl.execCmd("program p := { skip; }")
//    tl.execCmd("lemma xxx: PrOld[x:p(rho)] <= PrOld[x:p(rho)]")
//    println(1)
//    tl.execCmd("byqrhl")
//    println(2)
//    assert(tl.state.goal.length == 1)
//    println(3)
//    print(tl.state.goal.head)
//    println(4)
//    tl.state.goal.head.checkWelltyped(tl.state.isabelle)
//  }
}
