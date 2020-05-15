package qrhl.tactic

import org.scalatest.FunSuite
import qrhl.QRHLSubgoal
import qrhl.logic.Assign
import qrhl.toplevel.{Toplevel, ToplevelTest}

class EqualTacTest extends FunSuite {
  def toplevel(): Toplevel = {
    val tl = Toplevel.makeToplevelWithTheory()
    tl.run(
      """classical var x : bit.
        |quantum var q : bit.
        |program p := { x <- undefined; on q apply undefined; }.
      """.stripMargin)
    tl
  }

  test("permit postcondition to contain the quantum variable equality") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} call p; ~ call p; {Qeq[q1=q2]}")
    val state2 = tl.state.value.applyTactic(EqualTac(Nil,Nil,Nil,Nil))
    state2.goal.foreach(_.checkWelltyped(tl.state.value.isabelle))
    assert(state2.goal.length==2)
  }


  test("work on while loops") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} while (x ≠ 0) x <- x - 1; ~ while (x ≠ 0) x <- x - 1; {top}")
    val state2 = tl.state.value.applyTactic(EqualTac(Nil,Nil,Nil,Nil))
    state2.goal.foreach(_.checkWelltyped(tl.state.value.isabelle))
    assert(state2.goal.length==2)
  }

  test("with mismatch") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} while (x ≠ 0) x <- x - 2; ~ while (x ≠ 0) x <- x - 1; {top}")
    val state2 = tl.state.value.applyTactic(EqualTac(Nil,Nil,Nil,Nil))
    state2.goal.foreach(_.checkWelltyped(tl.state.value.isabelle))
    assert(state2.goal.length==3)
    val goal2 = state2.goal(1).asInstanceOf[QRHLSubgoal]
    assert(goal2.left.statements.length==1)
    val List(left) = goal2.left.statements
    assert(left.isInstanceOf[Assign])
  }

}
