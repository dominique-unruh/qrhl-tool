package qrhl.tactic

import org.scalatest.FunSuite
import qrhl.toplevel.{Toplevel, ToplevelTest}

class EqualTacTest extends FunSuite {
  def toplevel(): Toplevel = {
    val tl = ToplevelTest.makeToplevel()
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
    val state2 = tl.state.applyTactic(EqualTac)
    state2.goal.foreach(_.checkWelltyped())
    assert(state2.goal.length==2)
  }


  test("work on while loops") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} while (x ≠ 0) x <- x - 1; ~ while (x ≠ 0) x <- x - 1; {top}")
    val state2 = tl.state.applyTactic(EqualTac)
    state2.goal.foreach(_.checkWelltyped())
    assert(state2.goal.length==2)
  }
}
