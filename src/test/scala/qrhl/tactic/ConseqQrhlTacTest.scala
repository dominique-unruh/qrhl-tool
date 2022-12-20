package qrhl.tactic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.AmbientSubgoal
import qrhl.toplevel.{TacticCommand, Toplevel, ToplevelTest}

class ConseqQrhlTacTest extends AnyFunSuite {
  def toplevel(): Toplevel = {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.run(
      """quantum var q : bit.
        |quantum var r : bit.
        |qrhl t1: {top ⊓ Qeq[q1 = q2]} skip; ~ skip; {top ⊓ Qeq[q1 = q2]}. admit. qed.
      """.stripMargin)
    tl
  }


  test("do nothing") {
    val tl = toplevel()
    tl.execCmd("qrhl t1: {top ⊓ Qeq[q1 = q2]} skip; ~ skip; {top ⊓ Qeq[q1 = q2]}")
    tl.execCmd(TacticCommand(ConseqQrhlTac("t1", None)))
    val goal = tl.state.goal
    val context = tl.state.isabelle
    print(goal)
    assert(goal.length == 2)
    for (subgoal <- goal) {
      subgoal.checkWelltyped(context)
      assert(subgoal.isInstanceOf[AmbientSubgoal])
    }
  }

  test("rename") {
    val tl = toplevel()
    tl.execCmd("qrhl t1: {top ⊓ Qeq[r1 = r2]} skip; ~ skip; {top ⊓ Qeq[r1 = r2]}")
    val q = tl.state.environment.getQVariable("q")
    val r = tl.state.environment.getQVariable("r")
    tl.execCmd(TacticCommand(ConseqQrhlTac("t1", Some(((List(q), List(r)), (List(q), List(r)))))))
    val goal = tl.state.goal
    val context = tl.state.isabelle
    print(goal)
    assert(goal.length == 3)
    for (subgoal <- goal) {
      subgoal.checkWelltyped(context)
      assert(subgoal.isInstanceOf[AmbientSubgoal])
    }
  }
}
