package qrhl.tactic

import org.scalatest.{FlatSpec, FunSuite}
import qrhl.toplevel.{Toplevel, ToplevelTest}

class RuleTacTest extends FlatSpec {
  def toplevel(): Toplevel = {
    val tl = Toplevel.makeToplevelWithTheory()
    tl.run(
      """ambient var a : nat.
        |ambient var b : nat.
        |ambient var c : nat.
        |ambient var d : nat.
      """.stripMargin)
    tl
  }

  "rule tactic" should "produce new subgoals" in {
    val tl = toplevel()
    tl.execCmd("lemma test: a+b <= c+d")
    val state2 = tl.state.applyTactic(RuleTac("add_le_mono"))
    print("New goals: ",state2.goal)
    state2.goal.foreach(_.checkWelltyped(tl.state.isabelle))
    assert(state2.goal.length==2)
    // TODO: check the goals themselves?
  }

}
