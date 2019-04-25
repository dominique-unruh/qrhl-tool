package qrhl.tactic

import info.hupel.isabelle.ProverResult
import org.scalatest.FunSuite
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.toplevel.Toplevel

//noinspection ZeroIndexToHead
class RuleTacTest extends FunSuite {
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

  test("instantiations") {
    try {
      val tl = toplevel()
      tl.execCmd("lemma test: a <= c")
      val inst = List(("j", RichTerm(tl.state.isabelle, "0::nat", Isabelle.dummyT)))
      val state2 = tl.state.applyTactic(RuleTac("le_trans", inst))
      val goals = state2.goal
      print("New goals: ", goals)
      goals.foreach(_.checkWelltyped(tl.state.isabelle))
      assert(goals.length == 2)
      assert(goals(0).toString == "a ≤ 0")
      assert(goals(1).toString == "0 ≤ c")
    } catch {
      case e : ProverResult.Failure =>
        println(Isabelle.symbolsToUnicode(e.fullMessage))
        throw e
    }
  }

  test("produce new subgoals") {
    val tl = toplevel()
    tl.execCmd("lemma test: a+b <= c+d")
    val state2 = tl.state.applyTactic(RuleTac("add_le_mono"))
    print("New goals: ",state2.goal)
    state2.goal.foreach(_.checkWelltyped(tl.state.isabelle))
    assert(state2.goal.length==2)
    // TODO: check the goals themselves?
  }



}
