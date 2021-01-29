package qrhl.tactic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.isabellex.IsabelleX
import qrhl.toplevel.{Toplevel, ToplevelTest}
import qrhl.toplevel.ToplevelTest.output

//noinspection ZeroIndexToHead
class RuleTacTest extends AnyFunSuite {
  def toplevel(): Toplevel = {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.run(
      """ambient var a : nat.
        |ambient var b : nat.
        |ambient var c : nat.
        |ambient var d : nat.
      """.stripMargin)
    tl
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


  test("instantiations") {
      val tl = toplevel()
      tl.execCmd("lemma test: a <= c")
//      val inst = List(("j", RichTerm(tl.state.isabelle, "0::nat", Isabelle.dummyT)))
      val state2 = tl.state.applyTactic(RuleTac("le_trans[where j=0]"))
      val goals = state2.goal
      print("New goals: ", goals)
      goals.foreach(_.checkWelltyped(tl.state.isabelle))
      assert(goals.length == 2)
      assert(goals.toList(0).toString == "a ≤ 0")
      assert(goals.toList(1).toString == "0 ≤ c")
  }

  test("unicode") {
    val tl = toplevel()
    tl.execCmd("lemma test: 1=1")
    val rule = RuleTac("trans[where s=α]")
    val state2 = tl.state.applyTactic(rule)
  }

/*
  test("temp") {
    // TODO open issue in libisabelle
    val tl = toplevel()
    try {
      tl.isabelle.invoke(Operation.Hello,"α")
    } catch {
      case e : ProverResult.Failure =>
        println(Isabelle.symbolsToUnicode(e.fullMessage))
        throw e
    }
  }
*/
}
