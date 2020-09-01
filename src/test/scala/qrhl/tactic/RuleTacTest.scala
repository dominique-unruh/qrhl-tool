package qrhl.tactic

import info.hupel.isabelle.{Operation, ProverResult}
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


  test("produce new subgoals") {
    val tl = toplevel()
    tl.execCmd("lemma test: a+b <= c+d")
    val state2 = try {
      tl.state.value.applyTactic(RuleTac("add_le_mono"))
    } catch {
      case e : ProverResult.Failure =>
        println(Isabelle.symbols.symbolsToUnicode(e.fullMessage))
        throw e
    }
    print("New goals: ",state2.goal)
    state2.goal.foreach(_.checkWelltyped(tl.state.value.isabelle))
    assert(state2.goal.length==2)
    // TODO: check the goals themselves?
  }


  test("instantiations") {
    try {
      val tl = toplevel()
      tl.execCmd("lemma test: a <= c")
//      val inst = List(("j", RichTerm(tl.state.isabelle, "0::nat", Isabelle.dummyT)))
      val state2 = tl.state.value.applyTactic(RuleTac("le_trans[where j=0]"))
      val goals = state2.goal
      print("New goals: ", goals)
      goals.foreach(_.checkWelltyped(tl.state.value.isabelle))
      assert(goals.length == 2)
      assert(goals(0).toString == "a ≤ 0")
      assert(goals(1).toString == "0 ≤ c")
    } catch {
      case e : ProverResult.Failure =>
        println(Isabelle.symbols.symbolsToUnicode(e.fullMessage))
        throw e
    }
  }

  test("unicode") {
    val tl = toplevel()
    tl.execCmd("lemma test: 1=1")
    val rule = RuleTac("trans[where s=α]")
    val state2 = try {
      tl.state.value.applyTactic(rule)
    } catch {
      case e : ProverResult.Failure =>
        println(Isabelle.symbols.symbolsToUnicode(e.fullMessage))
        throw e
    }
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
