package qrhl.tactic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.Free
import org.scalatest.{FlatSpec, FunSuite}
import qrhl.{QRHLSubgoal, UserException}
import qrhl.toplevel.{TacticCommand, Toplevel, ToplevelTest}

class CaseTacTest extends FlatSpec {
  def toplevel(): Toplevel = {
    val tl = ToplevelTest.makeToplevel()
    tl.run(
      """classical var x : bool.
        |ambient var y : bool.
        |ambient var y2 : bool.
        |ambient var z : nat.
        |program P := { if (y2) then skip; else skip; }.
        """.stripMargin)
    tl
  }

  "case tactic" should "work" in {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val st = tl.state.applyTactic(CaseTac("y", tl.state.parseExpression(tl.state.boolT, "x1")))
//    print(st.goal)
    assert(st.goal.length==1)
    val pre = st.goal.head.asInstanceOf[QRHLSubgoal].pre
    assert(pre.toString == "ℭ𝔩𝔞[x1 = y] ⊓ top")
    pre.checkType()
  }


  "case tactic" should "parse" in {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val cmd = tl.state.parseCommand("case y := x1")

    val tac = cmd.asInstanceOf[TacticCommand].tactic.asInstanceOf[CaseTac]
    assert(tac.variable == "y")
    assert(tac.expr.isabelleTerm == Free("x1",HOLogic.boolT))
  }


  "case tactic" should "fail if the variable has the wrong type" in {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val ex = intercept[UserException] {
      tl.state.applyTactic(CaseTac("z", tl.state.parseExpression(tl.state.boolT, "x1")))
    }

    assert(ex.msg.startsWith("Variable z has type nat, but expression has type bool"))
  }

  "case tactic" should "fail if the variable is reused" in {
    val tl = toplevel()
    tl.execCmd("qrhl {Cla[y=True]} skip; ~ skip; {top}")
    val ex = intercept[UserException] {
      tl.state.applyTactic(CaseTac("y", tl.state.parseExpression(tl.state.boolT, "x1")))
    }

    assert(ex.msg.startsWith("Variable y already contained in goal"))
  }

  "case tactic" should "fail if the variable is already used in program declaration" in {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val ex = intercept[UserException] {
      tl.state.applyTactic(CaseTac("y2", tl.state.parseExpression(tl.state.boolT, "x1")))
    }

    assert(ex.msg.startsWith("Variable y2 already used in program P"))
  }

  "case tactic" should "fail if the expression contains unindexed program variables" in {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val ex = intercept[UserException] {
      tl.state.applyTactic(CaseTac("y", tl.state.parseExpression(tl.state.boolT, "x")))
    }

    assert(ex.msg.startsWith("Undeclared (or non-indexed) variable x in precondition"))
  }

}

