package qrhl.tactic

import org.scalatest.FunSuite
import qrhl.isabellex.IsabelleX
import qrhl.toplevel.{TacticCommand, Toplevel}
import qrhl.{QRHLSubgoal, UserException}
import IsabelleX.{globalIsabelle => GIsabelle}
import isabelle.Free

// Implicits
import GIsabelle.isabelleControl

class CaseTacTest extends FunSuite {
  def toplevel(): Toplevel = {
    val tl = Toplevel.makeToplevelWithTheory()
    tl.run(
      """classical var x : bool.
        |ambient var y : bool.
        |ambient var y2 : bool.
        |ambient var z : nat.
        |program P := { if (y2) then skip; else skip; }.
        """.stripMargin)
    tl
  }

  test("works") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val st = tl.state.value.applyTactic(CaseTac("y", tl.state.value.parseExpression(GIsabelle.boolT, "x1")))
//    print(st.goal)
    assert(st.goal.length==1)
    val pre = st.goal.head.asInstanceOf[QRHLSubgoal].pre
    assert(pre.toString == "ℭ𝔩𝔞[x1 = y] ⊓ ⊤")
    pre.checkWelltyped(tl.state.value.isabelle, GIsabelle.predicateT)
  }


  test("parse") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val cmd = tl.state.value.parseCommand("case y := x1")

    val tac = cmd.asInstanceOf[TacticCommand].tactic.asInstanceOf[CaseTac]
    assert(tac.variable == "y")
    assert(tac.expr.isabelleTerm == Free("x1",GIsabelle.boolT))
  }


  test("fail if the variable has the wrong type") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val ex = intercept[UserException] {
      tl.state.value.applyTactic(CaseTac("z", tl.state.value.parseExpression(GIsabelle.boolT, "x1")))
    }

    assert(ex.getMessage.startsWith("Variable z has type nat, but expression has type bool"))
  }

  test("fail if the variable is reused") {
    val tl = toplevel()
    tl.execCmd("qrhl {Cla[y=True]} skip; ~ skip; {top}")
    val ex = intercept[UserException] {
      tl.state.value.applyTactic(CaseTac("y", tl.state.value.parseExpression(GIsabelle.boolT, "x1")))
    }

    assert(ex.getMessage.startsWith("Variable y already contained in goal"))
  }

  test("fail if the variable is already used in program declaration") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val ex = intercept[UserException] {
      tl.state.value.applyTactic(CaseTac("y2", tl.state.value.parseExpression(GIsabelle.boolT, "x1")))
    }

    assert(ex.getMessage.startsWith("Variable y2 already used in program P"))
  }

  test("fail if the expression contains unindexed program variables") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val ex = intercept[UserException] {
      tl.state.value.applyTactic(CaseTac("y", tl.state.value.parseExpression(GIsabelle.boolT, "x")))
    }

    assert(ex.getMessage.startsWith("Undeclared (or non-indexed) variable x in precondition"))
  }

}

