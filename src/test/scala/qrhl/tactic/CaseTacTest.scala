package qrhl.tactic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.isabellex.IsabelleX
import qrhl.toplevel.{TacticCommand, Toplevel, ToplevelTest}
import qrhl.{QRHLSubgoal, UserException}
import IsabelleX.{globalIsabelle => GIsabelle}
import de.unruh.isabelle.control.IsabelleMLException
import de.unruh.isabelle.pure.Free
import qrhl.toplevel.ToplevelTest.output

import scala.concurrent.ExecutionContext.Implicits.global

// Implicits
import GIsabelle.isabelleControl

class CaseTacTest extends AnyFunSuite {
  def toplevel(): Toplevel = {
    val tl = ToplevelTest.makeToplevelWithTheory()
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
    val st = tl.state.applyTactic(CaseTac("y", tl.state.parseExpressionLongform(GIsabelle.boolT, "x1", indexed = true)))
    val context = tl.state.isabelle
//    print(st.goal)
    assert(st.goal.length==1)
    val pre = st.goal.head.asInstanceOf[QRHLSubgoal].pre
    pre.checkWelltyped(tl.state.isabelle, GIsabelle.predExpressionT)
    assert(pre.decodeFromExpression(context).toString == "ℭ𝔩𝔞[x1 = y] ⊓ ⊤")
  }


  test("parse") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val cmd = tl.state.parseCommand("case y := x1")

    val tac = cmd.asInstanceOf[TacticCommand].tactic.asInstanceOf[CaseTac]
    assert(tac.variable == "y")
    assert(tac.expr.decodeFromExpression(tl.state.isabelle).isabelleTerm == Free("x1",GIsabelle.boolT))
  }


  test("fail if the variable has the wrong type") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val ex = intercept[UserException] {
      tl.state.applyTactic(CaseTac("z", tl.state.parseExpressionLongform(GIsabelle.boolT, "x1", indexed = true)))
    }

    assert(ex.getMessage.startsWith("Variable z has type nat, but expression has type bool"))
  }

  test("fail if the variable is reused") {
    val tl = toplevel()
    tl.execCmd("qrhl {Cla[y=True]} skip; ~ skip; {top}")
    val ex = intercept[UserException] {
      tl.state.applyTactic(CaseTac("y", tl.state.parseExpressionLongform(GIsabelle.boolT, "x1", indexed = true)))
    }

    assert(ex.getMessage.startsWith("Variable y already contained in goal"))
  }

  test("fail if the variable is already used in program declaration") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val ex = intercept[UserException] {
      tl.state.applyTactic(CaseTac("y2", tl.state.parseExpressionLongform(GIsabelle.boolT, "x1", indexed = true)))
    }

    assert(ex.getMessage.startsWith("Variable y2 already used in program P"))
  }

  test("fail if the expression contains unindexed program variables") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} skip; ~ skip; {top}")
    val ex = intercept[IsabelleMLException] {
      tl.state.applyTactic(CaseTac("y", tl.state.parseExpressionLongform(GIsabelle.boolT, "x", indexed = true)))
    }

    assert(ex.getMessage.startsWith("Type unification failed"))
//    assert(ex.getMessage.startsWith("Undeclared (or non-indexed) variable x in precondition"))
  }
}

