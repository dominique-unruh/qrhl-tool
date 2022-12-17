package qrhl.tactic

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.pure.Term
import org.scalatest.funsuite.AnyFunSuite
import qrhl.QRHLSubgoal
import qrhl.isabellex.IsabelleX.globalIsabelle
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.logic.{Assign, QVariable}
import qrhl.toplevel.ToplevelTest.output
import qrhl.toplevel.{Parser, Toplevel, ToplevelTest}

import scala.collection.immutable.ListSet
import scala.concurrent.ExecutionContext.Implicits.global

class EqualTacTest extends AnyFunSuite {
  def toplevel(): Toplevel = {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.run(
      """classical var x : bit.
        |quantum var q : bit.
        |quantum var r : bit.
        |program p := { x <- undefined; on q apply undefined; }.
      """.stripMargin)
    tl
  }

  test("removeClassicals") {
    val tl = toplevel()
    val state = tl.state
    val ctxt = state.isabelle.context
    val env = state.environment
    val term = state.parseExpression(globalIsabelle.predicateT, "Cla[x1=0]", indexed = true).castIndexed.instantiateMemory
    val x = env.getCVariable("x")
    val result = EqualTac.removeClassicals(ctxt, env, term, ListSet(x), ListSet(x))
    val resultStr = result.toString
    println(resultStr)
    assert(resultStr == "⨅x1. ℭ𝔩𝔞[x1 = 0]")
  }

  test("permit postcondition to contain the quantum variable equality") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} call p; ~ call p; {Qeq[q1=q2]}")
    val state2 = tl.state.applyTactic(EqualTac(Nil,Nil,Nil,Nil))
    state2.goal.iterator.foreach(_.checkWelltyped(tl.state.isabelle))
    assert(state2.goal.length==2)
  }


  test("work on while loops") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} while (x ≠ 0) x <- x - 1; ~ while (x ≠ 0) x <- x - 1; {top}")
    val state2 = tl.state.applyTactic(EqualTac(Nil,Nil,Nil,Nil))
    state2.goal.foreach(_.checkWelltyped(tl.state.isabelle))
    assert(state2.goal.length==2)
  }

  test("with mismatch") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} while (x ≠ 0) x <- x - 2; ~ while (x ≠ 0) x <- x - 1; {top}")
    val state2 = tl.state.applyTactic(EqualTac(Nil,Nil,Nil,Nil))
    state2.goal.foreach(_.checkWelltyped(tl.state.isabelle))
    assert(state2.goal.length==3)
    val goal2 = state2.goal.toList(1).asInstanceOf[QRHLSubgoal]
    assert(goal2.left.statements.length==1)
    val List(left) = goal2.left.statements
    assert(left.isInstanceOf[Assign])
  }

  test("SimpleQeq") {
    val tl = toplevel()
    val simpleQeq = new EqualTac.SimpleQeq(tl.state.environment)
    val e = RichTerm.decodeFromExpression(tl.state.isabelle, "Qeq[q1,r1 = q2,r2]", globalIsabelle.predicateT, indexed = true)
    println(e)
    e.isabelleTerm match {
      case `simpleQeq`(vars) =>
        println(vars)
        assert(vars == Set(QVariable.fromName("q",globalIsabelle.bitT), QVariable.fromName("r",globalIsabelle.bitT)))
      case _ => fail("Should have matched")
    }
  }
}
