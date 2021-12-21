package qrhl.tactic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.toplevel.{Parser, ParserContext, Toplevel, ToplevelTest}
import IsabelleX.{globalIsabelle => GIsabelle}
import de.unruh.isabelle.pure.{Term, Type}
import qrhl.isabellex.IsabelleX.globalIsabelle.{cl2T, clT, intT, isabelleControl}

import scala.concurrent.ExecutionContext.Implicits.global



class ExpressionTest extends AnyFunSuite {
  test("read print roundtrip") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    val str = "Cla[ x=1 ]"
    //    val state = tl.state
    val e = RichTerm.decodeFromExpression(tl.state.isabelle, str, GIsabelle.predicateT, indexed = false)
    println(e)
    assert(e.toString=="ℭ\uD835\uDD29\uD835\uDD1E[x = 1]")
  }

  test("encodeAsExpression") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    val state = tl.state
    val e = state.parseExpression(GIsabelle.predicateT,"Cla[ x=1 ]", indexed=false)
    val t = e.encodeAsExpression(tl.state.isabelle, indexed=false)
    println(e)
    println(t)
    println(t.typ.pretty(tl.state.isabelle.context))
    assert(t.typ == GIsabelle.expressionT(GIsabelle.predicateT, indexed = false))
  }

  test("encodeAsExpression roundtrip") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    val state = tl.state
    val e = state.parseExpression(GIsabelle.predicateT,"Cla[ x=1 ]", indexed = false)
    println(e)
    val t = e.encodeAsExpression(tl.state.isabelle, indexed=false)
    println(t)
    val e2 = RichTerm.decodeFromExpression(tl.state.isabelle, t.isabelleTerm)
    println(e2)

    assert(e.isabelleTerm==e2.isabelleTerm)
    assert(e.typ==e2.typ)
    assert(e==e2)
  }

  test("encodeAsExpression roundtrip 2") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    val state = tl.state
    val e = state.parseExpression(GIsabelle.predicateT,"Cla[ x1=x2 ]", indexed = true)
    println(e)
    val t = e.encodeAsExpression(tl.state.isabelle, indexed=true)
    println(t)
    val e2 = RichTerm.decodeFromExpression(tl.state.isabelle, t.isabelleTerm)
    println(e2)

    assert(e.isabelleTerm==e2.isabelleTerm)
    assert(e.typ==e2.typ)
    assert(e==e2)
  }

  test("encodeAsExpression roundtrip 3") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    tl.execCmd("classical var c : int")
    val state = tl.state
    val e = state.parseExpression(GIsabelle.predicateT,"Cla[ x1=x2 ∧ c1=c2 ]", indexed = true)
    println(e)
    val t = e.encodeAsExpression(tl.state.isabelle, indexed=true)
    println(t)
    val e2 = RichTerm.decodeFromExpression(tl.state.isabelle, t.isabelleTerm)
    println(e2)

    assert(e.isabelleTerm==e2.isabelleTerm)
    assert(e.typ==e2.typ)
    assert(e==e2)
  }

  val intExprT: Type = clT -->: intT
  val intExpr2T: Type = cl2T -->: intT

  test ("getter x mem") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    val t = tl.state.isabelle.readTerm("%m. getter x m", intExprT)
    val e = RichTerm.decodeFromExpression(tl.state.isabelle, t)
    assert(e.toString == "x")
    assert(e.typ == intT)
  }

/*  test ("getter x1 mem") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    val t = tl.state.isabelle.readTerm("%m. getter x1 m", intExpr2T)
    val e = RichTerm.decodeFromExpression(tl.state.isabelle, t)
    assert(e.toString == "x1")
    assert(e.typ == intT)
  }*/

  test ("getter (cregister_chain cFst x) mem") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    val t = tl.state.isabelle.readTerm("%m. getter (cregister_chain cFst x) m", intExpr2T)
    val e = RichTerm.decodeFromExpression(tl.state.isabelle, t)
    assert(e.toString == "x1")
    assert(e.typ == intT)
  }

/*  test ("getter x (fst mem)") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    val t = tl.state.isabelle.readTerm("%m. getter x (fst m)", intExpr2T)
    val e = RichTerm.decodeFromExpression(tl.state.isabelle, t)
    assert(e.toString == "x1")
    assert(e.typ == intT)
  }*/
}
