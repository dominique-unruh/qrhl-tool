package qrhl.tactic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.toplevel.{Parser, ParserContext, Toplevel, ToplevelTest}
import IsabelleX.{globalIsabelle => GIsabelle}
import de.unruh.isabelle.pure.Term
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl

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


  test("tmp REMOVE ME") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    tl.execCmd("classical var y : int")
    val state = tl.state
    val e = state.parseExpression(GIsabelle.prodT(GIsabelle.intT, GIsabelle.intT),
      "(y,x)", indexed = false)
    println(e)
    val t = e.encodeAsExpression(tl.state.isabelle, indexed=false)
    println(t)
    val e2 = RichTerm.decodeFromExpression(tl.state.isabelle, t.isabelleTerm)
    println(e2)

    assert(e.isabelleTerm==e2.isabelleTerm)
    assert(e.typ==e2.typ)
    assert(e==e2)
  }
}
