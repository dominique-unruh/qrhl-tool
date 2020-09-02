package qrhl.tactic

import org.scalatest.FunSuite
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.toplevel.{Toplevel, ToplevelTest}
import IsabelleX.{globalIsabelle => GIsabelle}



class ExpressionTest extends FunSuite {
  test("read print roundtrip") {
    val tl = Toplevel.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    val str = "Cla[ x=(1::int) ]"
    //    val state = tl.state
    val e = RichTerm(tl.state.value.isabelle, str, GIsabelle.predicateT)
    println(e)
    assert(e.toString=="ℭ\uD835\uDD29\uD835\uDD1E[x = 1]")
  }

  test("encodeAsExpression") {
    val tl = Toplevel.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    val state = tl.state
    val e = state.value.parseExpression(GIsabelle.predicateT,"Cla[ x=(1::int) ]")
    val t = e.encodeAsExpression(tl.state.value.isabelle)
    println(e)
    println(t)
    assert(t.typ == GIsabelle.expressionT(GIsabelle.predicateT))
  }

  test("encodeAsExpression roundtrip") {
    val tl = Toplevel.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    val state = tl.state
    val e = state.value.parseExpression(GIsabelle.predicateT,"Cla[ x=(1::int) ]")
    println(e)
    val t = e.encodeAsExpression(tl.state.value.isabelle)
    println(t)
    val e2 = RichTerm.decodeFromExpression(tl.state.value.isabelle, t.isabelleTerm)
    println(e2)

    assert(e.isabelleTerm==e2.isabelleTerm)
    assert(e.typ==e2.typ)
    assert(e==e2)

  }

  test("encodeAsExpression roundtrip 2") {
    val tl = Toplevel.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    val state = tl.state
    val e = state.value.parseExpression(GIsabelle.predicateT,"Cla[ x1=x2 ]")
    println(e)
    val t = e.encodeAsExpression(tl.state.value.isabelle)
    println(t)
    val e2 = RichTerm.decodeFromExpression(tl.state.value.isabelle, t.isabelleTerm)
    println(e2)

    assert(e.isabelleTerm==e2.isabelleTerm)
    assert(e.typ==e2.typ)
    assert(e==e2)

  }

  test("encodeAsExpression roundtrip 3") {
    val tl = Toplevel.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    tl.execCmd("classical var c : int")
    val state = tl.state
    val e = state.value.parseExpression(GIsabelle.predicateT,"Cla[ x1=x2 ∧ c1=c2 ]")
    println(e)
    val t = e.encodeAsExpression(tl.state.value.isabelle)
    println(t)
    val e2 = RichTerm.decodeFromExpression(tl.state.value.isabelle, t.isabelleTerm)
    println(e2)

    assert(e.isabelleTerm==e2.isabelleTerm)
    assert(e.typ==e2.typ)
    assert(e==e2)
  }
}
