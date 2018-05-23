package qrhl.tactic

import org.scalatest.FunSuite
import qrhl.isabelle.Isabelle
import qrhl.toplevel.ToplevelTest

class ExpressionTest extends FunSuite {
  test("encodeAsExpression") {
    val tl = ToplevelTest.makeToplevel()
    tl.execCmd("classical var x : int")
    val state = tl.state
    val e = state.parseExpression(state.predicateT,"Cla[ x=(1::int) ]")
    val t = e.encodeAsExpression
    println(e)
    println(t)
    assert(state.isabelle.get.checkType(t) == Isabelle.expressionT(Isabelle.predicateT))
  }
}
