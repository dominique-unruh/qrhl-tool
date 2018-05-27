package qrhl

import org.scalatest.FunSuite
import qrhl.isabelle.Isabelle
import qrhl.logic.{Block, Expression, IfThenElse, While}
import qrhl.toplevel.{Toplevel, ToplevelTest}

class QRHLSubgoalTest extends FunSuite {
  val tl: Toplevel = ToplevelTest.makeToplevel()
  def pb(str:String): Expression = tl.state.parseExpression(Isabelle.boolT,str)
  def pp(str:String): Expression = tl.state.parseExpression(Isabelle.predicateT,str)

  def testToExpressionWelltyped(context: Isabelle.Context, left:Block, right:Block, pre:Expression, post:Expression): Unit = {
    val qrhl = QRHLSubgoal(left,right,pre,post,Nil)
    qrhl.checkWelltyped(context)
    val e = qrhl.toExpression(context)
    print(e)
    e.checkWelltyped(context, Isabelle.boolT)
  }

  test("toExpression welltyped") {
    val left = Block()
    val right = Block()
    val pre = pp("top")
    val post = pp("top")
    testToExpressionWelltyped(tl.state.isabelle.get, left,right,pre,post)
  }

  test("toExpression welltyped 2") {
    val left = Block(While(pb("1=2"), Block()))
    val right = Block(IfThenElse(pb("1=2"), Block(), Block()))
    val pre = pp("Cla[true]")
    val post = pp("Cla[false]")
    testToExpressionWelltyped(tl.state.isabelle.get, left,right,pre,post)
  }
}
