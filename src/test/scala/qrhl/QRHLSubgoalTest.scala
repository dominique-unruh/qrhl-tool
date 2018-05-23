package qrhl

import org.scalatest.FunSuite
import qrhl.logic.{Block, Expression, IfThenElse, While}
import qrhl.toplevel.{Toplevel, ToplevelTest}

class QRHLSubgoalTest extends FunSuite {
  val tl: Toplevel = ToplevelTest.makeToplevel()
  def pb(str:String): Expression = tl.state.parseExpression(tl.state.boolT,str)
  def pp(str:String): Expression = tl.state.parseExpression(tl.state.predicateT,str)

  def testToExpressionWelltyped(left:Block, right:Block, pre:Expression, post:Expression): Unit = {
    val qrhl = QRHLSubgoal(left,right,pre,post,Nil)
    qrhl.checkWelltyped()
    val e = qrhl.toExpression
    print(e)
    e.checkWelltyped(tl.state.boolT)
  }

  test("toExpression welltyped") {
    val left = Block()
    val right = Block()
    val pre = pp("top")
    val post = pp("top")
    testToExpressionWelltyped(left,right,pre,post)
  }

  test("toExpression welltyped 2") {
    val left = Block(While(pb("1=2"), Block()))
    val right = Block(IfThenElse(pb("1=2"), Block(), Block()))
    val pre = pp("Cla[true]")
    val post = pp("Cla[false]")
    testToExpressionWelltyped(left,right,pre,post)
  }
}
