package qrhl

import org.scalatest.FunSuite
import qrhl.isabelle.Isabelle
import qrhl.logic.{Block, Expression, IfThenElse, While}
import qrhl.tactic.SeqTac
import qrhl.toplevel.{Toplevel, ToplevelTest}

class QRHLSubgoalTest extends FunSuite {
  lazy val tl: Toplevel = {
    val tl = ToplevelTest.makeToplevel()
    tl.execCmd("classical var x : int")
    tl.execCmd("classical var y : int")
    tl
  }
  def pb(str:String): Expression = tl.state.parseExpression(Isabelle.boolT,str)
  def pp(str:String): Expression = tl.state.parseExpression(Isabelle.predicateT,str)

  def testToExpressionWelltypedRoundtrip(context: Isabelle.Context, left:Block, right:Block, pre:Expression, post:Expression): Unit = {
    val context = tl.state.isabelle
    val qrhl = QRHLSubgoal(left,right,pre,post,Nil)
    qrhl.checkWelltyped(context)
    val e = qrhl.toExpression(context)
    print(e)
    e.checkWelltyped(context, Isabelle.boolT)

    val qrhl2 = Subgoal(context, e)
    print(qrhl2)
    qrhl.checkWelltyped(context)

    assert(qrhl2 == qrhl)
  }

  test("toExpression welltyped roundtrip") {
    val left = Block()
    val right = Block()
    val pre = pp("top")
    val post = pp("top")
    testToExpressionWelltypedRoundtrip(tl.state.isabelle, left,right,pre,post)
  }

  test("toExpression welltyped roundtrip 2") {
    val left = Block(While(pb("1=2"), Block()))
    val right = Block(IfThenElse(pb("1=2"), Block(), Block()))
    val pre = pp("Cla[True]")
    val post = pp("Cla[False]")
    testToExpressionWelltypedRoundtrip(tl.state.isabelle, left,right,pre,post)
  }

  test("toExpression welltyped roundtrip 3") {
    val left = Block()
    val right = Block()
    val pre = pp("top")
    val post = pp("Cla[x1=x2]")
    testToExpressionWelltypedRoundtrip(tl.state.isabelle, left,right,pre,post)
  }

}
