package qrhl.tactic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.QRHLSubgoal
import qrhl.isabellex.IsabelleX
import qrhl.toplevel.{Toplevel, ToplevelTest}
import IsabelleX.{globalIsabelle => GIsabelle}
import qrhl.toplevel.ToplevelTest.output

class SeqTacTest extends AnyFunSuite {
  def testSeqRule(pre:String,post:String,left:String,right:String,middle:String) : Unit = {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("classical var x : int")
    val state = tl.state
    val left2 = state.parseBlock(left)
    val right2 = state.parseBlock(right)
    val pre2 = state.parseExpression(GIsabelle.predicateT,pre)
    val post2 = state.parseExpression(GIsabelle.predicateT,post)
    val qrhl = QRHLSubgoal(left2,right2,pre2,post2,Nil)
    val middle2 = state.parseExpression(GIsabelle.predicateT,middle)
    val tac = SeqTac(1,1,middle2)
    val goals = tac(state,qrhl)
    assert(goals.length == 2)
    val List(goal1,goal2) = goals
    goal1.checkWelltyped(tl.state.isabelle)
    goal2.checkWelltyped(tl.state.isabelle)
    assert(goal1.isInstanceOf[QRHLSubgoal])
    assert(goal2.isInstanceOf[QRHLSubgoal])
    val qrhl1 = goal1.asInstanceOf[QRHLSubgoal]
    val qrhl2 = goal2.asInstanceOf[QRHLSubgoal]
    assert(qrhl1.pre == pre2)
    assert(qrhl2.post == post2)
    assert(qrhl1.post == middle2)
    assert(qrhl2.pre == middle2)
  }

  test("seq rule succeeds") {
    testSeqRule("Cla[ x=(1::int) ]", "Cla[ x=(1::int) ]",
      "x <- 1; x <- 2;", "x <- 1; x <- 2;", "Cla[False]")
  }

  test("seq rule succeeds, x1=x2") {
    testSeqRule("Cla[ x=(1::int) ]", "Cla[ x=(1::int) ]",
      "x <- 1; x <- 2;", "x <- 1; x <- 2;", "Cla[x1=x2]")
  }
}
