package qrhl.tactic

import org.scalatest.FunSuite
import qrhl.QRHLSubgoal
import qrhl.isabelle.Isabelle
import qrhl.toplevel.ToplevelTest

class SeqTacTest extends FunSuite {
  test("seq rule succeeds") {
    val tl = ToplevelTest.makeToplevel()
    tl.execCmd("classical var x : int")
    val state = tl.state
    val left = state.parseBlock("x <- 1; x <- 2;")
    val pre = state.parseExpression(Isabelle.predicateT,"Cla[ x=(1::int) ]")
    val qrhl = QRHLSubgoal(left,left,pre,pre,Nil)
    val tac = SeqTac(1,1,state.parseExpression(Isabelle.predicateT,"Cla[False]"))
    val goals = tac(state,qrhl)
    assert(goals.length == 2)
    val List(goal1,goal2) = goals
    goal1.checkWelltyped(tl.state.isabelle)
    goal2.checkWelltyped(tl.state.isabelle)
    assert(goal1.isInstanceOf[QRHLSubgoal])
    assert(goal2.isInstanceOf[QRHLSubgoal])
  }
}
