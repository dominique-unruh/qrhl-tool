package qrhl.tactic

import qrhl.logic.{Block, Statement}
import qrhl._
import qrhl.isabellex.RichTerm


abstract class WpStyleTac(val left:Boolean) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(leftProg, rightProg, pre, post, assms) =>
      if (left) {
        val last = leftProg.statements.lastOption.getOrElse(throw UserException(s"No last statement of ${if (left) "left" else "right"} side"))
        val left1 = leftProg.statements.dropRight(1)
        val wp = getWP(state, last, post)
        List(QRHLSubgoal(Block(left1: _*), rightProg, pre, wp, assms))
      } else {
        val last = rightProg.statements.last
        val right1 = rightProg.statements.dropRight(1)
        val wp = getWP(state, last, post)
        List(QRHLSubgoal(leftProg, Block(right1: _*), pre, wp, assms))
      }
    case _ => throw UserException(s"$this supported only for qRHL subgoals")
  }

  def getWP(state: State, statement:Statement, post:RichTerm) : RichTerm
}
