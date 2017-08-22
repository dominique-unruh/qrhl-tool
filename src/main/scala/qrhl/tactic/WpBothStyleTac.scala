package qrhl.tactic

import qrhl._
import qrhl.logic.{Block, Expression, Statement}


abstract class WpBothStyleTac() extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(leftProg, rightProg, pre, post, assms) =>
      val lastL = leftProg.statements.lastOption.getOrElse(throw UserException(s"No last statement on left side"))
      val restL = leftProg.statements.dropRight(1)
      val lastR = rightProg.statements.lastOption.getOrElse(throw UserException(s"No last statement on right side"))
      val restR = rightProg.statements.dropRight(1)
      val wp = getWP(state, lastL, lastR, post)
      List(QRHLSubgoal(Block(restL: _*), Block(restR: _*), pre, wp, assms))
    case _ => throw UserException(s"$this supported only for qRHL subgoals")
  }

  def getWP(state: State, left:Statement, right:Statement, post:Expression) : Expression
}
