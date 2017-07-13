package qrhl.tactic

import qrhl.logic.{Block, Expression, Statement}
import qrhl._

/**
  * Created by unruh on 7/9/17.
  */
abstract class WpStyleTac(left:Boolean) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(leftProg,rightProg,pre,post) =>
      if (left) {
        val last = leftProg.statements.lastOption.getOrElse(throw UserException(s"No last statement of ${if (left) "left" else "right"} side"))
        val left1 = leftProg.statements.dropRight(1)
        val wp = getWP(state, left=true, last, post)
        List(QRHLSubgoal(Block(left1: _*), rightProg, pre, wp))
      } else {
        val last = rightProg.statements.last
        val right1 = rightProg.statements.dropRight(1)
        val wp = getWP(state, left=false, last, post)
        List(QRHLSubgoal(leftProg, Block(right1: _*), pre, wp))
      }
  }

  def getWP(state: State, left:Boolean, statement:Statement, post:Expression) : Expression
}
