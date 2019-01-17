package qrhl.tactic

import qrhl._
import qrhl.isabelle.RichTerm
import qrhl.logic.{Block, Statement}


abstract class WpBothStyleTac() extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(leftProg, rightProg, pre, post, assms) =>
      val lastL = leftProg.statements.lastOption.getOrElse(throw UserException(s"No last statement on left side"))
      val restL = leftProg.statements.dropRight(1)
      val lastR = rightProg.statements.lastOption.getOrElse(throw UserException(s"No last statement on right side"))
      val restR = rightProg.statements.dropRight(1)
      val (wp,subgoals) = getWP(state, lastL, lastR, post)
      subgoals.toList.map(_.addAssumptions(assms)) ::: List(QRHLSubgoal(Block(restL: _*), Block(restR: _*), pre, wp, assms))
    case _ => throw UserException(s"$this supported only for qRHL subgoals")
  }

  /** Returns a (preferably weakest) precondition for post given programs left/right.
    * @return (wp,assms), where wp is the precondition, and assms are potential additional subgoals that need to be proven
    */
  def getWP(state: State, left:Statement, right:Statement, post:RichTerm) : (RichTerm,Seq[Subgoal])
}
