package qrhl.tactic

import qrhl._
import qrhl.logic.Expression

case class ConseqTac(pre: Option[Expression]=None, post:Option[Expression]=None) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(left,right,pre2,post2,assms) =>
      var goals = List(QRHLSubgoal(left,right,pre.getOrElse(pre2),post.getOrElse(post2),assms)) : List[Subgoal]
      pre match {
        case None =>
        case Some(e) => goals = AmbientSubgoal(pre2.leq(e)).addAssumptions(assms) :: goals
      }
      post match {
        case None =>
        case Some(e) => goals = AmbientSubgoal(e.leq(post2)).addAssumptions(assms) :: goals
      }
      goals
    case _ => throw UserException("Expected a qRHL subgoal")
  }
}
