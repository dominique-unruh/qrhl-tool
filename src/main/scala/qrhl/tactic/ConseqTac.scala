package qrhl.tactic

import java.io.PrintWriter

import qrhl._
import qrhl.isabellex.RichTerm

case class ConseqTac(pre: Option[RichTerm]=None, post:Option[RichTerm]=None) extends Tactic {
  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
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
