package qrhl.tactic

import hashedcomputation.{Hash, HashTag, Hashable}

import java.io.PrintWriter
import qrhl._
import qrhl.logic.ExpressionIndexed

import hashedcomputation.Implicits._

case class ConseqTac(pre: Option[ExpressionIndexed]=None, post:Option[ExpressionIndexed]=None) extends Tactic {
  override def hash: Hash[ConseqTac.this.type] =
    HashTag()(Hashable.hash(pre), Hashable.hash(post))

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
