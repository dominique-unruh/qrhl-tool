package qrhl.tactic

import info.hupel.isabelle.Operation
import org.log4s
import qrhl._
import qrhl.isabelle.RichTerm

case class ConseqQrhlTac(rule: String) extends Tactic {
  import ConseqQrhlTac.logger

  private val thms_as_subgoals = Operation.implicitly[(BigInt,String),List[Subgoal]]("thms_as_subgoals")

  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(left,right,pre,post,assms) =>
      state.isabelle.isabelle.invoke(thms_as_subgoals,(state.isabelle.contextId,rule)) match {
        case List(QRHLSubgoal(left2,right2,pre2,post2,assms2)) =>
          if (left!=left2)
            throw UserException(s"Left program in current subgoal and in $rule are not identical.\n  $left\nvs.\n  $left2")
          if (right!=right2)
            throw UserException(s"Right program in current subgoal and in $rule are not identical.\n  $right\nvs.\n  $right2")
          if (assms2.nonEmpty)
            throw UserException(s"$rule contains assumptions, that is not supported.")

          val goal1 = AmbientSubgoal(pre.leq(pre2))
          val goal2 = AmbientSubgoal(post2.leq(post))

          List(goal1,goal2)
        case List(goal : AmbientSubgoal) =>
          logger.debug(goal.toString)
          throw UserException(s"Theorem $rule does not refer to a qRHL judgment")
        case _::_ =>
          throw UserException(s"Theorem $rule consists of several theorems")
      }


//
//
//      var goals = List(QRHLSubgoal(left,right,pre.getOrElse(pre2),post.getOrElse(post2),assms)) : List[Subgoal]
//      pre match {
//        case None =>
//        case Some(e) => goals = AmbientSubgoal(pre2.leq(e)).addAssumptions(assms) :: goals
//      }
//      post match {
//        case None =>
//        case Some(e) => goals = AmbientSubgoal(e.leq(post2)).addAssumptions(assms) :: goals
//      }
//      goals
    case _ => throw UserException("Expected a qRHL subgoal")
  }
}

object ConseqQrhlTac {
  private val logger = log4s.getLogger
}