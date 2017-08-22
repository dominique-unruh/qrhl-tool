package qrhl.tactic

import qrhl._

case class InlineTac(name:String) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(left,right,pre,post,assms) =>
      List(QRHLSubgoal(left.inline(state.environment,name), right.inline(state.environment,name), pre, post, assms))
    case _ => throw UserException("inline supported only for qRHL subgoals")
  }
}
