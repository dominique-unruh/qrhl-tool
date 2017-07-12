package qrhl.tactic

import qrhl.{QRHLSubgoal, State, Subgoal, Tactic}

case class InlineTac(name:String) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(left,right,pre,post) =>
      List(QRHLSubgoal(left.inline(state.environment,name), right.inline(state.environment,name), pre, post))
  }
}
