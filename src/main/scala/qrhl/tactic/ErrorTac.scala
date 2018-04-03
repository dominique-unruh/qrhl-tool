package qrhl.tactic

import qrhl.{State, Subgoal, Tactic, UserException}

case class ErrorTac(msg:String) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] =
    throw UserException(msg)
}
