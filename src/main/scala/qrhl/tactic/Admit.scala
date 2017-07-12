package qrhl.tactic

import qrhl.{State, Subgoal, Tactic}

object Admit extends Tactic {
  override def apply(state:State, subgoal: Subgoal): List[Subgoal] = Nil

  override def toString: String = "admit"
}
