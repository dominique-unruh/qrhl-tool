package qrhl.tactic

import java.io.PrintWriter

import qrhl.{State, Subgoal, Tactic}

object Admit extends Tactic {
  override def apply(state:State, subgoal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = Nil

  override def toString: String = "admit"
}
