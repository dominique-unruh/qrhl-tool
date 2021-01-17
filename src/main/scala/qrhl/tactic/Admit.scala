package qrhl.tactic

import hashedcomputation.{Hash, HashTag}

import java.io.PrintWriter
import qrhl.{State, Subgoal, Tactic}

object Admit extends Tactic {
  override def apply(state:State, subgoal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = Nil

  override def toString: String = "admit"

  override val hash: Hash[Admit.this.type] = HashTag()()
}
