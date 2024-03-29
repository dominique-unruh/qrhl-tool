package qrhl.tactic

import hashedcomputation.{Hash, HashTag, Hashable}

import java.io.PrintWriter
import qrhl._
import hashedcomputation.Implicits._

case class InlineTac(name:String) extends Tactic {
  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case QRHLSubgoal(left,right,pre,post,assms) =>
      if (!state.environment.programs.contains(name))
        throw UserException(s"Undefined program $name")
      List(QRHLSubgoal(left.inline(state.environment,name), right.inline(state.environment,name), pre, post, assms))
    case DenotationalEqSubgoal(left, right, assms) =>
      if (!state.environment.programs.contains(name))
        throw UserException(s"Undefined program $name")
      List(DenotationalEqSubgoal(left.inline(state.environment, name), right.inline(state.environment, name), assms))
    case _ => throw UserException("inline supported only for qRHL subgoals and denotational equivalence subgoals")
  }

  override def hash: Hash[InlineTac.this.type] = HashTag()(Hashable.hash(name))
}
