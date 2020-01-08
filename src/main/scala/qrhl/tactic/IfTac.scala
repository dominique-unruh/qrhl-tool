package qrhl.tactic

import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.logic.{Block, IfThenElse}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException}

import scala.collection.mutable.ListBuffer

case class IfTac(left:Boolean, trueFalse:Option[Boolean]=None) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case AmbientSubgoal(_) =>
      throw UserException("Expected a qRHL subgoal")
    case QRHLSubgoal(leftProg, rightProg, pre, post, assumptions) =>
      val (cond,thenBranch,elseBranch,rest) = (if (left) leftProg else rightProg) match {
        case Block(IfThenElse(cond,thenBranch,elseBranch), rest @_*) => (cond,thenBranch,elseBranch,Block(rest:_*))
        case _ => throw UserException(s"First statement on ${if (left) "left" else "right"} side must be an if-statement")
      }

      val env = state.environment
      val condIdx = cond.index(env, left=left)

      val subgoals = new ListBuffer[Subgoal]

      // Constructing the then-branch goal in case it should be shown impossible
      if (trueFalse.contains(false)) {
        // pre <= Cla[not cond]
        val subgoal = Isabelle.less_eq(pre.isabelleTerm, Isabelle.classical_subspace(Isabelle.not(condIdx.isabelleTerm)))
        subgoals.append(AmbientSubgoal(RichTerm(subgoal)))
      }

      // Constructing the else-branch goal in case it should be shown impossible
      if (trueFalse.contains(true)) {
        // pre <= Cla[cond]
        val subgoal = Isabelle.less_eq(pre.isabelleTerm, Isabelle.classical_subspace(condIdx.isabelleTerm))
        subgoals.append(AmbientSubgoal(RichTerm(subgoal)))
      }

      // Constructing the then-branch goal
      if (!trueFalse.contains(false)) {
        val pre2 = Isabelle.inf(pre.isabelleTerm, Isabelle.classical_subspace(condIdx.isabelleTerm))
        val prog2 = thenBranch ++ rest
        val subgoal = QRHLSubgoal(if (left) prog2 else leftProg, if (left) rightProg else prog2,
          RichTerm(Isabelle.predicateT, pre2), post, assumptions)
        subgoals.append(subgoal)
      }

      // Constructing the else-branch goal
      if (!trueFalse.contains(true)) {
        val pre2 = Isabelle.inf(pre.isabelleTerm, Isabelle.classical_subspace(Isabelle.not(condIdx.isabelleTerm)))
        val prog2 = elseBranch ++ rest
        val subgoal = QRHLSubgoal(if (left) prog2 else leftProg, if (left) rightProg else prog2,
          RichTerm(Isabelle.predicateT, pre2), post, assumptions)
        subgoals.append(subgoal)
      }

      subgoals.toList
  }
}