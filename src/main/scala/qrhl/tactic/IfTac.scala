package qrhl.tactic

import java.io.PrintWriter
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.logic.{Block, IfThenElse}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException}
import IsabelleX.{globalIsabelle => GIsabelle}
import hashedcomputation.{Hash, HashTag, Hashable}

import scala.collection.mutable.ListBuffer

// Implicits
import GIsabelle.isabelleControl
import hashedcomputation.Implicits._

case class IfTac(left:Boolean, trueFalse:Option[Boolean]=None) extends Tactic {

  override def hash: Hash[IfTac.this.type] = HashTag()(Hashable.hash(left), Hashable.hash(trueFalse))

  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case AmbientSubgoal(_) =>
      throw UserException("Expected a qRHL subgoal")
    case QRHLSubgoal(leftProg, rightProg, pre, post, assumptions) =>
      // Parses the left/right as "if (cond) thenBranch else elseBranch; rest"
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
        val subgoal = GIsabelle.less_eq(pre.isabelleTerm, GIsabelle.classical_subspace(GIsabelle.not(condIdx.isabelleTerm)))
        subgoals.append(AmbientSubgoal(RichTerm(subgoal)))
      }

      // Constructing the else-branch goal in case it should be shown impossible
      if (trueFalse.contains(true)) {
        // pre <= Cla[cond]
        val subgoal = GIsabelle.less_eq(pre.isabelleTerm, GIsabelle.classical_subspace(condIdx.isabelleTerm))
        subgoals.append(AmbientSubgoal(RichTerm(subgoal)))
      }

      // Constructing the then-branch goal
      if (!trueFalse.contains(false)) {
        // pre ⊓ Cla[cond1]
        val pre2 = GIsabelle.inf(pre.isabelleTerm, GIsabelle.classical_subspace(condIdx.isabelleTerm))
        val prog2 = thenBranch ++ rest
        val subgoal = QRHLSubgoal(if (left) prog2 else leftProg, if (left) rightProg else prog2,
          RichTerm(GIsabelle.predicateT, pre2), post, assumptions)
        subgoals.append(subgoal)
      }

      // Constructing the else-branch goal
      if (!trueFalse.contains(true)) {
        val pre2 = GIsabelle.inf(pre.isabelleTerm, GIsabelle.classical_subspace(GIsabelle.not(condIdx.isabelleTerm)))
        val prog2 = elseBranch ++ rest
        val subgoal = QRHLSubgoal(if (left) prog2 else leftProg, if (left) rightProg else prog2,
          RichTerm(GIsabelle.predicateT, pre2), post, assumptions)
        subgoals.append(subgoal)
      }

      subgoals.toList
  }
}
