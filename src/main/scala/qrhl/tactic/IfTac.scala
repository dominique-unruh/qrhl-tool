package qrhl.tactic

import java.io.PrintWriter
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.logic.{Block, ExpressionIndexed, ExpressionInstantiatedIndexed, IfThenElse}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException}
import IsabelleX.{globalIsabelle => GIsabelle}
import hashedcomputation.{Hash, HashTag, Hashable}
import qrhl.logic.Variable.{Index1, Index12}

import scala.collection.mutable.ListBuffer

// Implicits
import GIsabelle.isabelleControl
import hashedcomputation.Implicits._

case class IfTac(side:Index12, trueFalse:Option[Boolean]=None) extends Tactic {

  override def hash: Hash[IfTac.this.type] = HashTag()(Hashable.hash(side), Hashable.hash(trueFalse))

  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case AmbientSubgoal(_) =>
      throw UserException("Expected a qRHL subgoal")
    case QRHLSubgoal(leftProg, rightProg, pre, post, assumptions) =>
      // Parses the left/right as "if (cond) thenBranch else elseBranch; rest"
      val (cond,thenBranch,elseBranch,rest) = side.choose(leftProg, rightProg) match {
        case Block(IfThenElse(cond,thenBranch,elseBranch), rest @_*) => (cond,thenBranch,elseBranch,Block(rest:_*))
        case _ => throw UserException(s"First statement on ${side.leftright} side must be an if-statement")
      }

      val ctxt = state.isabelle.context
      val preI = pre.instantiateMemory
//      val postI = post.instantiateMemory
      val condIdx = cond.index(ctxt, side).instantiateMemory
      val subgoals = new ListBuffer[Subgoal]

      // Constructing the then-branch goal in case it should be shown impossible
      if (trueFalse.contains(false)) {
        // pre <= Cla[not cond]
        val subgoal = pre.leq(ctxt, ExpressionInstantiatedIndexed.fromTerm(
          GIsabelle.classical_subspace(GIsabelle.not(condIdx.termInst.isabelleTerm))).abstractMemory)
        subgoals.append(AmbientSubgoal(subgoal))
      }

      // Constructing the else-branch goal in case it should be shown impossible
      if (trueFalse.contains(true)) {
        // pre <= Cla[cond]
        val subgoal = pre.leq(ctxt, ExpressionInstantiatedIndexed.fromTerm(
          GIsabelle.classical_subspace(condIdx.termInst.isabelleTerm)).abstractMemory)
        subgoals.append(AmbientSubgoal(subgoal))
      }

      // Constructing the then-branch goal
      if (!trueFalse.contains(false)) {
        // pre ⊓ Cla[cond1]
        val pre2 = ExpressionInstantiatedIndexed.fromTerm(
          GIsabelle.inf(preI.termInst.isabelleTerm, GIsabelle.classical_subspace(condIdx.termInst.isabelleTerm)))
        val prog2 = thenBranch ++ rest
        val subgoal = QRHLSubgoal(side.choose(prog2, leftProg), side.choose(rightProg, prog2),
          pre2.abstractMemory, post, assumptions)
        subgoals.append(subgoal)
      }

      // Constructing the else-branch goal
      if (!trueFalse.contains(true)) {
        val pre2 = ExpressionInstantiatedIndexed.fromTerm(
          GIsabelle.inf(preI.termInst.isabelleTerm, GIsabelle.classical_subspace(GIsabelle.not(condIdx.termInst.isabelleTerm))))
        val prog2 = elseBranch ++ rest
        val subgoal = QRHLSubgoal(side.choose(prog2, leftProg), side.choose(rightProg, prog2),
          pre2.abstractMemory, post, assumptions)
        subgoals.append(subgoal)
      }

      subgoals.toList
  }
}
