package qrhl.tactic

import java.io.PrintWriter
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.logic.{Block, ExpressionInstantiatedIndexed, IfThenElse}
import qrhl.tactic.JointIfTac.{allCases, differentCases, sameCases}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException, Utils}
import IsabelleX.{globalIsabelle => GIsabelle}
import de.unruh.isabelle.pure.Term
import hashedcomputation.{Hash, HashTag, Hashable}

import scala.collection.mutable.ListBuffer
import hashedcomputation.Implicits._
import qrhl.logic.Variable.{Index1, Index2}

case class JointIfTac(cases : List[(Boolean,Boolean)]) extends Tactic {
  assert(Utils.areDistinct(cases))

  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case AmbientSubgoal(_) =>
      throw UserException("Expected a qRHL subgoal")
    case QRHLSubgoal(leftProg, rightProg, pre, post, assumptions) =>
      val (condL,thenBranchL,elseBranchL,restL) = leftProg match {
        case Block(IfThenElse(cond,thenBranch,elseBranch), rest @_*) => (cond,thenBranch,elseBranch,Block(rest:_*))
        case _ => throw UserException(s"First statement on left side must be an if-statement")
      }
      val (condR,thenBranchR,elseBranchR,restR) = rightProg match {
        case Block(IfThenElse(cond,thenBranch,elseBranch), rest @_*) => (cond,thenBranch,elseBranch,Block(rest:_*))
        case _ => throw UserException(s"First statement on right side must be an if-statement")
      }

      val env = state.environment
      val ctxt = state.isabelle.context
      val condLIdx = condL.index(ctxt, Index1).instantiateMemory
      val condRIdx = condR.index(ctxt, Index2).instantiateMemory
      val casesSet = Set(cases:_*)

      val subgoals = new ListBuffer[Subgoal]

      def eqBool(t: Term, truth: Boolean) =
        if (truth) t else GIsabelle.not(t)

      assert(cases.nonEmpty)
      // Logically equivalent to "there is a (l,r) <- cases such condLIdx=l, condRIdx=r"
      val excludedCasesCond =
        if (casesSet == allCases)
          GIsabelle.True_const
        else if (casesSet == sameCases)
          GIsabelle.mk_eq(condLIdx.termInst.isabelleTerm, condRIdx.termInst.isabelleTerm)
        else if (casesSet == differentCases)
          GIsabelle.not(GIsabelle.mk_eq(condLIdx.termInst.isabelleTerm, condRIdx.termInst.isabelleTerm))
        else
          GIsabelle.disj({
            for ((l,r) <- cases)
              yield
                GIsabelle.conj(eqBool(condLIdx.termInst.isabelleTerm,l),eqBool(condRIdx.termInst.isabelleTerm,r))
          } :_*)

      val casesSubgoal = pre.leq(ExpressionInstantiatedIndexed.fromTerm(GIsabelle.classical_subspace(excludedCasesCond)).abstractMemory)
      subgoals.append(AmbientSubgoal(casesSubgoal))

      for ((l,r) <- cases) {
        val newLeft = (if (l) thenBranchL else elseBranchL) ++ restL
        val newRight = (if (r) thenBranchR else elseBranchR) ++ restR
        val newPre = ExpressionInstantiatedIndexed.fromTerm(
          GIsabelle.inf(
            pre.instantiateMemory.termInst.isabelleTerm,
            GIsabelle.classical_subspace(GIsabelle.conj(
              eqBool(condLIdx.termInst.isabelleTerm, l),
              eqBool(condRIdx.termInst.isabelleTerm, r)))))
        subgoals.append(QRHLSubgoal(newLeft, newRight, newPre.abstractMemory, post, assumptions))
      }

      subgoals.toList
  }

  override def hash: Hash[JointIfTac.this.type] = HashTag()(Hashable.hash(cases))
}

object JointIfTac {
  private val allCases = Set((true,true),(false,false),(true,false),(false,true))
  private val sameCases = Set((true,true),(false,false))
  private val differentCases = Set((true,false),(false,true))
}