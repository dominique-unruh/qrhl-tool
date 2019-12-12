package qrhl.tactic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.Term
import qrhl.isabelle.Isabelle.{classical_subspace, conj, inf, less_eq, mk_eq, predicateT}
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.logic.{Block, IfThenElse}
import qrhl.tactic.JointIfTac.{allCases, differentCases, sameCases}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException, Utils}

import scala.collection.mutable.ListBuffer

case class JointIfTac(cases : List[(Boolean,Boolean)]) extends Tactic {
  assert(Utils.areDistinct(cases))

  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
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
      val condLIdx = condR.index1(env).isabelleTerm
      val condRIdx = condL.index2(env).isabelleTerm
      val casesSet = Set(cases:_*)

      val subgoals = new ListBuffer[Subgoal]

      def eqBool(t: Term, truth: Boolean) =
        if (truth) t else Isabelle.not(t)

      assert(cases.nonEmpty)
      val excludedCasesCond =
        if (casesSet == allCases)
          HOLogic.True
        else if (casesSet == sameCases)
          mk_eq(condLIdx, condRIdx)
        else if (casesSet == differentCases)
          Isabelle.not(mk_eq(condLIdx, condRIdx))
        else
          Isabelle.disj({
            for ((l,r) <- cases)
              yield
                conj(eqBool(condLIdx,l),eqBool(condRIdx,r))
          } :_*)

      val casesSubgoal = less_eq(pre.isabelleTerm, classical_subspace(excludedCasesCond))
      subgoals.append(AmbientSubgoal(RichTerm(predicateT, casesSubgoal)))

      for ((l,r) <- cases) {
        val newLeft = (if (l) thenBranchL else elseBranchL) ++ restL
        val newRight = (if (r) thenBranchR else elseBranchR) ++ restR
        val newPre = inf(pre.isabelleTerm, classical_subspace(conj(eqBool(condLIdx,l),eqBool(condRIdx,r))))
        subgoals.append(QRHLSubgoal(newLeft,newRight,RichTerm(predicateT,newPre),post,assumptions))
      }

      subgoals.toList
  }
}

object JointIfTac {
  private val allCases = Set((true,true),(false,false),(true,false),(false,true))
  private val sameCases = Set((true,true),(false,false))
  private val differentCases = Set((true,false),(false,true))
}