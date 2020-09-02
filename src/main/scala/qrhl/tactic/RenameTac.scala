package qrhl.tactic

import isabelle.{Context, Term, Typ}
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException, Utils}
import qrhl.logic.{QVariable, Variable}
import qrhl.tactic.FrameRuleTac.colocalityOp

import scala.collection.immutable.ListSet
import scala.language.postfixOps
import IsabelleX.{globalIsabelle => GIsabelle}
import isabelle.control.MLValue

// Implicits
import MLValue.Implicits._
import Context.Implicits._
import Term.Implicits._
import Typ.Implicits._
import scala.concurrent.ExecutionContext.Implicits.global

// Implicits
import GIsabelle.isabelleControl

case class RenameTac(left: Boolean, right: Boolean, renaming: List[(Variable,Variable)]) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case _ : AmbientSubgoal =>
      throw UserException("Expected qRHL subgoal")
    case QRHLSubgoal(leftProg, rightProg, pre, post, assumptions) =>
      val env = state.environment
      def typStr(typ: Typ) = state.isabelle.prettyTyp(typ)

      val fv1 : ListSet[Variable] = if (left) leftProg.variableUse(env).freeVariables else ListSet.empty
      val fv2 : ListSet[Variable] = if (right) rightProg.variableUse(env).freeVariables else ListSet.empty
      val fv12 = fv1 ++ fv2

      // The following conditions are required by the contract of Statement.noConflict
      // No x->x mappings, and no duplicates in domain

      val renaming = this.renaming.distinct
        .filterNot { case (x,y) => x==y }

      val dom = renaming map { _._1 }
      if (!Utils.areDistinct(dom))
        throw UserException("Conflicting variable renamings")

      // Checking conditions from lemma   / rename_qrhl_right

      // A variable is only renamed to a compatible variable (same quantum/classical kind, same type)
      //        assumes valid[simp]: "valid_var_subst σ"
      for ((x,y) <- renaming) {
        if (x.isClassical != y.isClassical)
          throw UserException(s"${x.name} is a ${x.classicalQuantumWord} variable while ${y.name} is a ${x.classicalQuantumWord} variable")
        if (x.valueTyp != y.valueTyp)
          throw UserException(s"${x.name} has type ${typStr(x.valueTyp)} while ${y.name} has ${typStr(y.valueTyp)}")
      }

      //  assumes [simp]: "no_conflict σ c"
      if (left)
        if (!leftProg.noConflict(env, renaming))
          throw UserException("no_conflict condition does not hold for left program")
      //  assumes [simp]: "no_conflict σ d"
      if (right)
        if (!rightProg.noConflict(env, renaming))
          throw UserException("no_conflict condition does not hold for right program")

      //  assumes inj: "inj_on σ (fv c ∪ deidx1 (fvp A) ∪ deidx1 (fvp B))"
      // We break this into two checks:
      // - `renaming` is injective on its domain
      val range = renaming map { _._2 }
      if (!Utils.areDistinct(range))
        throw UserException("Non-injective variable renaming")
      // - "fv c ∪ deidx1 (fvp A) ∪ deidx1 (fvp B)" contains no variables in `forbidden` (the range of `renaming` without the domain)
      val forbidden = range.toSet -- dom

      if ((forbidden & fv12).nonEmpty)
        throw UserException(s"Renaming target(s) ${Variable.varsToString(forbidden & fv12)} conflict with local variables of the program(s)")

      // The variables that must not occur in the invariant: this includes the variables from forbidden above,
      // as well as all quantum variables in the range of `renaming` (because our method for renaming quantum variables in the predicate does not work correctly otherwise)
      val forbiddenInInvariant : Set[Variable] = (if (left)  (forbidden++range.filter(_.isQuantum)).map(_.index1) else Set.empty) ++
                                                 (if (right) (forbidden++range.filter(_.isQuantum)).map(_.index2) else Set.empty)

      val varsPre = pre.variables(env)
      if ((forbiddenInInvariant & varsPre.program).nonEmpty)
        throw UserException(s"Renaming target(s) ${Variable.varsToString(forbiddenInInvariant & varsPre.program)} conflict with local variables of the precondition")

      val varsPost = post.variables(env)
      if ((forbiddenInInvariant & varsPost.program).nonEmpty)
        throw UserException(s"Renaming target(s) ${Variable.varsToString(forbiddenInInvariant & varsPost.program)} conflict with local variables of the postcondition")

      //  defines "σ1 ≡ idx_var_subst True σ"
      //  shows "qRHL A c d B ⟷
      //         qRHL (substp σ1 A) (subst_vars σ c) d (substp σ1 B)"

      val renamedLeft = if (left) leftProg.renameVariables(env, renaming) else leftProg
      val renamedRight = if (right) rightProg.renameVariables(env, renaming) else rightProg

      def renameInvariant1(side: Boolean, inv: RichTerm) : RichTerm = {
        val inv1 = inv.renameCVariables(renaming map { case (x,y) => (x.index(side), y.index(side)) })
        val inv2 = inv1.isabelleTerm
        val qRenaming = renaming collect { case (x : QVariable, y : QVariable) => (x.index(side), y.index(side)) }
        val inv3 = qRenaming.foldLeft(inv2)
          { case (inv, (x,y)) => GIsabelle.swap_variables_subspace(x.variableTerm, y.variableTerm, inv) }
        RichTerm(GIsabelle.predicateT, inv3)
      }

      def renameInvariant(inv: RichTerm) : RichTerm = {
        val inv2 = if (left) renameInvariant1(side = true, inv) else inv
        val inv3 = if (right) renameInvariant1(side = false, inv2) else inv2
        RichTerm(RenameTac.swapOp[(Context, Term), Term](MLValue((state.isabelle.context, inv3.isabelleTerm))).retrieveNow)
      }

      val renamedPre = renameInvariant(pre)
      val renamedPost = renameInvariant(post)

      val forbiddenQInInvariant12 = forbiddenInInvariant collect { case v: QVariable => (v.variableName, v.valueTyp) } toList
      val colocalitySubgoal =
        if (forbiddenQInInvariant12.isEmpty) null
        else {
          val colocalityPre = colocalityOp[(Context, Term, List[(String, Typ)]), Term](
            MLValue((state.isabelle.context, pre.isabelleTerm, forbiddenQInInvariant12))).retrieveNow
          val colocalityPost = colocalityOp[(Context, Term, List[(String, Typ)]), Term](
            MLValue((state.isabelle.context, post.isabelleTerm, forbiddenQInInvariant12))).retrieveNow
          AmbientSubgoal(GIsabelle.conj(colocalityPre, colocalityPost),
            assumptions.map(_.isabelleTerm))
        }

      val newQrhl = QRHLSubgoal(renamedLeft, renamedRight, renamedPre, renamedPost, assumptions)

      if (colocalitySubgoal==null)
        List(newQrhl)
      else
        List(colocalitySubgoal, newQrhl)
  }
}

object RenameTac {
  val swapOp: MLValue[((Context, Term)) => Term] =
    MLValue.compileFunction[(Context, Term), Term]("QRHL_Operations.swap_variables_conv")
}