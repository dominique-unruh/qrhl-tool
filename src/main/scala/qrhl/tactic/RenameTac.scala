package qrhl.tactic

import java.io.PrintWriter
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException, Utils}
import qrhl.logic.{CVariable, ExpressionIndexed, ExpressionInstantiatedIndexed, Nonindexed, QVariable, Variable}

import scala.collection.immutable.ListSet
import scala.language.postfixOps
import IsabelleX.{globalIsabelle => GIsabelle}
import GIsabelle.Ops
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.Typ
import hashedcomputation.{Hash, HashTag, Hashable}
import qrhl.logic.Variable.{Index1, Index12, Index2}

// Implicits
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._
import scala.concurrent.ExecutionContext.Implicits.global

// Implicits
import GIsabelle.isabelleControl
import hashedcomputation.Implicits._

case class RenameTac(left: Boolean, right: Boolean,
                     renaming: List[(Variable with Nonindexed, Variable with Nonindexed)]) extends Tactic {
  override def hash: Hash[RenameTac.this.type] =
    HashTag()(Hashable.hash(left), Hashable.hash(right), Hashable.hash(renaming))

  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case _ : AmbientSubgoal =>
      throw UserException("Expected qRHL subgoal")
    case QRHLSubgoal(leftProg, rightProg, pre, post, assumptions) =>
      val env = state.environment
      val ctxt = state.isabelle.context
      def typStr(typ: Typ) = state.isabelle.prettyTyp(typ)

      val fv1 : ListSet[Variable with Nonindexed] = if (left) leftProg.variableUse(ctxt, env).freeVariables else ListSet.empty
      val fv2 : ListSet[Variable with Nonindexed] = if (right) rightProg.variableUse(ctxt, env).freeVariables else ListSet.empty
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
          throw UserException(s"${x.shortformName} is a ${x.classicalQuantumWord} variable while ${y.shortformName} is a ${x.classicalQuantumWord} variable")
        if (x.valueTyp != y.valueTyp)
          throw UserException(s"${x.shortformName} has type ${typStr(x.valueTyp)} while ${y.shortformName} has ${typStr(y.valueTyp)}")
      }

      //  assumes [simp]: "no_conflict σ c"
      if (left)
        if (!leftProg.noConflict(ctxt, env, renaming))
          throw UserException("no_conflict condition does not hold for left program")
      //  assumes [simp]: "no_conflict σ d"
      if (right)
        if (!rightProg.noConflict(ctxt, env, renaming))
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

      val varsPre = pre.variables(ctxt, env)
      if ((forbiddenInInvariant & varsPre.program).nonEmpty)
        throw UserException(s"Renaming target(s) ${Variable.varsToString(forbiddenInInvariant & varsPre.program)} conflict with local variables of the precondition")

      val varsPost = post.variables(ctxt, env)
      if ((forbiddenInInvariant & varsPost.program).nonEmpty)
        throw UserException(s"Renaming target(s) ${Variable.varsToString(forbiddenInInvariant & varsPost.program)} conflict with local variables of the postcondition")

      //  defines "σ1 ≡ idx_var_subst True σ"
      //  shows "qRHL A c d B ⟷
      //         qRHL (substp σ1 A) (subst_vars σ c) d (substp σ1 B)"

      val renamedLeft = if (left) leftProg.renameVariables(ctxt, env, renaming) else leftProg
      val renamedRight = if (right) rightProg.renameVariables(ctxt, env, renaming) else rightProg

      def renameInvariant1(side: Index12, inv: ExpressionInstantiatedIndexed) : ExpressionInstantiatedIndexed = {
        val inv1 = inv.renameCVariables(renaming collect { case (x:CVariable,y:CVariable) => (x.index(side).castIndexedSafe, y.index(side).castIndexedSafe) })
        val inv2 = inv1.instantiateMemory.termInst.isabelleTerm
        val qRenaming = renaming collect { case (x : QVariable, y : QVariable) => (x.index(side), y.index(side)) }
        val inv3 = qRenaming.foldLeft(inv2)
          { case (inv, (x,y)) => GIsabelle.swap_variables_subspace(x.variableTermShort, y.variableTermShort, inv) }
        ExpressionInstantiatedIndexed.fromTerm(inv3)
      }

      def renameInvariant(inv: ExpressionInstantiatedIndexed) : ExpressionInstantiatedIndexed = {
        val inv2 = if (left) renameInvariant1(side = Index1, inv) else inv
        val inv3 = if (right) renameInvariant1(side = Index2, inv2) else inv2
        ExpressionInstantiatedIndexed.fromTerm(Ops.swapOp(state.isabelle.context, inv3.termInst.isabelleTerm).retrieveNow)
      }

      val renamedPre = renameInvariant(pre.instantiateMemory)
      val renamedPost = renameInvariant(post.instantiateMemory)

      val forbiddenQInInvariant12 = forbiddenInInvariant collect { case v: QVariable => (v.basename, v.theIndex, v.valueTyp) } toList
      val colocalitySubgoal =
        if (forbiddenQInInvariant12.isEmpty) null
        else {
          val colocalityPre = Ops.colocal_pred_qvars(state.isabelle.context, pre.term.isabelleTerm, forbiddenQInInvariant12).retrieveNow
          val colocalityPost = Ops.colocal_pred_qvars(state.isabelle.context, post.term.isabelleTerm, forbiddenQInInvariant12).retrieveNow
          AmbientSubgoal(GIsabelle.conj(colocalityPre, colocalityPost),
            assumptions.map(_.isabelleTerm))
        }

      val newQrhl = QRHLSubgoal(renamedLeft, renamedRight, renamedPre.abstractMemory, renamedPost.abstractMemory, assumptions)

      if (colocalitySubgoal==null)
        List(newQrhl)
      else
        List(colocalitySubgoal, newQrhl)
  }
}
