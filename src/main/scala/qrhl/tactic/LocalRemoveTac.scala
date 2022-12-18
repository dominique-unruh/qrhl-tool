package qrhl.tactic

import java.io.PrintWriter
import org.log4s
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.logic.{Block, CVariable, ExpressionInstantiatedIndexed, Local, Nonindexed, QVariable, VTSingle, VarTerm, Variable}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException}
import qrhl.tactic.LocalRemoveTac.logger
import IsabelleX.{globalIsabelle => GIsabelle}
import GIsabelle.Ops
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.Term
import hashedcomputation.{Hash, HashTag, Hashable}
import qrhl.logic.Variable.Index12

import scala.collection.immutable.ListSet

// Implicits
import scala.concurrent.ExecutionContext.Implicits.global
import GIsabelle.isabelleControl
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._
import hashedcomputation.Implicits._


case class LocalRemoveTac(side: Index12, withInit: Boolean, variablesToRemove : List[Variable with Nonindexed]) extends Tactic {
  override def hash: Hash[LocalRemoveTac.this.type] =
    HashTag()(Hashable.hash(side), Hashable.hash(withInit), Hashable.hash(variablesToRemove))

  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case AmbientSubgoal(_) =>
      throw UserException("Expected qRHL goal")
    case QRHLSubgoal(leftProg, rightProg, pre, post, assumptions) =>
      val env = state.environment
      val ctxt = state.isabelle.context

      // cvarsInProg / qvarsInProg: local variables declared at the top of the program
      // body: the body of that program
      val (varsInProg, body) = side.choose (leftProg, rightProg) match {
        case Block(Local(vars, body)) => (vars, body)
        case body =>
            throw UserException(s"Expected ${side.leftright} program to be of the form { local ...; ... }")
      }

      if (!variablesToRemove.toSet.subsetOf(varsInProg.toSet))
        throw UserException(s"Trying to remove variables ${Variable.varsToString(variablesToRemove.toSet -- varsInProg.toSet)} that are not in the toplevel local-statement")
      // variablesToRemove, but with default in case of Nil
      val variablesToRemove2 = if (variablesToRemove.isEmpty) varsInProg else variablesToRemove

      val varUse = body.variableUse(ctxt, env)
      val preVars = pre.variables(ctxt, env)
      val postVars = post.variables(ctxt, env)
      val prePostVars = preVars.program ++ postVars.program

      // Variables that we can remove by an application of the RemoveLocal1/2 rule
      val variablesToRemoveViaRule = variablesToRemove2.toSet -- (prePostVars.map(_.unindex))
      // Variables that we can remove because they do not occur in the program
      val variablesToRemoveNonOccur = variablesToRemove2.toSet -- variablesToRemoveViaRule -- varUse.freeVariables

      // If variables to remove were explicitly specified, we raise an error if we cannot remove all of them
      // Otherwise just just remove what we can
      if (variablesToRemove.nonEmpty) {
        val missing = variablesToRemove.toSet -- (variablesToRemoveViaRule ++ variablesToRemoveNonOccur)
        if (missing.nonEmpty)
          throw UserException(s"Cannot remove variables ${missing} (they occur both in program and pre/postcondition)")
      }

      // using ListSet to keep the ordering
      val variablesToKeep = ListSet(varsInProg:_*) -- (variablesToRemoveViaRule ++ variablesToRemoveNonOccur)

      // Subgoals for checking that pre/postcondition do not contain local quantum variables
      // (we checked that above already, but detection of quantum variables is not 100% sound)
      val qvarsIdx = variablesToRemoveViaRule map { _.index(side) }
      val qVarsIdxPairs = qvarsIdx.map { v => (v.basename, v.theIndex, v.valueTyp) }
      val colocalityPre = Ops.colocal_pred_qvars(state.isabelle.context, pre.term.isabelleTerm, qVarsIdxPairs.toList).retrieveNow
      val colocalityPost = Ops.colocal_pred_qvars(state.isabelle.context, post.term.isabelleTerm, qVarsIdxPairs.toList).retrieveNow
      val colocality = AmbientSubgoal(GIsabelle.conj(colocalityPre, colocalityPost), assumptions.map(_.isabelleTerm))

      val newProg = Local.makeIfNeeded(variablesToKeep.toSeq, body).toBlock

      val newPre =
        if (!withInit)
          pre.instantiateMemory
        else {
          def addQInitToPre(pre: ExpressionInstantiatedIndexed, v: QVariable): ExpressionInstantiatedIndexed = {
            import GIsabelle._
            ExpressionInstantiatedIndexed.fromTerm(
              inf(pre.termInst.isabelleTerm,
                liftSpace(span1(ket(undefined(v.valueTyp))),
                  VarTerm.isabelleTermLongform(VTSingle(v), classical=false, indexed=false))))
          }

          def addCInitToPre(pre: ExpressionInstantiatedIndexed, vs: Seq[CVariable]): ExpressionInstantiatedIndexed = {
            import GIsabelle._
            if (vs.isEmpty)
              pre
            else {
              val eqs = vs map { v => mk_eq(v.variableTermShort, undefined(v.valueTyp)) }
              ExpressionInstantiatedIndexed.fromTerm(
                inf(pre.termInst.isabelleTerm, classical_subspace(conj(eqs: _*))))
            }
          }

          val newPre1 =
            addCInitToPre(pre.instantiateMemory, Variable.classical(variablesToRemoveViaRule).toSeq)
          val newPre2 =
            Variable.quantum(variablesToRemoveViaRule).foldLeft(newPre1) {
              addQInitToPre
            }
          newPre2
        }

      // qRHL goal with removed "local"
      val newQRHLGoal = side match {
        case Variable.Index1 =>
          QRHLSubgoal(newProg, rightProg, newPre.abstractMemory, post, assumptions)
        case Variable.Index2 =>
          QRHLSubgoal(leftProg, newProg, newPre.abstractMemory, post, assumptions)
      }

      logger.debug(colocalityPre.toString)
      logger.debug(colocalityPost.toString)
      logger.debug(newQRHLGoal.toString)

      List(colocality, newQRHLGoal)
  }
}

object LocalRemoveTac {
  private val logger = log4s.getLogger
}
