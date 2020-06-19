package qrhl.tactic

import info.hupel.isabelle.pure.Term
import org.log4s
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.logic.{Block, CVariable, Local, QVariable, VTSingle, VarTerm, Variable}
import qrhl.tactic.FrameRuleTac.colocalityOp
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException, Utils}
import qrhl.tactic.LocalRemoveTac.logger

import scala.collection.immutable.ListSet

case class LocalRemoveTac(left : Boolean, withInit: Boolean, variablesToRemove : List[Variable]) extends Tactic {

  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case AmbientSubgoal(_) =>
      throw UserException("Expected qRHL goal")
    case QRHLSubgoal(leftProg, rightProg, pre, post, assumptions) =>
      val lrWord = if (left) "left" else "right"
      val env = state.environment

      // cvarsInProg / qvarsInProg: local variables declared at the top of the program
      // body: the body of that program
      val (varsInProg, body) = (if (left) leftProg else rightProg) match {
        case Block(Local(vars, body)) => (vars, body)
        case body =>
            throw UserException(s"Expected $lrWord program to be of the form { local ...; ... }")
      }

      if (!variablesToRemove.toSet.subsetOf(varsInProg.toSet))
        throw UserException(s"Trying to remove variables ${Variable.varsToString(variablesToRemove.toSet -- varsInProg.toSet)} that are not in the toplevel local-statement")
      // variablesToRemove, but with default in case of Nil
      val variablesToRemove2 = if (variablesToRemove.isEmpty) varsInProg else variablesToRemove

      val varUse = body.variableUse(env)
      val preVars = pre.variables(env)
      val postVars = post.variables(env)
      val prePostVars = preVars.program ++ postVars.program

      // Variables that we can remove by an application of the RemoveLocal1/2 rule
      val variablesToRemoveViaRule = variablesToRemove2.toSet -- (prePostVars collect { case Variable.Indexed(v, `left`) => v })
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
      val qvarsIdx = variablesToRemoveViaRule map { _.index(left) }
      val qVarsIdxPairs = qvarsIdx.map { v => (v.variableName, v.valueTyp) }
      val colocalityPre = state.isabelle.isabelle.invoke(colocalityOp,
        (state.isabelle.contextId, pre.isabelleTerm, qVarsIdxPairs.toList))
      val colocalityPost = state.isabelle.isabelle.invoke(colocalityOp,
        (state.isabelle.contextId, post.isabelleTerm, qVarsIdxPairs.toList))
      val colocality = AmbientSubgoal(Isabelle.conj(colocalityPre.isabelleTerm, colocalityPost.isabelleTerm), assumptions.map(_.isabelleTerm))

      val newProg = Local.makeIfNeeded(variablesToKeep.toSeq, body).toBlock

      val newPre =
        if (!withInit)
          pre
        else {
          def addQInitToPre(pre: Term, v: QVariable) = {
            import Isabelle._
            inf(pre, liftSpace(span1(ket(undefined(v.valueTyp))), VarTerm.isabelleTerm(VTSingle(v))))
          }

          def addCInitToPre(pre: Term, vs: Seq[CVariable]): Term = {
            import Isabelle._
            if (vs.isEmpty) return pre
            val eqs = vs map { v => Isabelle.mk_eq(v.valueTerm, undefined(v.valueTyp)) }
            inf(pre, classical_subspace(conj(eqs: _*)))
          }

          val newPre1 =
            addCInitToPre(pre.isabelleTerm, Variable.classical(variablesToRemoveViaRule).toSeq)
          val newPre2 =
            Variable.quantum(variablesToRemoveViaRule).foldLeft(newPre1) {
              addQInitToPre
            }
          RichTerm(Isabelle.predicateT, newPre2)
        }

      // qRHL goal with removed "local"
      val newQRHLGoal = if (left)
        QRHLSubgoal(newProg, rightProg, newPre, post, assumptions)
      else
        QRHLSubgoal(leftProg, newProg, newPre, post, assumptions)

      logger.debug(colocalityPre.toString)
      logger.debug(colocalityPost.toString)
      logger.debug(newQRHLGoal.toString)

      List(colocality, newQRHLGoal)
  }
}

object LocalRemoveTac {
  private val logger = log4s.getLogger
}
