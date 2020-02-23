package qrhl.tactic

import org.log4s
import qrhl.isabelle.Isabelle
import qrhl.logic.{Block, CVariable, Local, QVariable}
import qrhl.tactic.FrameRuleTac.colocalityOp
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException, Utils}
import qrhl.tactic.LocalTac.logger

case class LocalTac(left : Boolean, cVariables : List[CVariable], qVariables : List[QVariable]) extends Tactic {

  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case AmbientSubgoal(_) =>
      throw UserException("Expected qRHL goal")
    case QRHLSubgoal(leftProg, rightProg, pre, post, assumptions) =>
      val lrWord = if (left) "left" else "right"
      val env = state.environment

      // cvarsInProg / qvarsInProg: local variables declared at the top of the program
      // body: the body of that program
      val (cvarsInProg, qvarsInProg, body) = (if (left) leftProg else rightProg) match {
        case Block(Local(cvars, qvars, body)) => (cvars, qvars, body)
        case body =>
          if (cVariables.isEmpty && qVariables.isEmpty)
            throw UserException(s"Expected $lrWord program to be of the form { local ...; ... }")
          else
            (Nil, Nil, body)
      }

      val varUse = body.variableUse(env)

      // Set of variables that are removed or added from the locals (excluding variables that do not occur inside anyway)
      val cvars = Utils.symmetricDifferrence(cVariables.toSet, cvarsInProg.toSet).intersect(varUse.classical)
      val qvars = Utils.symmetricDifferrence(qVariables.toSet, qvarsInProg.toSet).intersect(varUse.quantum)

      // Checking that pre/postcondition do not contain local classical variables
      val cvarsIdx = cvars map { _.index(left) }
      val preConflict = pre.caVariables(env).classical.intersect(cvarsIdx)
      if (preConflict.nonEmpty)
        throw UserException(s"Precondition must not contain the classical variable(s) ${preConflict map { _.name } mkString ", "}")
      val postConflict = post.caVariables(env).classical.intersect(cvarsIdx)
      if (postConflict.nonEmpty)
        throw UserException(s"Postcondition must not contain the classical variable(s) ${postConflict map { _.name } mkString ", "}")

      // Subgoals for checking that pre/postcondition do not contain local quantum variables
      val qvarsIdx = qvars map { _.index(left) }
      val qVarsIdxPairs = qvarsIdx.map { v => (v.variableName, v.valueTyp) }
      val colocalityPre = state.isabelle.isabelle.invoke(colocalityOp,
        (state.isabelle.contextId, pre.isabelleTerm, qVarsIdxPairs.toList))
      val colocalityPost = state.isabelle.isabelle.invoke(colocalityOp,
        (state.isabelle.contextId, post.isabelleTerm, qVarsIdxPairs.toList))
      val colocality = AmbientSubgoal(Isabelle.conj(colocalityPre.isabelleTerm, colocalityPost.isabelleTerm), assumptions.map(_.isabelleTerm))

      val newProg = Local.makeIfNeeded(cVariables, qVariables, body).toBlock

      // qRHL goal with changed/removed "local"
      val newQRHLGoal = if (left)
        QRHLSubgoal(newProg, rightProg, pre, post, assumptions)
      else
        QRHLSubgoal(leftProg, newProg, pre, post, assumptions)

      logger.debug(colocalityPre.toString)
      logger.debug(colocalityPost.toString)
      logger.debug(newQRHLGoal.toString)

      List(colocality, newQRHLGoal)
  }
}

object LocalTac {
  private val logger = log4s.getLogger
}
