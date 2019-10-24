package qrhl.tactic

import qrhl.logic.{Block, Local}
import qrhl.tactic.FrameRuleTac.colocalityOp
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException}
import qrhl.tactic.LocalTac.Mode

case class LocalTac(mode: Mode) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = mode match {
    case LocalTac.joint => ???
    case LocalTac.left => apply1(state, goal, left=true)
    case LocalTac.right => apply1(state, goal, left=false)
  }

  def apply1(state: State, goal: Subgoal, left:Boolean): List[Subgoal] = goal match {
    case AmbientSubgoal(goal) =>
      throw UserException("Expected qRHL goal")
    case QRHLSubgoal(leftProg, rightProg, pre, post, assumptions) =>
      val lrWord = if (left) "left" else "right"
      val env = state.environment

      val (cvars, qvars, body) = (if (left) leftProg else rightProg) match {
        case Block(Local(cvars, qvars, body)) => (cvars, qvars, body)
        case _ => throw UserException(s"Expected $lrWord to be of the form { local ...; ... }")
      }

      // Checking that pre/postcondition do not contain local classical variables
      val cvarsIdx = cvars map { _.index(left) }
      val preConflict = pre.caVariables(env).classical.intersect(cvarsIdx.toSet)
      if (preConflict.nonEmpty)
        throw UserException(s"Precondition must not contain the classical variable(s) ${cvarsIdx map { _.name } mkString ", "}")
      val postConflict = post.caVariables(env).classical.intersect(cvarsIdx.toSet)
      if (postConflict.nonEmpty)
        throw UserException(s"Postcondition must not contain the classical variable(s) ${cvarsIdx map { _.name } mkString ", "}")

      // Subgoals for checking that pre/postcondition do not contain local quantum variables
      val qvarsIdx = qvars map { _.index(left) }
      val qVarsIdxPairs = qvarsIdx.map { v => (v.variableName, v.valueTyp) }
      val colocalityPre = AmbientSubgoal(state.isabelle.isabelle.invoke(colocalityOp,
        (state.isabelle.contextId, pre.isabelleTerm, qVarsIdxPairs)))
      val colocalityPost = AmbientSubgoal(state.isabelle.isabelle.invoke(colocalityOp,
        (state.isabelle.contextId, post.isabelleTerm, qVarsIdxPairs)))

      // qRHL goal without the "local"
      val newQRHLGoal = if (left)
        QRHLSubgoal(body, rightProg, pre, post, assumptions)
      else
        QRHLSubgoal(leftProg, body, pre, post, assumptions)

      println(colocalityPre)
      println(colocalityPost)
      println(newQRHLGoal)

      List(colocalityPre, colocalityPost, newQRHLGoal)
  }
}

object LocalTac {
  sealed trait Mode
  case object left extends Mode
  case object right extends Mode
  case object joint extends Mode
}