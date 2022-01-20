package qrhl.tactic

import java.io.PrintWriter
import qrhl.isabellex.{IsabelleConsts, IsabelleX, RichTerm}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException}
import IsabelleX.{globalIsabelle => GIsabelle}
import GIsabelle.Ops
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.{App, Const}
import hashedcomputation.{Hash, HashTag}

// Implicits
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._
import GIsabelle.isabelleControl
import scala.concurrent.ExecutionContext.Implicits.global

/**
 * Expects subgoal: {A ⊓ R} c ~ d {B ⊓ R}
 * New subgaol:
 * - colocal_pred_qvars R fv(c1,d2)
 * - {A} c ~ d {B}
 *
 * Conditions:
 * - written classical variables of c,d (with index 1,2) do not occur in R
 */
case object FrameRuleTac extends Tactic {
  override val hash: Hash[FrameRuleTac.this.type] = HashTag()()

  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case AmbientSubgoal(_) => throw UserException("Expected qRHL judgment")
    case QRHLSubgoal(left, right, pre, post, assumptions) =>
      val (b, r) = post.isabelleTerm match {
        case App(App(Const(IsabelleConsts.inf, _), b2), r2) => (b2, r2)
        case _ => throw UserException(s"""Postcondition must be of the form "B ⊓ R", not $post""")
      }
      val rRich = RichTerm(GIsabelle.predicateT, r)

      val a = pre.isabelleTerm match {
        case App(App(Const(IsabelleConsts.inf, _), a2), r2) =>
          if (r2!=r)
            throw UserException(s"Rhs of precondition and rhs of postcondition must be equal ($rRich vs ${RichTerm(GIsabelle.predicateT, r2)})")
          a2
        case _ => throw UserException(s"""Precondition must be of the form "A ⊓ R", not $pre""")
      }

      val env = state.environment
      val leftVarUse = left.variableUse(env)
      val rightVarUse = right.variableUse(env)

      /** Classical vars in R */
      val rCVars = rRich.variables(env).classical

      /** Written classical vars in c (indexed) */
      val leftCW1 = leftVarUse.writtenClassical.map(_.index1)
      /** Written classical vars in c occurring in R  */
      val leftCWinter = rCVars.intersect(leftCW1)
      if (leftCWinter.nonEmpty)
        throw UserException(s"Rhs of postcondition ($rRich) and left program share written classical variable(s) ${leftCWinter.mkString(", ")}")

      val rightCW2 = rightVarUse.writtenClassical.map(_.index2)
      val rightCWinter = rCVars.intersect(rightCW2)
      if (rightCWinter.nonEmpty)
        throw UserException(s"Rhs of postcondition ($rRich) and right program share written classical variable(s) ${rightCWinter.mkString(", ")}")

      /** quantum variables in c,d (with index) */
      val qVars12 = leftVarUse.quantum.map(_.index1).union(rightVarUse.quantum.map(_.index2))
      val qVars12list = qVars12.toList.map { v => (v.variableName, v.valueTyp) }
      /** "colocal_pred_qvars R qVars12" */
      val colocality = AmbientSubgoal(RichTerm(Ops.colocalityOp(state.isabelle.context, r, qVars12list).retrieveNow))

      val qrhlSubgoal = QRHLSubgoal(left, right, RichTerm(GIsabelle.predicateT, a), RichTerm(GIsabelle.predicateT, b), assumptions)

      List(colocality, qrhlSubgoal)
  }

}