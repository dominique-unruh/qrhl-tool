package qrhl.tactic

import info.hupel.isabelle.Operation
import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.{App, Const, Term, Typ}
import qrhl.isabelle.{Isabelle, IsabelleConsts, RichTerm}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException}

import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec

case object FrameRuleTac extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case AmbientSubgoal(_) => throw UserException("Expected qRHL judgment")
    case QRHLSubgoal(left, right, pre, post, assumptions) =>
      val (b, r) = post.isabelleTerm match {
        case App(App(Const(IsabelleConsts.inf, _), b2), r2) => (b2, r2)
        case _ => throw UserException(s"""Postcondition must be of the form "B ⊓ R", not $post""")
      }
      val rRich = RichTerm(Isabelle.predicateT, r)

      val a = pre.isabelleTerm match {
        case App(App(Const(IsabelleConsts.inf, _), a2), r2) =>
          if (r2!=r)
            throw UserException(s"Rhs of precondition and rhs of postcondition must be equal ($rRich vs ${RichTerm(Isabelle.predicateT, r2)})")
          a2
        case _ => throw UserException(s"""Precondition must be of the form "A ⊓ R", not $pre""")
      }

      val env = state.environment
      val leftVarUse = left.variableUse(env)
      val rightVarUse = right.variableUse(env)

      val rCVars = rRich.caVariables(env).classical

      val leftCW1 = leftVarUse.writtenClassical.map(_.index1)
      val leftCWinter = rCVars.intersect(leftCW1)
      if (leftCWinter.nonEmpty)
        throw UserException(s"Rhs of postcondition ($rRich) and left program share written classical variable(s) ${leftCWinter.mkString(", ")}")

      val rightCW2 = rightVarUse.writtenClassical.map(_.index2)
      val rightCWinter = rCVars.intersect(rightCW2)
      if (rightCWinter.nonEmpty)
        throw UserException(s"Rhs of postcondition ($rRich) and right program share written classical variable(s) ${rightCWinter.mkString(", ")}")

      val qVars12 = leftVarUse.quantum.map(_.index1).union(rightVarUse.quantum.map(_.index2))
      val qVars12list = qVars12.toList.map { v => (v.variableName, v.valueTyp) }
      val colocality = AmbientSubgoal(state.isabelle.isabelle.invoke(colocalityOp,
        (state.isabelle.contextId, r, qVars12list)))

      val qrhlSubgoal = QRHLSubgoal(left, right, RichTerm(Isabelle.predicateT, a), RichTerm(Isabelle.predicateT, b), assumptions)

      List(colocality, qrhlSubgoal)
  }

  val colocalityOp: Operation[(BigInt, Term, List[(String, Typ)]), RichTerm] = Operation.implicitly[(BigInt,Term,List[(String,Typ)]), RichTerm]("colocal_pred_qvars")
}