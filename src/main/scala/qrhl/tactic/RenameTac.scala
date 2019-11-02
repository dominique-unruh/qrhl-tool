package qrhl.tactic

import info.hupel.isabelle.Operation
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException}
import qrhl.logic.{CVariable, QVariable, Variable}
import info.hupel.isabelle.pure.Term

import RichTerm.term_tight_codec
import RichTerm.typ_tight_codec

case class RenameTac(left: Boolean, right: Boolean, a: Variable, b: Variable) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case _ : AmbientSubgoal =>
      throw UserException("Expected qRHL subgoal")
    case QRHLSubgoal(leftProg, rightProg, pre, post, assumptions) =>
      val env = state.environment
      if (a==b)
        throw UserException(s"Trying to replace ${a.name} by itself")
      if (a.valueTyp != b.valueTyp)
        throw UserException("The two variables need to have the same type")

      (a,b) match {
        case (a : CVariable, b : CVariable) =>
          val newLeft = if (left) leftProg.renameCVariable(env, a, b) else leftProg
          val newRight = if (right) rightProg.renameCVariable(env, a, b) else rightProg

          def swap(predicate: RichTerm) = {
            val pred1 = if (left) predicate.renameCVariable(a.index1, b.index1) else predicate
            val pred2 = if (right) pred1.renameCVariable(a.index2, b.index2) else pred1
            pred2
          }

          val newPre = swap(pre)
          val newPost = swap(post)

          val newQrhl = QRHLSubgoal(newLeft, newRight, newPre, newPost, assumptions)

          List(newQrhl)
        case (a : QVariable, b : QVariable) =>
          val newLeft = if (left) leftProg.renameQVariable(env, a, b) else leftProg
          val newRight = if (right) rightProg.renameQVariable(env, a, b) else rightProg

          def swap(predicate: RichTerm) = {
            val pred1 = if (left) Isabelle.swap_variables_subspace(a.index1.variableTerm, b.index1.variableTerm, predicate.isabelleTerm) else predicate.isabelleTerm
            val pred2 = if (right) Isabelle.swap_variables_subspace(a.index2.variableTerm, b.index2.variableTerm, pred1) else pred1
            val pred3 = state.isabelle.isabelle.invoke(RenameTac.swapOp, (state.isabelle.contextId, pred2))
            pred3
          }

          val newPre = swap(pre)
          val newPost = swap(post)

          val newQrhl = QRHLSubgoal(newLeft, newRight, newPre, newPost, assumptions)

          List(newQrhl)
        case  (_ : CVariable, _ : QVariable) =>
          throw UserException("You cannot rename classical variables into quantum variables")
        case  (_ : QVariable, _ : CVariable) =>
          throw UserException("You cannot rename quantum variables into classical variables")
      }
  }
}

object RenameTac {
  val swapOp: Operation[(BigInt, Term), RichTerm] = Operation.implicitly[(BigInt,Term),RichTerm]("swap_variables_conv")
}