package qrhl.tactic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.{Const, Free, Term}
import info.hupel.isabelle.{ml, pure}
import qrhl._
import qrhl.isabelle.Isabelle
import qrhl.logic.{Expression, Variable}

case class CaseTac(variable:String, expr:Expression) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(left,right,pre,post,assms) =>

      if (goal.containsAmbientVar(variable))
        throw UserException(s"Variable $variable already contained in goal")

      if (expr.variables.contains(variable))
        throw UserException(s"Variable $variable already contained in supplied expression $expr")

      state.environment.variableUsedInPrograms(variable) match {
        case None =>
        case Some(prog) => throw UserException(s"Variable $variable already used in program $prog")
      }

      val varTyp = state.environment.ambientVariables(variable)
      if (varTyp != expr.typ)
        throw UserException(s"Variable $variable has type $varTyp, but expression has type ${expr.typ}")

      for (x <- expr.variables)
        if (!state.environment.variableExistsForPredicate(x))
          throw UserException(s"Undeclared (or non-indexed) variable $x in precondition")


      val caseExpr : Term = Isabelle.classical_subspace $
        (HOLogic.equ(varTyp.isabelleTyp) $ expr.isabelleTerm $ Free(variable,varTyp.isabelleTyp))
      val pre2 = Isabelle.predicate_inf $ caseExpr $ pre.isabelleTerm
      val pre3 = Expression(pre.isabelle, state.predicateT, pre2)


      List(QRHLSubgoal(left,right,pre3,post,assms))
    case _ : AmbientSubgoal => throw UserException("Expected a QRHL subgoal")
  }
}
