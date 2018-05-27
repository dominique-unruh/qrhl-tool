package qrhl.tactic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.{Free, Term}
import qrhl._
import qrhl.isabelle.Isabelle
import qrhl.logic.Expression

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
        throw UserException(s"Variable $variable has type ${state.isabelle.prettyTyp(varTyp)}, but expression has type ${state.isabelle.prettyTyp(expr.typ)}")

      for (x <- expr.variables)
        if (!state.environment.variableExistsForPredicate(x))
          throw UserException(s"Undeclared (or non-indexed) variable $x in precondition")


      val caseExpr : Term = Isabelle.classical_subspace $
        (HOLogic.equ(varTyp) $ expr.isabelleTerm $ Free(variable,varTyp))
      val pre2 = Isabelle.predicate_inf $ caseExpr $ pre.isabelleTerm
      val pre3 = Expression(Isabelle.predicateT, pre2)


      List(QRHLSubgoal(left,right,pre3,post,assms))
    case _ : AmbientSubgoal => throw UserException("Expected a QRHL subgoal")
  }
}
