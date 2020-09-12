package qrhl.tactic

import qrhl._
import qrhl.isabellex.{IsabelleX, RichTerm}
import IsabelleX.{globalIsabelle => GIsabelle}
import isabelle.pure.{Free, Term}

// Implicits
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl
import scala.concurrent.ExecutionContext.Implicits._

case class CaseTac(variable:String, expr:RichTerm) extends Tactic {
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


      val caseExpr : Term = GIsabelle.classical_subspace(
        GIsabelle.mk_eq(expr.isabelleTerm, Free(variable,varTyp)))
      val pre2 = GIsabelle.predicate_inf $ caseExpr $ pre.isabelleTerm
      val pre3 = RichTerm(GIsabelle.predicateT, pre2)


      List(QRHLSubgoal(left,right,pre3,post,assms))
    case _ : AmbientSubgoal => throw UserException("Expected a QRHL subgoal")
  }
}
