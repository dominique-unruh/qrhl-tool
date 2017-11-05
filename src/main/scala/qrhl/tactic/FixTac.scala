package qrhl.tactic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.Term
import info.hupel.isabelle.{ml, pure}
import qrhl._
import qrhl.logic.{Expression, Typ}

case class FixTac(variable:String) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(left,right,pre,post,assms) =>
      throw UserException("Expecting an ambient logic goal")
    case AmbientSubgoal(expr) =>
      if (goal.containsAmbientVar(variable))
        throw UserException(s"Variable $variable already contained in goal")

      val varTyp = state.environment.ambientVariables.getOrElse(variable,
        throw UserException(s"$variable is not an ambient variable"))

      val lit = ml.Expr.uncheckedLiteral[Term => String => (Term,pure.Typ)]("QRHL.fixTac")
      val mlExpr = lit(expr.isabelleTerm)(implicitly) (variable)
      val (result,varTyp2) = state.isabelle.get.runExpr(mlExpr)
      val varTyp3 = Typ(state.isabelle.get, varTyp2)

      if (varTyp!=varTyp3)
        throw UserException(s"Please use a variable of type $varTyp3 ($variable has type $varTyp)")

      List(AmbientSubgoal(Expression(state.isabelle.get, state.predicateT, result)))
  }
}
