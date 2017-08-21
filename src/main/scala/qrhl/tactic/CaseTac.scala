package qrhl.tactic

import qrhl._
import qrhl.logic.{Expression, Variable}

case class CaseTac(variable:String, expr:Expression) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(left,right,pre,post) =>

      if (goal.containsAmbientVar(variable))
        throw UserException(s"Variable $variable already contained in goal")

      state.environment.variableUsedInPrograms(variable) match {
        case None =>
        case Some(prog) => throw UserException(s"Variable $variable already used in program $prog")
      }

      val varTyp = state.environment.ambientVariables(variable)
      if (varTyp != expr.typ)
        throw UserException(s"Variable $variable has type $varTyp, but expression has type ${expr.typ}")

      ???
    case _ : AmbientSubgoal => throw UserException("Expected a QRHL subgoal")
  }
}
