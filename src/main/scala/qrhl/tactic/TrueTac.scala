package qrhl.tactic


import info.hupel.isabelle.hol.HOLogic
import qrhl._
import qrhl.logic.Expression

object TrueTac extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match{
    case AmbientSubgoal(exp : Expression) =>
      if (exp.isabelleTerm==HOLogic.True) Nil
      else throw UserException("""Tactic true expects a subgoal that is simply "true"""")
    case _ : QRHLSubgoal =>
      throw UserException("""Tactic true expects a subgoal that is simply "true" (not a qRHL judgement)""")
  }

  override def toString: String = "true"
}
