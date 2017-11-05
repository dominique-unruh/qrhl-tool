package qrhl.tactic


import info.hupel.isabelle.hol.HOLogic
import qrhl._
import qrhl.isabelle.Isabelle
import qrhl.logic.Expression

object TrueTac extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match{
    case AmbientSubgoal(exp : Expression) =>
      if (exp.isabelleTerm==HOLogic.True) Nil
      else throw UserException("""Tactic true expects a subgoal that is simply "true"""")
    case g : QRHLSubgoal =>
      if (g.assumptions.exists(_.isabelleTerm==HOLogic.False)) Nil
      else if (g.pre.isabelleTerm==Isabelle.predicate_bot || g.pre.isabelleTerm==Isabelle.predicate_0) Nil
      else throw UserException("""Expecting a QRHL subgoal with one assumption being "False" or the precondition being "bot" or "0"""")
  }

  override def toString: String = "true"
}
