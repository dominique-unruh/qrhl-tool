package qrhl.tactic


import info.hupel.isabelle.hol.HOLogic
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}

object TrueTac extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] =
    if (isTrivial(goal)) Nil
    else throw UserException("""Tactic true expects a subgoal that is simply "true", or a QRHL subgoal with one assumption being "False" or the precondition being "bot" or "0"""")

  def isTrivial(goal: Subgoal): Boolean = goal match{
    case AmbientSubgoal(exp : RichTerm) => exp.isabelleTerm==HOLogic.True
    case g : QRHLSubgoal =>
      g.assumptions.exists(_.isabelleTerm==HOLogic.False) ||
      g.pre.isabelleTerm==Isabelle.predicate_bot ||
      g.pre.isabelleTerm==Isabelle.predicate_0
  }

  override def toString: String = "true"
}
