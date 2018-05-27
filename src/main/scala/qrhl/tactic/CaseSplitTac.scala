package qrhl.tactic

import info.hupel.isabelle.hol.HOLogic
import qrhl.logic.Expression
import qrhl._

case class CaseSplitTac(expr:Expression) extends Tactic {
  assert(expr.typ==HOLogic.boolT)

  override def apply(state: State, goal: Subgoal): List[Subgoal] = {
    if (goal.isInstanceOf[QRHLSubgoal])
      for (x <- expr.variables)
        if (!state.environment.ambientVariables.contains(x))
          throw UserException(s"When apply case split to QRHL goal, the provided Boolean expression must contain only ambient variables (not $x)")

    List(
      goal.addAssumption(expr),
      goal.addAssumption(expr.not)
    )
  }
}
