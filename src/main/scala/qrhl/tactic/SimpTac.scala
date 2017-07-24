package qrhl.tactic

import qrhl._
import qrhl.toplevel.Parser

object SimpTac extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] =
    state.isabelle match {
      case Some(isa) => goal match {
        case AmbientSubgoal(expr) => List(AmbientSubgoal(expr.simplify(isa)))
        case QRHLSubgoal(left, right, pre, post) => List(QRHLSubgoal(left, right, pre.simplify(isa), post.simplify(isa)))
      }
      case None => throw UserException(Parser.noIsabelleError)
    }

  override def toString: String = "simplify"
}
