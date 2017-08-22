package qrhl.tactic

import info.hupel.isabelle.hol.HOLogic
import org.log4s
import qrhl._
import qrhl.logic.Expression
import qrhl.toplevel.Parser

case class SimpTac(facts:List[String]) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] =
    state.isabelle match {
      case Some(isa) => goal match {
        case AmbientSubgoal(expr) => List(AmbientSubgoal(expr.simplify(isa,facts)))

        case QRHLSubgoal(left, right, pre, post, assms) =>
          if (assms.nonEmpty) SimpTac.logger.warn("Ignoring assumptions in simplification")
          val assms2: List[Expression] =
            assms.map(_.simplify(isa,facts)).filter(_.isabelleTerm!=HOLogic.True)
          List(QRHLSubgoal(left, right, pre.simplify(isa,facts), post.simplify(isa,facts), assms2))
      }
      case None => throw UserException(Parser.noIsabelleError)
    }

  override def toString: String = "simplify"
}

object SimpTac {
  private val logger = log4s.getLogger
}
