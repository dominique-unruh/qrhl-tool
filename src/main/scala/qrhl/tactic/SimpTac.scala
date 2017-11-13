package qrhl.tactic

import org.log4s
import qrhl._
import qrhl.toplevel.Parser

import scala.collection.immutable.Nil

case class SimpTac(facts:List[String]) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] =
    state.isabelle match {
      case Some(isa) =>
        val newGoal = goal.simplify(isa,facts)
        if (TrueTac.isTrivial(newGoal)) Nil
        else List(newGoal)
      case None => throw UserException(Parser.noIsabelleError)
    }

  override def toString: String = "simplify"
}

object SimpTac {
  private val logger = log4s.getLogger
}
