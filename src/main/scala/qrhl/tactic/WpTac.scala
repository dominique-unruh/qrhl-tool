package qrhl.tactic

import info.hupel.isabelle.Operation
import info.hupel.isabelle.pure.{Term, Typ => ITyp}
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.logic._
import qrhl.{QRHLSubgoal, State, Subgoal, UserException}

import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec

case class WpTac(left:Int, right:Int)
  extends IsabelleTac[(BigInt,BigInt)]("wp_tac", { _ => (left,right) }) {

  assert(left >= 0, s"wp tactic must have nonnegative arguments (not left=$left)")
  assert(right >= 0, s"wp tactic must have nonnegative arguments (not right=$right)")

  override def toString: String =
    s"wp($left left, $right right)"

  override def check(state: State, goal: Subgoal, newGoals: List[Subgoal]): Unit = {
    assert(newGoals.length==1, newGoals.length)
    assert(newGoals.head.isInstanceOf[QRHLSubgoal], newGoals.head)
  }
}
