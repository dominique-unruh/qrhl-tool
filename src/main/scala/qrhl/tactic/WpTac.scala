package qrhl.tactic

import qrhl.{QRHLSubgoal, State, Subgoal}

import isabelle.control.MLValue.Implicits._

case class WpTac(left:Int, right:Int)
  extends IsabelleTac[(Int,Int)]("wp_tac", { _ => (left,right) }) {

  assert(left >= 0, s"wp tactic must have nonnegative arguments (not left=$left)")
  assert(right >= 0, s"wp tactic must have nonnegative arguments (not right=$right)")

  override def toString: String =
    s"wp($left left, $right right)"

  override def check(state: State, goal: Subgoal, newGoals: List[Subgoal]): Unit = {
    assert(newGoals.length==1, newGoals.length)
    assert(newGoals.head.isInstanceOf[QRHLSubgoal], newGoals.head)
  }
}
