package qrhl.tactic

import de.unruh.isabelle.mlvalue.Implicits._
import hashedcomputation.Implicits._
import hashedcomputation.{Hash, HashTag, Hashable}
import qrhl.{QRHLSubgoal, State, Subgoal}

case class SpTac(left:Int, right:Int)
  extends IsabelleTac[(Int,Int)]("sp_tac", { _ => (left,right) }) {

  assert(left >= 0, s"sp tactic must have nonnegative arguments (not left=$left)")
  assert(right >= 0, s"sp tactic must have nonnegative arguments (not right=$right)")

  override def hash: Hash[SpTac.this.type] = HashTag()(Hashable.hash(left), Hashable.hash(right))

  override def toString: String =
    s"sp($left left, $right right)"

  override def check(state: State, goal: Subgoal, newGoals: List[Subgoal]): Unit = {
    assert(newGoals.nonEmpty)
    assert(newGoals.last.isInstanceOf[QRHLSubgoal], newGoals.last)
  }
}
