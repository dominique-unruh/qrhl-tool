package qrhl.tactic

import org.log4s
import qrhl.isabellex.IsabelleX
import qrhl.{State, Subgoal, Tactic, UserException}
import de.unruh.isabelle.mlvalue.Implicits._
import hashedcomputation.{Hash, HashTag, Hashable}
import hashedcomputation.Implicits._

case class IsaTac(method:String, force:Boolean) extends IsabelleTac[String]("apply_method",
  { _ => IsabelleX.symbols.unicodeToSymbols(method) }) {
  override def toString: String = "isabelle method "+method

  override def check(state: State, goal: Subgoal, newGoals: List[Subgoal]): Unit = {
    if (force && newGoals.nonEmpty)
      throw UserException(s"$this failed to fully solve subgoal. New subgoals: $newGoals")
  }

  override def hash: Hash[IsaTac.this.type] =
    HashTag()(Hashable.hash(method), Hashable.hash(force))
}
