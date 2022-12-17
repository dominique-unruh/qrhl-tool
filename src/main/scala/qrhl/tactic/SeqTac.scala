package qrhl.tactic

import qrhl._
import qrhl.isabellex.IsabelleX
import qrhl.logic.ExpressionIndexed
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.pure.Term
import hashedcomputation.{Hash, HashTag, Hashable}
import hashedcomputation.Implicits._
import qrhl.isabellex.IsabelleX.globalIsabelle

case class SeqTac(left:Int, right:Int, inner:ExpressionIndexed, swap: Boolean = false)
  extends IsabelleTac[(Int, Int, Term)]("seq_tac", {
    ctx => (left,right,inner.term.isabelleTerm) }) {

  override def hash: Hash[SeqTac.this.type] =
    HashTag()(Hashable.hash(left), Hashable.hash(right), Hashable.hash(inner), Hashable.hash(swap))

  override def toString: String = s"seq${if (swap) "<->" else ""} $left $right"

  override def postprocess(state: State, goal: Subgoal, newGoals: List[Subgoal]): List[Subgoal] =
    if (swap) newGoals.reverse else newGoals

  override def check(state: State, goal: Subgoal, newGoals: List[Subgoal]): Unit = {
    if (newGoals.length!=2) throw UserException(s"Internal error: seq tactic returned ${newGoals.length} subgoals")
    if (newGoals.exists(!_.isInstanceOf[QRHLSubgoal])) throw UserException(s"Internal error: seq tactic returned subgoals that are not QRHL judgments")
  }

  override def precheck(state: State, goal: Subgoal): Unit =
    if (inner.rangeTyp != globalIsabelle.predicateT)
      throw UserException(s"Internal error: seq tactic got expression of invalid type ${IsabelleX.theContext.prettyTyp(inner.rangeTyp)}")
}
