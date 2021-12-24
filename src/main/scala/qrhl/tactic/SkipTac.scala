package qrhl.tactic

import de.unruh.isabelle.pure.Abs
import hashedcomputation.{Hash, HashTag}

import java.io.PrintWriter
import qrhl.logic.Block
import qrhl._

// Implicits
import de.unruh.isabelle.mlvalue.Implicits._

object SkipTac extends IsabelleTac[Unit]("skip_tac_op", _ => ()) {
  /*override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case QRHLSubgoal(Block(),Block(),pre,post,assms) =>
      val pre2 = pre.encodeAsExpression(state.isabelle, indexed = true)
      val post2 = post.encodeAsExpression(state.isabelle, indexed = true)
      val ineq = Abs("mem", )
      List(AmbientSubgoal(pre.leq(post)).addAssumptions(assms))
    case QRHLSubgoal(_,_,_,_,_) =>
      throw UserException("Expected skip on both sides of the subgoal.")
    case AmbientSubgoal(_) =>
      throw UserException("Expected a qrhl subgoal.")
  }*/

  override def precheck(state: State, goal: Subgoal): Unit = goal match {
    case QRHLSubgoal(Block(),Block(),pre,post,assms) =>
    case QRHLSubgoal(_,_,_,_,_) =>
      throw UserException("Expected skip on both sides of the subgoal.")
    case AmbientSubgoal(_) =>
      throw UserException("Expected a qrhl subgoal.")
  }

  override def toString: String = "skip"

  override val hash: Hash[SkipTac.this.type] = HashTag()()
}
