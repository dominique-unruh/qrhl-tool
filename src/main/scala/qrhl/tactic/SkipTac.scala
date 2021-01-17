package qrhl.tactic

import hashedcomputation.{Hash, HashTag}

import java.io.PrintWriter
import qrhl.logic.Block
import qrhl._

/**
  * Created by unruh on 7/9/17.
  */
object SkipTac extends Tactic {
  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case QRHLSubgoal(Block(),Block(),pre,post,assms) =>
      List(AmbientSubgoal(pre.leq(post)).addAssumptions(assms))
    case QRHLSubgoal(_,_,_,_,_) =>
      throw UserException("Expected skip on both sides of the subgoal.")
    case AmbientSubgoal(_) =>
      throw UserException("Expected a qrhl subgoal.")
  }

  override def toString: String = "skip"

  override val hash: Hash[SkipTac.this.type] = HashTag()()
}
