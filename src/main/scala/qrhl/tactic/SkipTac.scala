package qrhl.tactic

import qrhl.logic.Block
import qrhl._

/**
  * Created by unruh on 7/9/17.
  */
object SkipTac extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(Block(),Block(),pre,post) =>
      List(AmbientSubgoal(pre.leq(post)))
  }

  override def toString: String = "skip"
}
