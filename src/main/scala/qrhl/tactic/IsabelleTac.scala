package qrhl.tactic

import qrhl._

/**
  * Created by unruh on 7/8/17.
  */
case class IsabelleTac(name:String) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case AmbientSubgoal(e) => Nil
    case _ => throw new UserException("Expected an ambient logic subgoal")
  }
}
