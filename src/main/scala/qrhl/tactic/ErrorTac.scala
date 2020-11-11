package qrhl.tactic

import java.io.PrintWriter

import qrhl.{State, Subgoal, Tactic, UserException}

case class ErrorTac(msg:String) extends Tactic {
  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] =
    throw UserException(msg)
}
