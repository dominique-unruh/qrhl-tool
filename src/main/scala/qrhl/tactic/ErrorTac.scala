package qrhl.tactic

import hashedcomputation.{Hash, HashTag, Hashable}

import java.io.PrintWriter
import qrhl.{State, Subgoal, Tactic, UserException}
import hashedcomputation.Implicits._

case class ErrorTac(msg:String) extends Tactic {
  override def hash: Hash[ErrorTac.this.type] = HashTag()(Hashable.hash(msg))

  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] =
    throw UserException(msg)
}
