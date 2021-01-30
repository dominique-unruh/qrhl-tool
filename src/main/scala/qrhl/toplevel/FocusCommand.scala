package qrhl.toplevel
import hashedcomputation.{Hash, HashTag, Hashable}
import qrhl.{State, SubgoalSelector}

import java.io.PrintWriter
import hashedcomputation.Implicits._

case class FocusCommand(selector: Option[SubgoalSelector], label: String) extends Command {
  override protected def act(state: State, output: PrintWriter): State = {
    state.focusOrUnfocus(selector, label)
  }

  override def hash: Hash[FocusCommand.this.type] = HashTag()(Hashable.hash(selector), Hashable.hash(label))
}
