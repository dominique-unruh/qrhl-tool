package qrhl.toplevel
import hashedcomputation.{Hash, HashTag, Hashable}
import qrhl.State

import java.io.PrintWriter

import hashedcomputation.Implicits._

case class FocusCommand(focusVariant: String) extends Command {
  override protected def act(state: State, output: PrintWriter): State = {
    state.focusOrUnfocus(focusVariant)
  }

  /** Must return a stable value */
  override def hash: Hash[FocusCommand.this.type] = HashTag()(Hashable.hash(focusVariant))
}
