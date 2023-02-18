package qrhl.toplevel

class OutOfBandCommand

case class UndoCommand(steps: Int) extends OutOfBandCommand {
  assert (steps > 0, "Undo command must have positive number of steps.")

  override def toString: String = s"undo $steps"
}

class OptionCommand extends OutOfBandCommand

case class SillyTestOptionCommand() extends OptionCommand