package qrhl.tactic

import qrhl._
import qrhl.logic.{Block, Environment}


case class SwapTac(left:Boolean, number:Int=1) extends Tactic {
  if (number < 1)
    throw UserException(s"swap tactic must get numeric argument >=1, not $number")

  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(l,r,pre,post,assms) =>
      val env = state.environment
      List(QRHLSubgoal(
        if (left) swap(env,l) else l,
        if (!left) swap(env,r) else r,
        pre, post, assms))
    case _ =>
      throw UserException("Expected qRHL goal")
  }

  def swap(env:Environment, prog: Block) : Block = {
    if (prog.length<number+1)
      throw UserException(s"Program must have at least ${number+1} statements (on top level)")
    val (rest,rotate) = prog.statements.splitAt(prog.length-number-1)
    val last = rotate.last
    val jump = rotate.dropRight(1)
    val shared = last.variablesAll(env).intersect(Block(jump:_*).variablesAll(env))
    if (shared.nonEmpty)
      throw UserException(s"Cannot swap $last and ${jump.mkString(" ")}, they have shared variables (${shared.mkString(", ")})")
    Block(rest ++ (last :: jump) : _*)
  }
}
