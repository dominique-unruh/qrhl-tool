package qrhl.tactic

import org.log4s
import qrhl._
import qrhl.logic.{Block, Environment}


case class SwapTac(left:Boolean, numStatements:Int, steps:Int) extends Tactic {
  if (steps < 1)
    throw UserException(s"swap tactic must get numeric argument >=1, not $steps")
  if (numStatements < 1)
    throw UserException(s"swap tactic must get numeric argument >=1, not $numStatements")

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
    SwapTac.logger.debug(this.toString)
    if (prog.length<steps+1)
      throw UserException(s"Program must have at least ${steps+1} statements (on top level)")
    val (rest,rotate) = prog.statements.splitAt(prog.length-steps-numStatements)
    val (jump,last) = rotate.splitAt(steps)
    SwapTac.logger.debug(s"$jump")
    SwapTac.logger.debug(s"$last")
    val shared = Block(last:_*).variablesAll(env).intersect(Block(jump:_*).variablesAll(env))
    if (shared.nonEmpty)
      throw UserException(s"Cannot swap ${last.mkString(" ")} and ${jump.mkString(" ")}, they have shared variables (${shared.mkString(", ")})")
    Block(rest ++ (last ::: jump) : _*)
  }
}


object SwapTac {
  private val logger = log4s.getLogger
}