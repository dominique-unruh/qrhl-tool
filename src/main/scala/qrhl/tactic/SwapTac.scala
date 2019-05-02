package qrhl.tactic

import org.log4s
import qrhl._
import qrhl.logic.{Block, Environment, Statement}


case class SwapTac(left:Boolean, range:SwapTac.Range, steps:Int) extends Tactic {
  if (steps < 1)
    throw UserException(s"swap tactic must get numeric argument >=1, not $steps")

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

  private def checkSwappable(env: Environment, block1 : List[Statement], block2: List[Statement]): Unit = {
    val shared = Block(block1:_*).variablesAll(env).intersect(Block(block2:_*).variablesAll(env))
    if (shared.nonEmpty)
      throw UserException(s"Cannot swap ${block1.mkString(" ")} and ${block2.mkString(" ")}, they have shared variables (${shared.mkString(", ")})")
  }

  def swap(env:Environment, prog: Block) : Block = {
    SwapTac.logger.debug(this.toString)

    val (before,toMove,after) = range.split(prog)

    if (before.length<steps)
      throw UserException(s"Program must have at least ${steps+1} statements before the specified range (not ${before.length})")

    val (before1, before2) = before.splitAt(before.length-steps)

    checkSwappable(env, toMove, before2)

    Block(before1 ::: toMove ::: before2 ::: after : _*)
  }
}


object SwapTac {
  private val logger = log4s.getLogger

  sealed trait Range {
    def split(prog:Block) : (List[Statement], List[Statement], List[Statement])
  }
  final case class FinalRange(numStatements:Int) extends Range {
    assert(numStatements>0)

    override def split(prog: Block): (List[Statement], List[Statement], List[Statement]) = {
      if (prog.length < numStatements)
        throw UserException(s"You are trying to move the last $numStatements but program has only ${prog.length} statements")
      val (before,range) = prog.statements.splitAt(prog.length-numStatements)
      (before,range,Nil)
    }
  }
  final case class MiddleRange(start:Int, end:Int) extends Range {
    if (start<=0)
      throw UserException(s"Start of range must be >=1 (not $start)")
    if (end<start)
      throw UserException(s"Start of range ($start) < end of range ($end)")

    override def split(prog: Block): (List[Statement], List[Statement], List[Statement]) = {
      if (end>prog.length)
        throw UserException(s"End of range is $end, but program has only ${prog.length} statements")
      val (before,rangeEnd) = prog.statements.splitAt(start-1)
      val (range,endBlock) = rangeEnd.splitAt(end-start+1)
      (before,range,endBlock)
    }
  }
}
