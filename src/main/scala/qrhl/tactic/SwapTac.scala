package qrhl.tactic

import org.log4s
import qrhl._
import qrhl.logic.{Block, Environment, Statement, Variable}


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
    val (c1,w1,q1,_,_) = Block(block1:_*).cwqapVariables(recurse=true, environment = env)
    val (c2,w2,q2,_,_) = Block(block2:_*).cwqapVariables(recurse=true, environment = env)

    def error(msg: String) =
      throw UserException(s"Cannot swap\n    ${block1.mkString(" ")}\nand\n    ${block2.mkString(" ")},\n$msg")

    def vars(vars:Seq[Variable]) : String =
      vars.map(_.name).mkString(", ")

    val qshared = q1.intersect(q2)
    if (qshared.nonEmpty)
      error(s"they have shared quantum variables (${vars(qshared)})")

    val wshared = w1.intersect(w2)
    if (wshared.nonEmpty)
      error(s"they have shared written classical variables (${vars(wshared)})")

    val w1r2 = w1.intersect(c2)
    if (w1r2.nonEmpty)
      error(s"the first block writes classical variables that the second reads (${vars(w1r2)})")

    val w2r1 = w2.intersect(c1)
    if (w2r1.nonEmpty)
      error(s"the first block reads classical variables that the second writes (${vars(w2r1)})")
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
