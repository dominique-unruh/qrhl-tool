package qrhl.tactic

import java.io.PrintWriter
import qrhl._
import qrhl.isabellex.RichTerm
import qrhl.logic.{Block, ExpressionIndexed, Statement}

/** amount -1 means "all" */
abstract class WpBothStyleTac(leftAmount:Int=1, rightAmount:Int=1) extends Tactic {
  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case QRHLSubgoal(leftProg, rightProg, pre, post, assms) =>
      val leftAmount2 = if (leftAmount == -1) leftProg.statements.length else leftAmount
      val rightAmount2 = if (rightAmount == -1) rightProg.statements.length else rightAmount
      if (leftProg.statements.length < leftAmount2)
        throw UserException(s"Need at least ${leftAmount2} statement(s) on the left side")
      if (rightProg.statements.length < rightAmount2)
        throw UserException(s"Need at least ${rightAmount2} statement(s) on the right side")
      
      val lastL = leftProg.statements.takeRight(leftAmount2)
      val restL = leftProg.statements.dropRight(leftAmount2)
      val lastR = rightProg.statements.takeRight(rightAmount2)
      val restR = rightProg.statements.dropRight(rightAmount2)
      val (wp,subgoals) = getWP(state, Block.makeBlockIfNeeded(lastL), Block.makeBlockIfNeeded(lastR), post)
      subgoals.toList.map(_.addAssumptions(assms)) ::: List(QRHLSubgoal(Block(restL: _*), Block(restR: _*), pre, wp, assms))
    case _ => throw UserException(s"$this supported only for qRHL subgoals")
  }

  /** Returns a (preferably weakest) precondition for post given programs left/right.
    * @return (wp,assms), where wp is the precondition, and assms are potential additional subgoals that need to be proven
    */
  def getWP(state: State, left: Statement, right: Statement, post: ExpressionIndexed)(implicit output: PrintWriter) : (ExpressionIndexed, Seq[Subgoal])
}
