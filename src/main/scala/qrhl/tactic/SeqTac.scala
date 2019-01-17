package qrhl.tactic

import info.hupel.isabelle.pure.Term
import info.hupel.isabelle.{Operation, pure}
import qrhl._
import qrhl.isabelle.RichTerm
import qrhl.logic.Block

import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec

@deprecated("Use SeqTac","now")
case class SeqTacOLD(left:Int, right:Int, inner:RichTerm) extends Tactic {
  assert(left>=0)
  assert(right>=0)
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(leftProg,rightProg,pre,post,assms) =>
      if (leftProg.length < left)
        throw UserException(s"Left program contains ${leftProg.length} statements, but we try to split after the ${left}th")
      if (rightProg.length < right)
        throw UserException(s"Right program contains ${rightProg.length} statements, but we try to split after the ${right}th")
      val left1 = Block(leftProg.statements.take(left):_*)
      val left2 = Block(leftProg.statements.drop(left):_*)
      val right1 = Block(rightProg.statements.take(right):_*)
      val right2 = Block(rightProg.statements.drop(right):_*)
      List(
        QRHLSubgoal(left1,right1,pre,inner,assms),
        QRHLSubgoal(left2,right2,inner,post,assms)
      )
    case _ => throw UserException("Expected a qRHL subgoal")
  }
}

case class SeqTac(left:Int, right:Int, inner:RichTerm)
  extends IsabelleTac[(BigInt, BigInt, RichTerm)]("seq_tac", { ctx => (BigInt(left),BigInt(right),inner.encodeAsExpression(ctx) /* TODO: encodeAsExpression should be done on Isabelle side */) }) {
  override def toString: String = s"seq $left $right"

  override def check(state: State, goal: Subgoal, newGoals: List[Subgoal]): Unit = {
    if (newGoals.length!=2) throw UserException(s"Internal error: seq tactic returned ${newGoals.length} subgoals")
    if (newGoals.exists(!_.isInstanceOf[QRHLSubgoal])) throw UserException(s"Internal error: seq tactic returned subgoals that are not QRHL judgments")
  }
}

object SeqTac {
//  val seqTacOp: Operation[((BigInt, BigInt, Term), Term, BigInt), Option[(List[RichTerm],BigInt)]] =
//    Operation.implicitly[((BigInt,BigInt,Term),Term,BigInt), Option[(List[RichTerm],BigInt)]]("seq_tac")
}