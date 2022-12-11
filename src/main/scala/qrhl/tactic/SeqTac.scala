package qrhl.tactic

import qrhl._
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.logic.Block
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.pure.Term
import hashedcomputation.{Hash, HashTag, Hashable}
import hashedcomputation.Implicits._
import qrhl.isabellex.IsabelleX.globalIsabelle

/*@deprecated("Use SeqTac","now")
case class SeqTacOLD(left:Int, right:Int, inner:RichTerm) extends Tactic {
  assert(left>=0)
  assert(right>=0)
  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
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
}*/

case class SeqTac(left:Int, right:Int, inner:RichTerm, swap: Boolean = false)
  extends IsabelleTac[(Int, Int, Term)]("seq_tac", {
    ctx => (left,right,inner.encodeAsExpression(ctx, indexed=true).isabelleTerm) }) {

  override def hash: Hash[SeqTac.this.type] =
    HashTag()(Hashable.hash(left), Hashable.hash(right), Hashable.hash(inner), Hashable.hash(swap))

  override def toString: String = s"seq${if (swap) "<->" else ""} $left $right"

  override def postprocess(state: State, goal: Subgoal, newGoals: List[Subgoal]): List[Subgoal] =
    if (swap) newGoals.reverse else newGoals

  override def check(state: State, goal: Subgoal, newGoals: List[Subgoal]): Unit = {
    if (newGoals.length!=2) throw UserException(s"Internal error: seq tactic returned ${newGoals.length} subgoals")
    if (newGoals.exists(!_.isInstanceOf[QRHLSubgoal])) throw UserException(s"Internal error: seq tactic returned subgoals that are not QRHL judgments")
  }

  override def precheck(state: State, goal: Subgoal): Unit =
    if (inner.typ != globalIsabelle.predExpressionT) throw UserException(s"Internal error: seq tactic got expression of invalid type ${IsabelleX.theContext.prettyTyp(inner.typ)}")
}

object SeqTac {
//  val seqTacOp: Operation[((BigInt, BigInt, Term), Term, BigInt), Option[(List[RichTerm],BigInt)]] =
//    Operation.implicitly[((BigInt,BigInt,Term),Term,BigInt), Option[(List[RichTerm],BigInt)]]("seq_tac")
}