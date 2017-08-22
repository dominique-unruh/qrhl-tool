package qrhl.tactic

import qrhl._
import qrhl.logic.{Block, Environment}

case class SwapTac(left:Boolean) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(l,r,pre,post,assms) =>
      val env = state.environment
      List(QRHLSubgoal(if (left) swap(env,l) else l, if (!left) swap(env,r) else r, pre, post,assms))
    case _ =>
      throw UserException("Expected qRHL goal")
  }

  def swap(env:Environment, prog: Block) : Block = {
    if (prog.length<2)
      throw UserException("Program must have at least two statements (on top level)")
    val (rest,List(a,b)) = prog.statements.splitAt(prog.length-2)
    val shared = a.variablesAll(env).intersect(b.variablesAll(env))
    if (shared.nonEmpty)
      throw UserException(s"Cannot swap $a and $b, they have shared variables (${shared.mkString(", ")})")
    Block(rest ++ Seq(b,a) : _*)
  }
}
