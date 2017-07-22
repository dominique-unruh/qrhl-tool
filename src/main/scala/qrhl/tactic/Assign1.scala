package qrhl.tactic

import qrhl._
import qrhl.logic.{Assign, Block, Expression, Statement}

@deprecated
object Assign1 extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(Block(Assign(v,e)),Block(),pre,post) =>
      val env = state.environment
      List(AmbientSubgoal(pre.leq(post.map(Expression.substitute(v.index1.name,e.index1(env).isabelleTerm,_)))))
    case _ =>
      throw UserException("Expected a qRHL subgoal")
  }

  override val toString: String = "assign1"
}

@deprecated
object Assign2 extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(Block(),Block(Assign(v,e)),pre,post) =>
      val env = state.environment
      List(AmbientSubgoal(pre.leq(post.substitute(v.index2,e.index2(env)))))
    case _ =>
      throw UserException("Expected a qRHL subgoal")
  }

  override val toString: String = "assign2"
}

//@deprecated
//case class AssignTac(left:Boolean) extends WpStyleTac(left=left) {
//  override def getWP(state: State, left: Boolean, statement: Statement, post: Expression): Expression = statement match {
//    case Assign(v,e) =>
//      val env = state.environment
//      post.substitute(v.index(left=left),e.index(env, left=left))
//    case _ => throw UserException(s"Expected am assign statement as last expression on the ${if (left) "left" else "right"} side")
//  }
//
//  override val toString: String = if (left) "assign(left)" else "assign(right)"
//}
//
//object AssignTac {
//  def getWP(state: State, left: Boolean, statement: Statement, post: Expression): _root_.qrhl.logic.Expression = ???
//}