package qrhl.tactic

import info.hupel.isabelle.Operation
import info.hupel.isabelle.pure.Term
import qrhl._
import qrhl.isabelle.Isabelle
import qrhl.logic.Expression
import qrhl.toplevel.Parser


abstract class IsabelleTac[A](operation : Operation[(A, Term, BigInt), Option[List[Term]]], arg : Isabelle.Context => A) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = {
    val ctx = state.isabelle
//    println("IsabelleTac",Isabelle.pretty(goal.toExpression(ctx).isabelleTerm))
    val goals = ctx.isabelle.invoke(operation, (arg(ctx), goal.toExpression(ctx).isabelleTerm, ctx.contextId)).getOrElse {
      throw UserException("tactic failed")
    }
//println("IsabelleTac goals",goals.map(Isabelle.pretty))
    val newGoals = for (t <- goals) yield Subgoal(ctx, Expression(Isabelle.boolT, t))
//println("IsabelleTac newGoals",newGoals)
    check(state, goal, newGoals)
    newGoals
  }

  def check(state: State, goal: Subgoal, newGoals : List[Subgoal]): Unit = {}

  override def toString: String = f"IsabelleTac($operation,$arg)"
}
