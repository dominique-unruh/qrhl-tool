package qrhl.tactic

import info.hupel.isabelle.Operation
import info.hupel.isabelle.pure.Term
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.toplevel.Parser

abstract class IsabelleTac[A](operation : Operation[(A, Term, BigInt), Option[(List[RichTerm],BigInt)]], arg : Isabelle.Context => A) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = {
    val ctx = state.isabelle
//    println("IsabelleTac",Isabelle.pretty(goal.toExpression(ctx).isabelleTerm))
    val (goals,thmId) = ctx.isabelle.invoke(operation, (arg(ctx), goal.toTerm(ctx).isabelleTerm, ctx.contextId)).getOrElse {
      throw UserException("tactic failed") }
    val thm = if (thmId==0) null else new Isabelle.Thm(ctx.isabelle, thmId)

    val newGoals = for (t <- goals) yield Subgoal(ctx, t)

    check(state, goal, newGoals)

    if (thm!=null) Subgoal.printOracles(thm)

    newGoals
  }

  def check(state: State, goal: Subgoal, newGoals : List[Subgoal]): Unit = {}

  override def toString: String = f"IsabelleTac($operation,$arg)"
}
