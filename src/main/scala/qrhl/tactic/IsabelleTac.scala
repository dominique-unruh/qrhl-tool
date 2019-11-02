package qrhl.tactic

import info.hupel.isabelle.{Codec, Operation}
import info.hupel.isabelle.pure.Term
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.toplevel.Parser

abstract class IsabelleTac[A](operationName : String, arg : Isabelle.Context => A)(implicit codec : Codec[A]) extends Tactic {

  override def apply(state: State, goal: Subgoal): List[Subgoal] = {
    val ctx = state.isabelle
//    println("IsabelleTac",Isabelle.pretty(goal.toExpression(ctx).isabelleTerm))

    implicit val isabelle: Isabelle = ctx.isabelle
    implicit val _ : Codec[A] = codec
    import Isabelle.Thm.codec

    val operation : Operation[(A, Subgoal, Isabelle.Context), Option[(List[Subgoal],Isabelle.Thm)]] = {
      Operation.implicitly[(A, Subgoal, Isabelle.Context), Option[(List[Subgoal],Isabelle.Thm)]](operationName)
    }

    val (newGoals,thm) = ctx.isabelle.invoke(operation, (arg(ctx), goal, ctx)).getOrElse {
      throw UserException("tactic failed") }
//    val thm = if (thmId==0) null else new Isabelle.Thm(ctx.isabelle, thmId)

//    val newGoals = for (t <- goals) yield Subgoal(ctx, t)

    check(state, goal, newGoals)

    Subgoal.printOracles(thm)

    postprocess(state,goal,newGoals)
  }

  def check(state: State, goal: Subgoal, newGoals : List[Subgoal]): Unit = {}
  def postprocess(state: State, goal: Subgoal, newGoals : List[Subgoal]): List[Subgoal] = newGoals


  override def toString: String = f"IsabelleTac($operationName,$arg)"
}
