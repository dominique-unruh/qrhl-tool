package qrhl.tactic

import info.hupel.isabelle.Operation
import info.hupel.isabelle.pure.Term
import qrhl._
import qrhl.logic.Expression
import qrhl.toplevel.Parser


abstract class IsabelleTac[A](operation : Operation[(A, Term, BigInt), Option[List[Term]]], arg : A) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] =
  //    goal match {
  //      case _: QRHLSubgoal => throw UserException("Expected an ambient logic subgoal")
  //      case AmbientSubgoal(expr) =>
    state.isabelle match {
      case Some(isa) =>
        val ctx = state.isabelle.get
        val goals = ctx.isabelle.invoke(operation, (arg, goal.toExpression.isabelleTerm, ctx.contextId)).get
        for (t <- goals) yield AmbientSubgoal(Expression(isa,state.boolT,t))
      case None => throw UserException(Parser.noIsabelleError)
    }
  //    }

  override def toString: String = f"IsabelleTac($operation,$arg)"
}
