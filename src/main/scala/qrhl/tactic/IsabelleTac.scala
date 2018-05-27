package qrhl.tactic

import info.hupel.isabelle.Operation
import info.hupel.isabelle.pure.Term
import qrhl._
import qrhl.isabelle.Isabelle
import qrhl.logic.Expression
import qrhl.toplevel.Parser


abstract class IsabelleTac[A](operation : Operation[(A, Term, BigInt), Option[List[Term]]], arg : Isabelle.Context => A) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] =
  //    goal match {
  //      case _: QRHLSubgoal => throw UserException("Expected an ambient logic subgoal")
  //      case AmbientSubgoal(expr) =>
    state.isabelle match {
      case Some(isa) =>
        val ctx = state.isabelle.get
        val goals = ctx.isabelle.invoke(operation, (arg(isa), goal.toExpression(isa).isabelleTerm, ctx.contextId)).getOrElse {
          throw UserException("tactic failed")
        }
        for (t <- goals) yield Subgoal(isa, Expression(Isabelle.boolT,t))
      case None => throw UserException(Parser.noIsabelleError)
    }
  //    }

  override def toString: String = f"IsabelleTac($operation,$arg)"
}
