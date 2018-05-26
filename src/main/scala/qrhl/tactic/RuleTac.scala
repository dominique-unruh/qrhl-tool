package qrhl.tactic

import info.hupel.isabelle.ml.Expr
import info.hupel.isabelle.pure.Term
import info.hupel.isabelle.{Operation, pure}
import org.log4s
import qrhl._
import qrhl.logic.Expression
import qrhl.toplevel.Parser

import scala.collection.immutable.Nil

case class RuleTac(rule:String) extends IsabelleTac(RuleTac.applyRuleOp, { _ => rule }) {
//  override def apply(state: State, goal: Subgoal): List[Subgoal] =
//    goal match {
//      case _: QRHLSubgoal => throw UserException("Expected an ambient logic subgoal")
//      case AmbientSubgoal(expr) =>
//        state.isabelle match {
//          case Some(isa) =>
////            val ml = Expr.uncheckedLiteral[String => pure.Term => pure.Context => List[pure.Term]]("QRHL.applyRule")
////            val goalsExpr = ml(rule)(implicitly)   (expr.isabelleTerm)(implicitly)   (isa.contextExpr)
////            val goals = state.isabelle.get.runExpr(goalsExpr)
//
//            val ctx = state.isabelle.get
//            val goals = ctx.isabelle.invoke(RuleTac.applyRuleOp, (rule, expr.isabelleTerm, ctx.contextId))
//            for (t <- goals) yield AmbientSubgoal(Expression(isa,state.boolT,t))
//          case None => throw UserException(Parser.noIsabelleError)
//        }
//    }

  override def toString: String = "rule "+rule
}

object RuleTac {
  private val logger = log4s.getLogger
  val applyRuleOp: Operation[(String, Term, BigInt), Option[List[Term]]] =
    Operation.implicitly[(String,pure.Term,BigInt), Option[List[pure.Term]]]("applyRule")
}
