package qrhl.tactic

import java.io.PrintWriter
import qrhl._
import qrhl.isabellex.{IsabelleX}
import IsabelleX.globalIsabelle
import de.unruh.isabelle.pure.{Abs, Bound, Free, Term}
import hashedcomputation.{Hash, HashTag, Hashable}
import qrhl.logic.ExpressionIndexed

// Implicits
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl
import scala.concurrent.ExecutionContext.Implicits._
import hashedcomputation.Implicits._

case class CaseTac(variable:String, expr:ExpressionIndexed) extends Tactic {
  override def hash: Hash[CaseTac.this.type] =
    HashTag()(Hashable.hash(variable), expr.hash)

  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case QRHLSubgoal(left,right,pre,post,assms) =>
      if (goal.containsAmbientVar(variable))
        throw UserException(s"Variable $variable already contained in goal")

      if (expr.term.variables.contains(variable))
        throw UserException(s"Variable $variable already contained in supplied expression $expr")

      state.environment.variableUsedInPrograms(variable) match {
        case None =>
        case Some(prog) => throw UserException(s"Variable $variable already used in program $prog")
      }

      val varTyp = state.environment.ambientVariables(variable)
      if (varTyp != expr.rangeTyp)
        throw UserException(s"Variable $variable has type ${state.isabelle.prettyTyp(varTyp)}, but expression has type ${state.isabelle.prettyTyp(expr.rangeTyp)}")

      for (x <- expr.term.variables)
        if (!state.environment.variableExistsForPredicateLongform(x))
          throw UserException(s"Undeclared (or non-indexed) variable $x in precondition")

      val caseExpr : Term = globalIsabelle.classical_subspace(
        globalIsabelle.mk_eq(expr.term.isabelleTerm $ Bound(0), Free(variable,varTyp)))
      val pre2 = Abs("mem", globalIsabelle.cl2T, globalIsabelle.predicate_inf $ caseExpr $ (pre.term.isabelleTerm $ Bound(0)))
      val pre3 = ExpressionIndexed.fromTerm(pre2)

      List(QRHLSubgoal(left,right,pre3,post,assms))
    case _ : AmbientSubgoal => throw UserException("Expected a QRHL subgoal")
  }
}
