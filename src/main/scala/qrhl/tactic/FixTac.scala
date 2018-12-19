package qrhl.tactic

import info.hupel.isabelle.pure.Term
import info.hupel.isabelle.{Operation, pure}
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}

import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec

case class FixTac(variable:String) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(_, _, _, _, _) =>
      throw UserException("Expecting an ambient logic goal")
    case AmbientSubgoal(expr) =>
      if (goal.containsAmbientVar(variable))
        throw UserException(s"Variable $variable already contained in goal")

      state.environment.variableUsedInPrograms(variable) match {
        case None =>
        case Some(prog) => throw UserException(s"Variable $variable already used in program $prog")
      }

      val varTyp = state.environment.ambientVariables.getOrElse(variable,
        throw UserException(s"$variable is not an ambient variable"))

//      val lit = ml.Expr.uncheckedLiteral[Term => String => (Term,pure.Typ)]("QRHL.fixTac")
//      val mlExpr = lit(expr.isabelleTerm)(implicitly) (variable)
//      val (result,varTyp2) = state.isabelle.runExpr(mlExpr)
      val (result,varTyp2) = state.isabelle.isabelle.invoke(fixTacOp, (state.isabelle.contextId, expr.isabelleTerm, variable))
      val varTyp3 = varTyp2

      if (varTyp!=varTyp3)
        throw UserException(s"Please use a variable of type ${state.isabelle.prettyTyp(varTyp3)} ($variable has type ${state.isabelle.prettyTyp(varTyp)}")

      List(AmbientSubgoal(result))
  }

  val fixTacOp: Operation[(BigInt, Term, String), (RichTerm, pure.Typ)] =
    Operation.implicitly[(BigInt, Term,String), (RichTerm, pure.Typ)]("fixTac")
}