package qrhl.tactic

import isabelle.{Context, Term, Typ}
import isabelle.control.MLValue
import qrhl._
import qrhl.isabellex.{IsabelleX, RichTerm}


// Implicits
import MLValue.Implicits._
import Term.Implicits._
import Typ.Implicits._
import Context.Implicits._
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl
import qrhl.isabellex.IsabelleX.globalIsabelle.Ops
import scala.concurrent.ExecutionContext.Implicits.global



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
      val (result,varTyp2) = Ops.fixTacOp(expr.isabelleTerm, variable).retrieveNow
      val varTyp3 = varTyp2

      if (varTyp!=varTyp3)
        throw UserException(s"Please use a variable of type ${state.isabelle.prettyTyp(varTyp3)} ($variable has type ${state.isabelle.prettyTyp(varTyp)}")

      List(AmbientSubgoal(RichTerm(result)))
  }
}

