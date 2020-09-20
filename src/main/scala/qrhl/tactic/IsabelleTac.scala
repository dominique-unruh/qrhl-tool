package qrhl.tactic

import java.util.concurrent.ConcurrentHashMap

import de.unruh.isabelle.mlvalue.MLValue.Converter
import de.unruh.isabelle.control.Isabelle
import qrhl._
import qrhl.isabellex.IsabelleX
import de.unruh.isabelle.mlvalue.{MLFunction3, MLValue}
import de.unruh.isabelle.pure.{Context, Thm}
import qrhl.tactic.IsabelleTac.tactics
import scala.collection.mutable

// Implicits
import scala.collection.JavaConverters.mapAsScalaConcurrentMapConverter
import scala.concurrent.ExecutionContext.Implicits.global
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import qrhl.isabellex.MLValueConverters.Implicits._

abstract class IsabelleTac[A](operationName : String, arg : IsabelleX.ContextX => A)(implicit converter: Converter[A]) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = {
    implicit val isabelle: Isabelle = state.isabelle.isabelle.isabelleControl
    val ctxt = state.isabelle.context

    type In = (A, Subgoal, Context)
    type Out = Option[(List[Subgoal], Thm)]
    type Fun = MLFunction3[A, Subgoal, Context, Out]

    val tacMlValue : MLFunction3[A, Subgoal, Context, Out] = {
      val exnToValue = converter.exnToValueProtected
      tactics.getOrElseUpdate((operationName, exnToValue),
        MLValue.compileFunctionRaw[In, Out](
          s"""fn E_Pair (a', E_Pair (QRHL_Operations.E_Subgoal subgoal, E_Context ctxt)) =>
                case QRHL_Operations.$operationName (($exnToValue) a', subgoal, ctxt) of
                  NONE => E_Option NONE
                 | SOME (subgoals, thm) =>
                    E_Option (SOME (E_Pair (E_List (map QRHL_Operations.E_Subgoal subgoals), E_Thm thm)))""")
          .function3[A, Subgoal, Context, Out])
        .asInstanceOf[Fun]
    }

    val (newGoals, thm) = tacMlValue(arg(state.isabelle), goal, ctxt).retrieveNow.getOrElse {
      throw UserException("tactic failed") }

    check(state, goal, newGoals)

    Subgoal.printOracles(thm)

    postprocess(state,goal,newGoals)
  }

  def check(state: State, goal: Subgoal, newGoals : List[Subgoal]): Unit = {}
  def postprocess(state: State, goal: Subgoal, newGoals : List[Subgoal]): List[Subgoal] = newGoals


  override def toString: String = f"IsabelleTac($operationName,$arg)"
}

object IsabelleTac {
  private val tactics: mutable.Map[(String, String), MLValue[_]] = new ConcurrentHashMap[(String,String), MLValue[_]]().asScala
}