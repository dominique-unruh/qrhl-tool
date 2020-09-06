package qrhl.tactic

import java.util.concurrent.ConcurrentHashMap

import isabelle.control.MLValue.Converter
import isabelle.{Context, Thm}
import isabelle.control.{Isabelle, MLFunction, MLFunction3, MLValue}
import qrhl._
import qrhl.isabellex.IsabelleX
import MLValue.Implicits._
import qrhl.isabellex.MLValueConverters.Implicits._
import Context.Implicits._
import Thm.Implicits._
import qrhl.tactic.IsabelleTac.tactics

import scala.collection.JavaConverters.mapAsScalaConcurrentMapConverter
import scala.collection.mutable
import scala.concurrent.ExecutionContext.Implicits.global

abstract class IsabelleTac[A](operationName : String, arg : IsabelleX.ContextX => A)(implicit converter: Converter[A]) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = {
    implicit val isabelle: Isabelle = state.isabelle.isabelle.isabelleControl
    val ctxt = state.isabelle.context

    type Out = Option[(List[Subgoal], Thm)]

    val tacMlValue : MLFunction3[A, Subgoal, Context, Out] = {
      val exnToValue = converter.exnToValue
      tactics.getOrElseUpdate((operationName, exnToValue),
        MLValue.compileFunctionRaw[(A, Subgoal, Context), Out](
          s"""fn E_Pair (a', E_Pair (QRHL_Operations.E_Subgoal subgoal, E_Context ctxt)) =>
                case QRHL_Operations.$operationName ((${converter.exnToValue}) a', subgoal, ctxt) of
                  NONE => E_Option NONE
                 | SOME (subgoals, thm) =>
                    E_Option (SOME (E_Pair (E_List (map QRHL_Operations.E_Subgoal subgoals), E_Thm thm)))""")
          .function3[A, Subgoal, Context, Out])
        .asInstanceOf[MLFunction3[A, Subgoal, Context, Out]]
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