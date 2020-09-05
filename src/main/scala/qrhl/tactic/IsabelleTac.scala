package qrhl.tactic

import java.util.concurrent.ConcurrentHashMap

import isabelle.control.MLValue.Converter
import isabelle.{Context, Thm}
import isabelle.control.{Isabelle, MLFunction, MLValue}
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

abstract class IsabelleTac[A](operationName : String, arg : IsabelleX.ContextX => A)(implicit storer: Converter[A]) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = {
    implicit val isabelle: Isabelle = state.isabelle.isabelle.isabelleControl
    val ctxt = state.isabelle.context

    type In = (A, Subgoal, Context)
    type Out = (List[Subgoal], Thm)

    val tacMlValue : MLFunction[In, Out] = {
      val exnToValue = storer.exnToValue
      tactics.getOrElseUpdate((operationName,exnToValue),
        MLValue.compileFunctionRaw[In, Out](
          s"fn (a',E_Subgoal subgoal,E_Context ctxt) => " +
            s"let val (subgoals, thm) = QRHL_Operations.$operationName (${storer.exnToValue} a') subgoal ctxt " +
            s"in E_Pair (E_List (map E_Subgoal subgoals), E_Thm thm) end)")).
        asInstanceOf
    }

    val (newGoals, thm) = tacMlValue(
      MLValue((arg(state.isabelle), goal, ctxt))).retrieveNowOrElse {
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