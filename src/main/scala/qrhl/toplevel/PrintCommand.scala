package qrhl.toplevel

import qrhl.{State, Subgoal}
import qrhl.isabellex.IsabelleX
import IsabelleX.{globalIsabelle => GIsabelle}
import isabelle.control.IsabelleException
import GIsabelle.Ops
import isabelle.mlvalue.MLValue
import isabelle.pure.Context

// Implicits
import isabelle.mlvalue.MLValue.Implicits._
import qrhl.isabellex.MLValueConverters.Implicits._
import Context.Implicits._
import scala.concurrent.ExecutionContext.Implicits.global
import GIsabelle.isabelleControl

case class PrintCommand(symbol : String) extends Command {
  override def act(state: State): State = {
    var found = false
    val env = state.environment
    val prettyTyp = state.isabelle.prettyTyp _

    for (prog <- env.programs.get(symbol)) {
      found = true
      println(prog.toStringMultiline)
      println(s"\nVariable use of $symbol:${prog.variablesRecursive}")
    }

    for (typ <- env.ambientVariables.get(symbol)) {
      found = true
      println(s"ambient var $symbol : ${prettyTyp(typ)}")
    }

    for (v <- env.cVariables.get(symbol)) {
      found = true
      println(v.toString)
    }

    for (v <- env.qVariables.get(symbol)) {
      found = true
      println(v.toString)
    }

    try {
      val fact = Ops.thms_as_subgoals(MLValue((state.isabelle.context, symbol))).retrieveNow
      found = true
      println(s"The name $symbol refers to ${fact.length} lemmas:\n")
      for (lemma <- fact)
        println(lemma+"\n\n")
    } catch {
      case e : IsabelleException => // Means there is no such lemma
    }

    if (!found)
      println(s"No variable/program/lemma with name $symbol found.")

    state
  }
}
