package qrhl.toplevel

import java.io.PrintWriter
import qrhl.{State, Subgoal}
import qrhl.isabellex.IsabelleX
import IsabelleX.{globalIsabelle => GIsabelle}
import de.unruh.isabelle.control.IsabelleMLException
import GIsabelle.Ops
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.Context
import hashedcomputation.{Hash, HashTag, Hashable}

// Implicits
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import qrhl.isabellex.MLValueConverters.Implicits._
import scala.concurrent.ExecutionContext.Implicits.global
import GIsabelle.isabelleControl
import hashedcomputation.Implicits._

case class PrintCommand(symbol : String) extends Command {
  override def hash: Hash[PrintCommand.this.type] = HashTag()(Hashable.hash(symbol))

  override def act(state: State, output: PrintWriter): State = {
    var found = false
    val env = state.environment
    val prettyTyp = state.isabelle.prettyTyp _

    for (prog <- env.programs.get(symbol)) {
      found = true
      output.println(prog.toStringMultiline)
      output.println(s"\nVariable use of $symbol:${prog.variablesRecursive}")
    }

    for (typ <- env.ambientVariables.get(symbol)) {
      found = true
      output.println(s"ambient var $symbol : ${prettyTyp(typ)}")
    }

    for (v <- env.cVariables.get(symbol)) {
      found = true
      output.println(v.toString)
    }

    for (v <- env.qVariables.get(symbol)) {
      found = true
      output.println(v.toString)
    }

    try {
      val fact = Ops.thms_as_subgoals(state.isabelle.context, symbol).retrieveNow
      found = true
      output.println(s"The name $symbol refers to ${fact.length} lemmas:\n")
      for (lemma <- fact)
        output.println(lemma+"\n\n")
    } catch {
      case e : IsabelleMLException => // Means there is no such lemma
    }

    if (!found)
      output.println(s"No variable/program/lemma with name $symbol found.")

    state
  }
}
