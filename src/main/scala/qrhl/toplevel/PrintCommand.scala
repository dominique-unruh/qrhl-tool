package qrhl.toplevel

import java.io.PrintWriter
import qrhl.{State, Subgoal}
import qrhl.isabellex.IsabelleX
import IsabelleX.{globalIsabelle, symbols}
import de.unruh.isabelle.control.{Isabelle, IsabelleMLException}
import globalIsabelle.Ops
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.{Const, Context, Term}
import hashedcomputation.{Hash, HashTag, Hashable}
import org.log4s
import qrhl.Utils.pluralS
import qrhl.toplevel.PrintCommand.logger

import scala.collection.mutable.ListBuffer
import scala.util.Random

// Implicits
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import qrhl.isabellex.MLValueConverters.Implicits._
import scala.concurrent.ExecutionContext.Implicits.global
import globalIsabelle.isabelleControl
import hashedcomputation.Implicits._

case class PrintCommand(symbol : String) extends Command {
  override def hash: Hash[PrintCommand.this.type] = HashTag()(Hashable.hash(symbol))

  override def act(state: State, output: PrintWriter): State = {
    var found = false
    val env = state.environment
    val ctxt = state.isabelle.context
    val prettyTyp = state.isabelle.prettyTyp _
    val terms : ListBuffer[Term] = new ListBuffer

    if (symbol == "goal") {
      found = true
      terms ++= printGoal(state, output)
    }

    for (prog <- env.programs.get(symbol)) {
      found = true
      output.println(prog.toStringMultiline)
      output.println(s"\nVariable use of program $symbol:${prog.variablesRecursive}")
    }

    for (typ <- env.ambientVariables.get(symbol)) {
      found = true
      output.println(s"\nambient var $symbol : ${prettyTyp(typ)}")
    }

    for (v <- env.cVariables.get(symbol)) {
      found = true
      output.println()
      output.println(v.toString)
    }

    for (v <- env.qVariables.get(symbol)) {
      found = true
      output.println()
      output.println(v.toString)
    }

    try {
      Ops.check_const(ctxt, symbol).retrieveNow match {
        case Const(name, typ) =>
          output.println(s"\nThe name $symbol refers to the Isabelle constant $name :: ${typ.pretty(ctxt)}")
        case term =>
          output.println(s"\nThe name $symbol refers to the Isabelle constant ${term.pretty(ctxt)} :: ${term.fastType.pretty(ctxt)}")
      }
      found = true
    } catch {
      case _: IsabelleMLException => // Means there is no such constant
    }

    val fact = try Some(Ops.thms_as_subgoals(ctxt, symbol).retrieveNow) catch {
      case e: IsabelleMLException =>
        // Means there is no such lemma, either because it's not a lemma name, or because the spec has errors.
        // We output the error only if nothing else was found.
        if (!found)
          output.println(s"""Could not interpret "$symbol" as a lemma name: ${e.getMessage}""")
        None
    }

    fact match {
      case Some(fact) =>
        found = true
        output.println(s"\nThe name $symbol refers to ${fact.length} lemmas:\n")
        for ((term,subgoal) <- fact) {
          terms += term
          output.println(s"$subgoal\n\n")
        }
      case None =>
    }

    if (!found)
      output.println(s"No variable/program/lemma with name $symbol found.")

    state.withPrintedTerm(terms.toSeq)
  }

  def printGoal(state: State, output: PrintWriter): Seq[Term] = {
    val subgoals = state.goal.focusedSubgoals
    if (subgoals.isEmpty)
      output.println("No goals to print.")
    else
      output.println(s"Current goal${pluralS(subgoals.length)} in Isabelle syntax:")

    // Context without variable declarations etc. This approximates what is available in the Isabelle theories
    val initialContext = state.isabelle.context.theoryOf.context

    for (subgoal <- subgoals) yield {
      val currentLemmaName = state.currentLemma match {
        case Some(("", _)) => "lemma"
        case Some((name, _)) => name
        case None => "lemma"
      }
      val lemmaname = symbols.unicodeToSymbols(currentLemmaName + "_" + Random.between(100000, 999999))

      val term = subgoal.toTerm(state.isabelle)

      val fixes = globalIsabelle.freeVarsWithType(term.isabelleTerm).toList

      val qvars = for (name <- term.variables; v <- state.environment.qVariables.get(name)) yield v

      val declaredQvars =
        if (qvars.isEmpty)
          Nil
        else
          List(symbols.unicodeToSymbols(
            s"  assumes [register]: ‹declared_qvars ⟦${qvars.map(_.basename).mkString(", ")}⟧›"))

      val string = globalIsabelle.Ops.print_as_statement(
        initialContext, lemmaname, fixes, declaredQvars, Nil, term.isabelleTerm).retrieveNow
      val unicode = symbols.symbolsToUnicode(string)

      output.println()
      output.println(unicode)
      term.isabelleTerm
    }
  }
}

object PrintCommand {
  private val logger = log4s.getLogger
}