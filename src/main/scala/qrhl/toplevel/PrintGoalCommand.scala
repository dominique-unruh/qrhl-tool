package qrhl.toplevel
import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.misc.Symbols
import de.unruh.isabelle.misc.Symbols.{symbolsToUnicode, unicodeToSymbols}
import hashedcomputation.{Hash, HashTag}
import org.log4s
import qrhl.State
import qrhl.Utils.pluralS
import qrhl.isabellex.{IsabelleTypes, IsabelleX}
import qrhl.isabellex.IsabelleX.globalIsabelle
import qrhl.isabellex.IsabelleX.globalIsabelle.dummyT

import java.io.PrintWriter
import scala.math.random
import scala.util.Random

// Implicits
import scala.concurrent.ExecutionContext.Implicits.global
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._

case object PrintGoalCommand extends Command {
  override def act(state: State, output: PrintWriter): State = {
    val subgoals = state.goal.focusedSubgoals
    if (subgoals.isEmpty)
      output.println("No goals to print.")
    else
      output.println(s"Current goal${pluralS(subgoals.length)} in Isabelle syntax:")

    implicit val isabelle: Isabelle = globalIsabelle.isabelleControl

    // Context without variable declarations etc. This approximates what is available in the Isabelle theories
    val initialContext = state.isabelle.context.theoryOf.context

    for (subgoal <- subgoals) {
      val currentLemmaName = state.currentLemma match {
        case Some(("", _)) => "lemma"
        case Some((name, _)) => name
        case None => "lemma"
      }
      val lemmaname = unicodeToSymbols(currentLemmaName + "_" + Random.between(100000, 999999))

      val term = subgoal.toTerm(state.isabelle)

      val fixes = globalIsabelle.freeVarsWithType(term.isabelleTerm).toList

      val qvars = term.variables(state.environment).quantum
      val declaredQvars =
        if (qvars.isEmpty)
          Nil
        else
          List(unicodeToSymbols(
            s"  assumes [simp]: ‹declared_qvars ⟦${qvars.map(_.name).mkString(", ")}⟧›"))

      val string = globalIsabelle.Ops.print_as_statement(
        initialContext, lemmaname, fixes, declaredQvars, Nil, term.isabelleTerm).retrieveNow
      val unicode = symbolsToUnicode(string)

      output.println()
      output.println(unicode)
    }

    state
  }

  override val hash: Hash[PrintGoalCommand.this.type] = HashTag()()

  private val logger = log4s.getLogger
}
