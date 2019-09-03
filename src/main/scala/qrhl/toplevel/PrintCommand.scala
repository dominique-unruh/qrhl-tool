package qrhl.toplevel
import info.hupel.isabelle.ProverResult
import qrhl.State
import qrhl.isabelle.Isabelle
import qrhl.logic.{AbstractProgramDecl, ConcreteProgramDecl}

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
      val fact = state.isabelle.isabelle.invoke(Isabelle.thms_as_subgoals, (state.isabelle.contextId, symbol))
      found = true
      println(s"The name $symbol refers to ${fact.length} lemmas:\n")
      for (lemma <- fact)
        println(lemma+"\n\n")
    } catch {
      case e : ProverResult.Failure => // Means there is no such lemma
    }

    if (!found)
      println(s"No variable/program/lemma with name $symbol found.")

    state
  }
}
