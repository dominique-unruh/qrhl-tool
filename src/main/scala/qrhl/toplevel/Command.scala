package qrhl.toplevel

import qrhl.{State, Subgoal, Tactic, UserException}
import qrhl.logic.{Block, Typ}

trait Command {
  def act(state: State): State
}

case class IsabelleCommand(path: String, thy:Option[String]=None) extends Command {
  override def act(state: State): State = {
    println(s"Loading Isabelle at $path.")
    state.loadIsabelle(path,thy.getOrElse(State.defaultIsabelleTheory))
  }
}

case class DeclareVariableCommand(name: String, typ: Typ, ambient:Boolean=false, quantum:Boolean=false) extends Command {
  assert(!(ambient && quantum))

  override def act(state: State): State = {
    if (ambient) {
      println(s"Declaring ambient variable $name : $typ.")
      state.declareAmbientVariable(name,typ)
    } else {
      println(s"Declaring ${if (quantum) "quantum" else "classical"} variable $name : $typ.")
      state.declareVariable(name, typ, quantum = quantum)
    }
  }
}

case class DeclareProgramCommand(name: String, program : Block) extends Command {
  override def act(state: State): State = {
    println(s"Declaring program $name. ")
    state.declareProgram(name,program)
  }
}

case class GoalCommand(goal: Subgoal) extends Command {
  override def act(state: State): State = {
    println("Starting proof.")
    val state2 = state.openGoal(goal)
    state2
  }
}

case class TacticCommand(tactic:Tactic) extends Command {
  override def act(state: State): State = {
    println(s"Applying tactic $tactic.")
    val state2 = state.applyTactic(tactic)
    state2
  }
}

case class UndoCommand(n:Int) extends Command {
  assert(n>0)

  override def act(state: State): State = throw new RuntimeException() // should not be called
}

//case object QuitCommand extends Command {
//  override def act(state: State): State = throw new RuntimeException() // should not be called
//}

//case class DummyCommand() extends Command {
//  override def act(state: State): State = state
//}

case class QedCommand() extends Command {
  override def act(state: State): State = {
    if (state.goal.nonEmpty)
      throw UserException("Pending subgoals.")
    state
  }
}

