package qrhl.toplevel

import java.nio.file.Path

import info.hupel.isabelle.pure
import qrhl.isabelle.Isabelle
import qrhl.logic.{Block, CVariable, QVariable}
import qrhl.{State, Subgoal, Tactic, UserException}


trait Command {
  def act(state: State): State
}

case class ChangeDirectoryCommand(dir:Path) extends Command {
  assert(dir!=null)
  override def act(state: State): State = state.changeDirectory(dir)
}

case class IsabelleCommand(thy:Option[String]=None) extends Command {
  override def act(state: State): State = {
    println(s"Loading Isabelle.")
    val newState = state.loadIsabelle("auto",thy)
    println("Isabelle loaded.")
    newState
  }
}

case class DeclareVariableCommand(name: String, typ: pure.Typ, ambient:Boolean=false, quantum:Boolean=false) extends Command {
  assert(!(ambient && quantum))

  override def act(state: State): State = {
    if (ambient) {
      println(s"Declaring ambient variable $name : $typ.")
      state.declareAmbientVariable(name,typ)
    } else {
      println(s"Declaring ${if (quantum) "quantum" else "classical"} variable $name : ${Isabelle.pretty(typ)}.")
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

case class DeclareAdversaryCommand(name: String, cvars: Seq[CVariable], qvars : Seq[QVariable]) extends Command {
  override def act(state: State): State = {
    println(s"Declaring adversary $name. ")
    state.declareAdversary(name,cvars,qvars)
  }
}

/**
  * @param name may be "", if the lemma should not be stored
  * @param goal the subgoal to be opened
  */
case class GoalCommand(name: String, goal: Subgoal) extends Command {
  override def act(state: State): State = {
    println("Starting proof.")
    val state2 = state.openGoal(name, goal)
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
    if (state.currentLemma.isEmpty)
      throw UserException("Not in a proof.")
    if (state.currentLemma.get._1 != "")
      println(s"Finished and saved current lemma as '${state.currentLemma.get._1}':\n${state.currentLemma.get._2}")
    else
      println("Finished current lemma.")
    state.qed
  }
}

