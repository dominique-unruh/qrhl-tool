package qrhl.toplevel

import java.io.{PrintWriter, StringWriter}
import java.nio.file.{Path, Paths}

import de.unruh.isabelle.pure.Typ
import qrhl.isabellex.IsabelleX
import qrhl.logic.{Block, CVariable, QVariable, Variable}
import qrhl.{State, Subgoal, Tactic, UserException}
import IsabelleX.{globalIsabelle => GIsabelle}

import scala.collection.immutable.ListSet
import GIsabelle.Ops
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.Typ
import scalaz.Scalaz.ToIdOps

// Implicits
import GIsabelle.isabelleControl
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._
import scala.concurrent.ExecutionContext.Implicits.global


trait Command {
  protected def act(state: State, output: PrintWriter): State
  def actString(state: State): State = {
    val stringWriter = new StringWriter()
    val writer = new PrintWriter(stringWriter)
    val newState = act(state, writer)
    writer.flush()
    newState.setLastOutput(stringWriter.toString)
  }
  def actPrint(state: State): State = {
    val newState = actString(state)
    println(newState.lastOutput)
    newState
  }
}

case class ChangeDirectoryCommand(dir:Path) extends Command {
  assert(dir!=null)
  override def act(state: State, output: PrintWriter): State = state.changeDirectory(dir)
}
object ChangeDirectoryCommand {
  def apply(dir:String) : ChangeDirectoryCommand = apply(Paths.get(dir))
}

case class IsabelleCommand(thy:Seq[String]) extends Command {
  override def act(state: State, output: PrintWriter): State =
    throw new RuntimeException("IsabelleCommand.act must not be called.")
}

case class DeclareVariableCommand(name: String, typ: Typ, ambient:Boolean=false, quantum:Boolean=false) extends Command {
  assert(!(ambient && quantum))

  override def act(state: State, output: PrintWriter): State = {
    if (ambient) {
      output.println(s"Declaring ambient variable $name : ${IsabelleX.pretty(typ)}.")
      state.declareAmbientVariable(name,typ)
    } else {
      output.println(s"Declaring ${if (quantum) "quantum" else "classical"} variable $name : ${IsabelleX.pretty(typ)}.")
      state.declareVariable(name, typ, quantum = quantum)
    }
  }
}

case class DeclareProgramCommand(name: String, oracles: List[String], program : Block) extends Command {
  override def act(state: State, output: PrintWriter): State = {
    output.println(s"Declaring program $name. ")
    state.declareProgram(name,oracles,program.markOracles(oracles))
  }
}

case class DeclareAdversaryCommand(name: String, free: Seq[Variable], inner : Seq[Variable],
                                   readonly: Seq[Variable], covered : Seq[Variable],
                                   overwritten: Seq[Variable], numOracles: Int) extends Command {
  override def act(state: State, output: PrintWriter): State = {
    output.println(s"Declaring adversary $name. ")
    if (numOracles==0 && inner.nonEmpty)
      throw UserException("An adversary without oracles cannot have inner variables")
    if (numOracles==0 && covered.nonEmpty)
      throw UserException("An adversary without oracles cannot have explicitly specified covered variables")
    if ((overwritten.toSet & readonly.toSet).nonEmpty)
      throw UserException("A variable cannot be overwritten and readonly at the same time")
    val free2 = free ++ readonly ++ overwritten
    val written = (ListSet(free:_*) -- readonly).toList
    val inner2 = inner ++ covered
    state.declareAdversary(name,free=free2,inner=inner2,written=written,covered=covered,overwritten=overwritten,numOracles=numOracles)
  }
}

/**
  * @param name may be "", if the lemma should not be stored
  * @param goal the subgoal to be opened
  */
case class GoalCommand(name: String, goal: Subgoal) extends Command {
  override def act(state: State, output: PrintWriter): State = {
    output.println("Starting proof.")
    val state2 = state.openGoal(name, goal)
    state2
  }
}

case class TacticCommand(tactic:Tactic) extends Command {
  override def act(state: State, output: PrintWriter): State = {
    if (!state.cheatMode.cheating)
      output.println(s"Applying tactic $tactic.")
    val state2 = state.applyTactic(tactic)(output)
    state2
  }
}

/*case class UndoCommand(n:Int) extends Command {
  assert(n>0)

  override def act(state: State, output: PrintWriter): State = throw new RuntimeException() // should not be called
}*/

//case object QuitCommand extends Command {
//  override def act(state: State, output: PrintWriter): State = throw new RuntimeException() // should not be called
//}

//case class DummyCommand() extends Command {
//  override def act(state: State, output: PrintWriter): State = state
//}

case class QedCommand() extends Command {
  override def act(state: State, output: PrintWriter): State = {
    if (state.goal.nonEmpty)
      throw UserException("Pending subgoals.")
    if (state.currentLemma.isEmpty)
      throw UserException("Not in a proof.")
    if (state.currentLemma.get._1 != "")
      output.println(s"Finished and saved current lemma as '${state.currentLemma.get._1}':\n${state.currentLemma.get._2}")
    else
      output.println("Finished current lemma.")
    state.qed
  }
}


class DebugCommand private (action: (State,PrintWriter) => State) extends Command {
  override def act(state: State, output: PrintWriter): State = action(state, output)
}
object DebugCommand {
  def state(action: (State,PrintWriter) => Unit): DebugCommand = new DebugCommand({ (state,output) => action(state,output); state})
  def goals(action: (IsabelleX.ContextX, List[Subgoal], PrintWriter) => Unit): DebugCommand =
    new DebugCommand({(state,output) => action(state.isabelle, state.goal, output); state})
  val isabelle: DebugCommand = DebugCommand.state({
    (state, output) =>
      val str = Ops.debugOp(MLValue(state.isabelle.context)).retrieveNow
      output.println(s"DEBUG: $str")
  })

}

case class CheatCommand(file:Boolean=false, proof:Boolean=false, stop:Boolean=false) extends Command {
  assert(! (file&&proof))
  assert(! (file&&stop))
  assert(! (proof&&stop))

  override def act(state: State, output: PrintWriter): State = {
    val infile = {
      if (file) true
      else if (proof) false
      else if (state.currentLemma.isDefined) false
      else true
    }
    if (stop) {
      state.stopCheating
    } else if (infile) {
      output.println("Cheating (till end of file)")
      state.cheatInFile
    } else {
      output.println("Cheating (till end of proof)")
      state.cheatInProof
    }
  }
}

case class IncludeCommand(file:Path) extends Command {
  assert(file!=null)
  override def act(state: State, output: PrintWriter): State =
    throw new RuntimeException("IncludeCommand.act must not be called.")
}
object IncludeCommand {
  def apply(file:String) : IncludeCommand = apply(Paths.get(file))
}

