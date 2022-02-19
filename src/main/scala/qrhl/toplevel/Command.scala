package qrhl.toplevel

import java.io.{PrintWriter, StringWriter}
import java.nio.file.{Path, Paths}
import de.unruh.isabelle.pure.{Context, Typ}
import qrhl.logic.{Block, CVariable, QVariable, Variable}
import qrhl.{State, Subgoal, Tactic, UserException, toplevel}

import scala.collection.immutable.ListSet
import de.unruh.isabelle.control.{Isabelle, IsabelleMLException, OperationCollection}
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.Typ
import hashedcomputation.{Hash, HashTag, Hashable, HashedValue, ListHashable, PathHashable}
import qrhl.isabellex.IsabelleX
import qrhl.isabellex.IsabelleX.{globalIsabelle => GIsabelle}
import scalaz.Scalaz.ToIdOps

import scala.concurrent.ExecutionContext

// Implicits
import GIsabelle.isabelleControl
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._
import scala.concurrent.ExecutionContext.Implicits.global
import hashedcomputation.Implicits._
import qrhl.isabellex.Implicits.TypHashable

trait Command extends HashedValue {
  protected def act(state: State, output: PrintWriter): State
  def actString(state: State): State = {
    val stringWriter = new StringWriter()
    val writer = new PrintWriter(stringWriter)
    def output = { writer.flush(); stringWriter.toString }

    val newState = try {
      act(state, writer)
    } catch {
      case e : UserException => e.setLog(output); throw e
      case e : IsabelleMLException => throw UserException(e, log=output)
    }
    newState.setLastOutput(output)
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
  override def hash: Hash[ChangeDirectoryCommand.this.type] = HashTag()(PathHashable.hash(dir))
}
object ChangeDirectoryCommand {
  def apply(dir:String) : ChangeDirectoryCommand = apply(Paths.get(dir))
}

case class IsabelleCommand(thy:Seq[String]) extends Command {
  override def act(state: State, output: PrintWriter): State =
    throw new RuntimeException("IsabelleCommand.act must not be called.")

  override def hash: Hash[IsabelleCommand.this.type] = HashTag()(Hashable.hash(thy.toList))
}

// TODO test cases
// TODO document in manual
case class IsabelleToplevelCommand(command: String) extends Command {
  override protected def act(state: State, output: PrintWriter): State =
    state.applyIsabelleToplevelCommand(command)

  override def hash: Hash[IsabelleToplevelCommand.this.type] = HashTag()(Hashable.hash(command))
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

  override def hash: Hash[DeclareVariableCommand.this.type] =
    HashTag()(Hashable.hash(name), Hashable.hash(typ), Hashable.hash(ambient), Hashable.hash(quantum))
}

case class DeclareProgramCommand(name: String, oracles: List[String], program : Block) extends Command {
  override def act(state: State, output: PrintWriter): State = {
    output.println(s"Declaring program $name. ")
    state.declareProgram(name,oracles,program.markOracles(oracles))
  }

  override def hash: Hash[DeclareProgramCommand.this.type] =
    HashTag()(Hashable.hash(name), Hashable.hash(oracles), Hashable.hash(program))
}

case class DeclareAdversaryCommand(name: String, free: Seq[Variable], inner : Seq[Variable],
                                   readonly: Seq[Variable], covered : Seq[Variable],
                                   overwritten: Seq[Variable], numOracles: Int) extends Command {

  override def hash: Hash[DeclareAdversaryCommand.this.type] =
    HashTag()(Hashable.hash(name), Hashable.hash(free.toList), Hashable.hash(inner.toList),
      Hashable.hash(readonly.toList), Hashable.hash(covered.toList), Hashable.hash(overwritten.toList),
      Hashable.hash(numOracles))

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

  override def hash: Hash[GoalCommand.this.type] =
    HashTag()(Hashable.hash(name), goal.hash)
}

case class TacticCommand(tactic:Tactic) extends Command {
  override def act(state: State, output: PrintWriter): State = {
    if (!state.cheatMode.cheating)
      output.println(s"Applying tactic $tactic.")
    val state2 = state.applyTactic(tactic)(output)
    state2
  }

  override def hash: Hash[TacticCommand.this.type] =
    HashTag()(tactic.hash)
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
    if (!state.goal.isProved) {
      if (state.goal.isEmpty)
        throw UserException(s"You need to unfocus using ${state.goal.applicableUnfocusCommand} first.")
      else
        throw UserException("Pending subgoals.")
    }
    if (state.currentLemma.isEmpty)
      throw UserException("Not in a proof.")
    if (state.currentLemma.get._1 != "")
      output.println(s"Finished and saved current lemma as '${state.currentLemma.get._1}':\n${state.currentLemma.get._2}")
    else
      output.println("Finished current lemma.")
    state.qed
  }

  override def hash: Hash[QedCommand.this.type] = HashTag()()
}


class DebugCommand private (action: (State,PrintWriter) => State) extends Command {
  override def act(state: State, output: PrintWriter): State = action(state, output)

  override def hash: Hash[DebugCommand.this.type] = HashTag()() // WARNING: not the right hash
}

object DebugCommand {
  def state(action: (State,PrintWriter) => Unit): DebugCommand = new DebugCommand({ (state,output) => action(state,output); state})
//  def goals(action: (IsabelleX.ContextX, List[Subgoal], PrintWriter) => Unit): DebugCommand =
//    new DebugCommand({(state,output) => action(state.isabelle, state.goal, output); state})
  val isabelle: DebugCommand = DebugCommand.state({
    (state, output) =>
      val str = GIsabelle.Ops.debugOp(MLValue(state.isabelle.context)).retrieveNow
      output.println(s"DEBUG: $str")
  })

}

case class CheatCommand(file:Boolean=false, proof:Boolean=false, stop:Boolean=false) extends Command {
  assert(! (file&&proof))
  assert(! (file&&stop))
  assert(! (proof&&stop))

  override def hash: Hash[CheatCommand.this.type] =
    HashTag()(Hashable.hash(file), Hashable.hash(proof), Hashable.hash(stop))

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

  override def hash: Hash[IncludeCommand.this.type] =
    HashTag()(Hashable.hash(file))
}
object IncludeCommand {
  def apply(file:String) : IncludeCommand = apply(Paths.get(file))
}

