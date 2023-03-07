package qrhl.toplevel
import de.unruh.isabelle.pure.Typ
import hashedcomputation.{Hash, HashTag, Hashable}
import qrhl.{State, UserException}

import java.io.PrintWriter
import hashedcomputation.Implicits._
import org.log4s
import qrhl.isabellex.IsabelleX
import qrhl.isabellex.IsabelleX.globalIsabelle.boolT
import qrhl.logic.AbstractProgramDecl
import qrhl.toplevel.TransformUnrolledCommand.logger

import scala.collection.immutable.ListSet

abstract class TransformCommand extends Command

case class TransformUnrolledCommand(program: String) extends TransformCommand {
  /** Must return a stable value */
  override def hash: Hash[TransformUnrolledCommand.this.type] = HashTag()(Hashable.hash(program))

  override def toString: String = s"transform unrolled $program"

  override protected def act(state: State, output: PrintWriter): State = {
    output.println(s"WARNING: Possibly unsound (not proven) command 'derive unrolled' invoked.")

    val env = state.environment
    val programName = this.program
    val program = env.programs.getOrElse(programName, throw UserException(s"Undefined program $programName"))
    if (program.numOracles != 1)
      throw UserException(s"Program $programName has ${program.numOracles} oracles. It must have exactly one.")
    val variables = program.variablesRecursive
    /** Types that need to be embedded in `store` */
    val classicalTypes : ListSet[Typ] = ListSet(boolT) ++ variables.classical.toSeq.map(_.valueTyp)
    /** Types that need to be embedded in `qstore` */
    val quantumTypes : ListSet[Typ] = variables.quantum.map(_.valueTyp)
    val storeName = s"store_$programName"
    val qstoreName = s"qstore_$programName"
    if (env.variableExists(storeName))
      throw UserException(s"Variable of name $storeName already exists. We need a fresh name.")
    if (env.variableExists(qstoreName))
      throw UserException(s"Variable of name $qstoreName already exists. We need a fresh name.")
    if (storeName == qstoreName)
      throw UserException(s"Cannot use the same variable name ($storeName) for the classical and quantum auxiliary variable for the transformed adversary.")
    val storeTyp = IsabelleX.globalIsabelle.tupleT(classicalTypes.toSeq : _*)
    val qstoreTyp = IsabelleX.globalIsabelle.tupleT(quantumTypes.toSeq : _*)
    logger.debug(s"$storeName : $storeTyp, $qstoreName : $qstoreTyp")

    val state2 = state
      .declareVariable(storeName, storeTyp, quantum=false)
      .declareVariable(qstoreName, qstoreTyp, quantum=true)
    val env2 = state2.environment
    val storeVar = env2.getProgVariable(storeName)
    val qstoreVar = env2.getProgVariable(qstoreName)
    val transformedName = s"${programName}_unrolled"
    if (env.variableExists(transformedName))
      throw UserException(s"Variable of name $transformedName already exists. Cannot use it as the name for the transformed adversary.")

    val state3 = state2.declareAdversary(
      name = transformedName,
      free = storeVar :: qstoreVar :: variables.freeVariables.toList,
      inner = Nil,
      written = storeVar :: qstoreVar :: variables.written.toList, // TODO: Is this the correct list? Or do r/o variables become effectively written in our trafo?
      overwritten = Nil,
      covered = Nil,
      numOracles = 0
    )
    val env3 = state3.environment
    val transformedProgram = env3.programs(transformedName)
    logger.debug(s"Transformed program: $transformedProgram")

    logger.warn("Incomplete!")

    output.println(s"Declared transformed adversary $transformedName with additional variables $storeName, $qstoreName.")
    output.println(s"""Use "print $transformedName.", "print $storeName.", and "print $qstoreName." to inspect the details.""")
    // TODO instructions how to derive additional facts.
    state3
  }
}

object TransformUnrolledCommand {
  private val logger = log4s.getLogger
}