package qrhl.toplevel
import de.unruh.isabelle.pure.{Term, Typ}
import hashedcomputation.{Hash, HashTag, Hashable}
import qrhl.{QRHLSubgoal, Schema, SchemaInstantiation, State, UserException}

import java.io.PrintWriter
import hashedcomputation.Implicits._
import org.log4s
import qrhl.isabellex.RichTerm
import qrhl.isabellex.IsabelleX.globalIsabelle
import qrhl.isabellex.IsabelleX.globalIsabelle.{liftSpace, boolT, classical_subspace_optimized, conj, default, dest_listT, empty_set, fst, infOptimized, isabelleControl, ket, listT, mk_eq, nil, not, predicate_top, prodT, quantum_equality, span1, tupleT}
import qrhl.logic.{Assign, Block, CVariable, Call, IfThenElse, ProgramDecl, QInit, QVariable, VTSingle, VarTerm, While}
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
    val storeTyp = prodT(listT(tupleT(classicalTypes.toSeq : _*)), boolT)
    val qstoreTyp = listT(tupleT(quantumTypes.toSeq : _*))
    logger.debug(s"$storeName : $storeTyp, $qstoreName : $qstoreTyp")

    val state2 = state
      .declareVariable(storeName, storeTyp, quantum=false)
      .declareVariable(qstoreName, qstoreTyp, quantum=true)
    val env2 = state2.environment
    val storeVar = env2.getProgVariable(storeName).asInstanceOf[CVariable]
    val qstoreVar = env2.getProgVariable(qstoreName).asInstanceOf[QVariable]
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

    val schemaName = s"${programName}_unrolled"
    if (state2.schemas.contains(schemaName))
      throw UserException(s"An axiom scheme of name $schemaName already exists. Cannot register the axiom schema for this transformation.")
    val state4 = state3.registerSchema(TransformUnrolledSchema(
      name = schemaName, originalProgram = program, transformedProgram = transformedProgram, store = storeVar, qstore = qstoreVar))

    logger.warn("Incomplete!")

    output.println(s"Declared transformed adversary $transformedName with additional variables $storeName, $qstoreName.\n")
    output.println(s"""Use "print $transformedName.", "print $storeName.", and "print $qstoreName." to inspect the details.\n""")
    output.println(s"""For any given oracle O, invoke "schema $schemaName O." to generate the facts relating "call $programName(O)" to a loop involving "call $transformedName".""")

    state4
  }
}

object TransformUnrolledCommand {
  private val logger = log4s.getLogger
}


case class TransformUnrolledSchema(/** Name of the schema */
                                   name: String,
                                   /** The original program */
                                   originalProgram: ProgramDecl,
                                   /** The transformed program */
                                   transformedProgram: ProgramDecl,
                                   store: CVariable,
                                   qstore: QVariable) extends Schema {
  override def toString = s"schema $name (for ${transformedProgram.name})"
  override def hash: Hash[TransformUnrolledSchema.this.type] =
    HashTag()(Hashable.hash(name))

  override def parser(implicit context: ParserContext): Parser.Parser[SchemaInstantiation] =
    for (oracle <- Parser.identifier)
      yield TransformUnrolledSchemaInstantiation(oracle)

  case class TransformUnrolledSchemaInstantiation(oracle: String) extends SchemaInstantiation {
    override def toString: String = s"schema $name (for ${transformedProgram.name} and $oracle)"
    override def act(state: State, output: PrintWriter): State = {
      output.println(s"WARNING: Possibly unsound (not proven) command 'derive unrolled' used.\n")

      output.println(s"Instantiating facts about ${transformedProgram.name} with oracle $oracle.\n")

      val env = state.environment
      val oracleProg =  env.programs.getOrElse(oracle, throw UserException(s"Unknown program $oracle"))
      if (oracleProg.numOracles != 0)
        throw UserException(s"Oracle $oracle takes oracles itself. It must be a program (with no oracles).")

      if (oracleProg.variablesRecursive.freeVariables.contains(store))
        throw UserException(s"Oracle $oracle contains the classical variable ${store.name}. This variable is for private use in ${transformedProgram.name}")
      if (oracleProg.variablesRecursive.freeVariables.contains(qstore))
        throw UserException(s"Oracle $oracle contains the quantum variable ${qstore.name}. This variable is for private use in ${transformedProgram.name}")

      val lhs = Block(Call(originalProgram.name, Call(oracle)))
      val fstOfStore = fst(store.valueTerm(globalIsabelle.isabelleControl))
      val condition = RichTerm(
        not(mk_eq(
          fstOfStore,
          nil(dest_listT(fstOfStore.fastType))
        )))

      val defaultVal = default(store.valueTyp)
      val ketDefaultVal = ket(default(qstore.valueTyp))

      val oracleInvoke = IfThenElse (condition, Block(Call(oracle)), Block())
      val rhs = Block(
        Assign(VTSingle(store), RichTerm(defaultVal)),
        QInit(VTSingle(qstore), RichTerm(ketDefaultVal)),
        Call(transformedProgram.name),
        oracleInvoke,
        While(condition, body = Block(
          Call(transformedProgram.name),
          oracleInvoke
        )))

      val equalityVarsClassical = originalProgram.variablesRecursive.classical ++ oracleProg.variablesRecursive.classical
      val equalityVarsQuantum = originalProgram.variablesRecursive.quantum ++ oracleProg.variablesRecursive.quantum

      val quantumEquality: Term =
        if (equalityVarsQuantum.isEmpty) predicate_top
        else {
          val left = VarTerm.isabelleTerm(VarTerm.varlist(equalityVarsQuantum.map(_.index1).toSeq: _*))
          val right = VarTerm.isabelleTerm(VarTerm.varlist(equalityVarsQuantum.map(_.index2).toSeq: _*))
          quantum_equality(left, right)
        }

      val classicalIndividualEqualities = equalityVarsClassical.map { v => mk_eq(v.index1.valueTerm, v.index2.valueTerm) }.toSeq

      val storeDefault = mk_eq(store.valueTerm, defaultVal)
      val qstoreDefault = liftSpace(span1(ketDefaultVal), VarTerm.isabelleTerm(VTSingle(qstore)))

      val precondition = infOptimized(
        classical_subspace_optimized(conj(classicalIndividualEqualities: _*)),
        quantumEquality)
      val postcondition = infOptimized(
        classical_subspace_optimized(conj(classicalIndividualEqualities ++ Seq(storeDefault): _*)),
        quantumEquality,
        qstoreDefault)

      val factName = s"${name}_${oracle}"
      val fact = QRHLSubgoal(lhs, rhs, RichTerm(precondition), RichTerm(postcondition), Nil)

      // TODO: remove eventually?
      fact.checkWelltyped(state.isabelle)

      val state2 = state.declareFact(factName, fact)

      output.println(s"""Use "print ${factName}." to inspect the resulting fact.""")

      state2
    }

    override def hash: Hash[TransformUnrolledSchemaInstantiation.this.type] = HashTag()(TransformUnrolledSchema.this.hash, Hashable.hash(oracle))
  }
}

