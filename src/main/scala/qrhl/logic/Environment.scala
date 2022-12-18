package qrhl.logic

import qrhl.{MaybeAllSet, UserException}
import qrhl.isabellex.IsabelleX.ContextX
import qrhl.isabellex.IsabelleX

import scala.collection.mutable
import de.unruh.isabelle.pure.{Context, Term, Typ}
import IsabelleX.{ContextX, globalIsabelle => GIsabelle}
import GIsabelle.Ops
import de.unruh.isabelle.mlvalue.MLValue
import hashedcomputation.{Hash, HashTag, Hashable, HashedValue}

import scala.collection.immutable.ListSet

// Implicits
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._
import qrhl.isabellex.MLValueConverters.Implicits._
import qrhl.isabellex.Implicits._
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl
import scala.concurrent.ExecutionContext.Implicits.global
import hashedcomputation.Implicits._


/** Represents a logic environment in which programs and expressions are interpreted.
  * @param cVariables All declared classical variables
  * @param qVariables All declared quantum variables
  * @param ambientVariables All declared ambient variables (i.e., unspecified values, can be used in programs but not written)
  * @param programs All declared programs (both concrete and abstract (adversary) ones)
  */
final class Environment private
  (val cVariables : Map[String, CVariableNI],
   val qVariables : Map[String, QVariableNI],
   val ambientVariables : Map[String,Typ],
   val cqVariables12 : Set[String],
//   val indexedNames : Set[String], // all variable names together, program variables indexed with 1/2
//   val nonindexedNames : Set[String], // all variable names together, without 1/2-index
   val programs : Map[String,ProgramDecl],
   val _hash: Hash[Environment])
  extends HashedValue
{
  override def hash: Hash[Environment.this.type] = _hash.asInstanceOf[Hash[this.type]]

  def getCVariable(res: String): CVariableNI =
    cVariables.getOrElse(res, throw UserException(s"Classical variable $res not declared"))
  def getQVariable(res: String): QVariableNI =
    qVariables.getOrElse(res, throw UserException(s"Quantum variable $res not declared"))
  def getProgVariable(name: String): Variable with Nonindexed =
    qVariables.getOrElse(name, cVariables.getOrElse(name, throw UserException(s"Program variable $name not declared")))

  def getAmbientVariable(res: String): Typ =
    ambientVariables.getOrElse(res, throw UserException(s"Ambient variable $res not declared"))

  /** Checks whether the ambient variable "variable" is used in the definition of some program
    *
    * @return Some(programName) if the variable is used in program programName, None otherwise
    */
  def variableUsedInPrograms(variable: String) : Option[String] = {
    for ((n, p) <- programs) p match {
      case _: AbstractProgramDecl =>
      case cpd: ConcreteProgramDecl =>
        if (cpd.ambientVars.contains(variable))
          return Some(n)
    }
    None
  }


  //  def getCVariable(name: String): CVariable = cVariables(name)
  /** Tests whether variable of name ''name'' already exists.
    * This includes classical, quantum, and ambient variables, as well as indexed variables
    * and program names.
    */
  def variableExists(name:String) : Boolean = {
    cVariables.contains(name) || qVariables.contains(name) || ambientVariables.contains(name) ||
      cqVariables12.contains(name) || programs.contains(name)
  }

  /** Variable declared as program variable or ambient variable */
  def variableExistsForProg(name:String) : Boolean = cVariables.contains(name) || qVariables.contains(name) || ambientVariables.contains(name)
  /** Variable declared as indexed program variable or ambient variable */
  def variableExistsForPredicateShortform(name:String) : Boolean = cqVariables12.contains(name) || ambientVariables.contains(name)
  /** Variable declared as program variable or ambient variable */
  def variableExistsForPredicateLongform(name:String) : Boolean = variableExistsForProg(name)
//  /** Variable declared as indexed program variable or ambient variable or program */
//  def variableExistsForGoal(name:String) : Boolean = cqVariables12.contains(name) || ambientVariables.contains(name) || programs.contains(name)

  def declareVariable(name: String, typ: Typ, quantum:Boolean=false): Environment = {
    if (variableExists(name))
      throw UserException(s"Variable name $name already in use (as variable or program name)")
//    val nonidxNames = nonindexedNames + name

    val newIdxNames = List(Variable.index1(name),Variable.index2(name))
    for (n <- newIdxNames)
      if (variableExists(n))
        throw UserException(s"Indexed form $n of variable $name already in use (as variable or program name)")
//    assert(!indexedNames.contains(n))
//    val idxNames = indexedNames ++ newIdxNames

//    assert(!cVariables.contains(name))
//    assert(!qVariables.contains(name))
    if (quantum)
      copy(qVariables = qVariables.updated(name, QVariable.fromName(name, typ)),
        cqVariables12=cqVariables12++newIdxNames,
        hash = HashTag()(hash, Hashable.hash(name), Hashable.hash(typ)))
    else
      copy(cVariables = cVariables.updated(name, CVariable.fromName(name,typ)),
        cqVariables12=cqVariables12++newIdxNames,
        hash = HashTag()(hash, Hashable.hash(name), Hashable.hash(typ)))
  }

  def declareAmbientVariable(name: String, typ:Typ) : Environment = {
    assert(!variableExists(name))
    copy(ambientVariables=ambientVariables.updated(name, typ),
      hash = HashTag()(hash, Hashable.hash(name), Hashable.hash(typ)))
  }

  def declareProgram(decl: ProgramDecl) : Environment = {
    if (programs.contains(decl.name))
      throw UserException(s"A program with name ${decl.name} was already declared.")
    if (variableExists(decl.name))
      throw UserException(s"Program name ${decl.name} conflicts with an existing variable name")
    copy(programs=programs.updated(decl.name, decl),
      hash = HashTag()(hash, decl.hash))
  }

//  def declareProgram(name: String, oracles:List[String], program: Block): Environment = {
//    if (programs.contains(name))
//      throw UserException(s"A program with name $name was already declared.")
//    if (variableExists(name))
//      throw UserException(s"Program name $name conflicts with an existing variable name")
//    copy(programs=programs.updated(name, ConcreteProgramDecl(this,name,oracles,program)))
//  }
//
//  def declareAdversary(name: String, cvars: Seq[CVariable], qvars: Seq[QVariable], numOracles: Int): Environment = {
//    if (programs.contains(name))
//      throw UserException(s"A program with name $name was already declared.")
////    for (p <- calls)
////      if (!programs.contains(p))
////        throw UserException(s"Please declare program $p first.")
//    assert(!variableExists(name))
//    copy(programs=programs.updated(name, AbstractProgramDecl(name, cvars.toList, qvars.toList, numOracles)))
//  }


  private def copy(cVariables:Map[String,CVariableNI]=cVariables,
                   qVariables:Map[String,QVariableNI]=qVariables,
                   ambientVariables:Map[String,Typ]=ambientVariables,
                   programs:Map[String,ProgramDecl]=programs,
                   cqVariables12:Set[String]=cqVariables12,
                   hash:Hash[Environment]) =
    new Environment(cVariables = cVariables, qVariables=qVariables, programs=programs,
      ambientVariables=ambientVariables, cqVariables12=cqVariables12, _hash=hash)
}

object Environment {
  private val emptyHash = Hash.randomHash()
  val empty = new Environment(cVariables=Map.empty, qVariables=Map.empty,
    ambientVariables=Map.empty, programs=Map.empty, cqVariables12=Set.empty,
    _hash = emptyHash)
}

sealed trait ProgramDecl extends HashedValue {
  /** All variables used by this program (classical, classical-written, quantum, ambient, program names), recursively. */
  val variablesRecursive : VariableUse
//  val variables : (List[CVariable],List[QVariable])
//  val subprograms : List[ProgramDecl]
  val name: String
  val numOracles : Int
  def declareInIsabelle(context: IsabelleX.ContextX): IsabelleX.ContextX
  def toStringMultiline : String
}

final case class AbstractProgramDecl(name:String, free:List[Variable with Nonindexed], inner:List[Variable with Nonindexed], written:List[Variable with Nonindexed],
                                     overwritten:List[Variable with Nonindexed], covered:List[Variable with Nonindexed], numOracles:Int) extends ProgramDecl {

  override lazy val hash: Hash[AbstractProgramDecl.this.type] =
    HashTag()(Hashable.hash(name), Hashable.hash(free), Hashable.hash(inner), Hashable.hash(written),
      Hashable.hash(overwritten), Hashable.hash(covered), Hashable.hash(numOracles))

  import AbstractProgramDecl._
  override val variablesRecursive: VariableUse = {
    VariableUse(freeVariables = ListSet(free:_*), written = ListSet(written:_*), ambient = ListSet.empty,
      programs = ListSet.empty, overwritten = ListSet(overwritten:_*), oracles=ListSet((1 to numOracles) map (_.toString) :_*),
      inner = ListSet(inner:_*),
      covered = if (numOracles==0) MaybeAllSet.all else MaybeAllSet(covered:_*))
  }

  def declareInIsabelle(isabelle: IsabelleX.ContextX): IsabelleX.ContextX = {
    val vars = variablesRecursive
    val cvars = vars.classical map { v => (v.basename, v.valueTyp) }
    val cwvars = vars.written collect { case v : CVariable => (v.basename, v.valueTyp) }
    val qvars = vars.quantum map { v => (v.basename, v.valueTyp) }
    val ctxt = Ops.declare_abstract_program_op(
      isabelle.context, name, cvars.toList, cwvars.toList, qvars.toList, numOracles).retrieveNow
    new ContextX(isabelle.isabelle,ctxt)
  }

  override def toStringMultiline: String = {
    val calls = if (numOracles==0) "" else " calls " + Seq.fill(numOracles)("?").mkString(", ")
    s"adversary $name$calls"
  }
}

object AbstractProgramDecl {
}

final case class ConcreteProgramDecl(ctxt: Context, environment: Environment, name:String, oracles:List[String], program:Block) extends ProgramDecl {
  import ConcreteProgramDecl._

  override lazy val hash: Hash[ConcreteProgramDecl.this.type] =
    HashTag()(Hashable.hash(environment), Hashable.hash(name), Hashable.hash(oracles), Hashable.hash(program))

  override val numOracles: Int = oracles.length
  lazy val ambientVars: List[String] = {
    val vars = new mutable.LinkedHashSet[String]
    def scan(st:Statement) : Unit = st match {
      case Local(_,body) => scan(body)
      case Block(sts@_*) => sts.foreach(scan)
      case Call(_,_*) =>
      case Assign(_,e) =>
        vars ++= e.term.variables.filter(environment.ambientVariables.contains)
      case Sample(_,e) =>
        vars ++= e.term.variables.filter(environment.ambientVariables.contains)
      case QApply(_,e) =>
        vars ++= e.term.variables.filter(environment.ambientVariables.contains)
      case While(e,body) =>
        vars ++= e.term.variables.filter(environment.ambientVariables.contains)
        scan(body)
      case IfThenElse(e,thenBranch,elseBranch) =>
        vars ++= e.term.variables.filter(environment.ambientVariables.contains)
        scan(thenBranch)
        scan(elseBranch)
      case Measurement(_, _,e) =>
        vars ++= e.term.variables.filter(environment.ambientVariables.contains)
      case QInit(_,e) =>
        vars ++= e.term.variables.filter(environment.ambientVariables.contains)
    }
    scan(program)
    vars.toList
  }

  override lazy val variablesRecursive: VariableUse =
    program.variableUse(ctxt, environment)

  def declareInIsabelle(context: IsabelleX.ContextX): IsabelleX.ContextX = {
    val vars = variablesRecursive
    val cvars = vars.classical map { v => (v.basename, v.valueTyp) }
    val cwvars = vars.written collect { case v : CVariable => (v.basename, v.valueTyp) }
    val qvars = vars.quantum map { v => (v.basename, v.valueTyp) }
    val ctxt = Ops.declare_concrete_program_op(context.context, name, cvars.toList, cwvars.toList, qvars.toList, oracles, program).retrieveNow
    new ContextX(context.isabelle, ctxt)
  }

  override def toStringMultiline: String = {
    val args = if (oracles.isEmpty) "" else "(" + oracles.mkString(",") + ")"
    s"program $name$args = {\n${this.program.toStringMultiline("  ")}\n}"
  }
}