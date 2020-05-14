package qrhl.logic

import info.hupel.isabelle.{Operation, pure}
import info.hupel.isabelle.pure.Typ
import qrhl.{MaybeAllSet, UserException}
import qrhl.isabelle.Isabelle.{Context, declareVariableOp}
import qrhl.isabelle.{Isabelle, RichTerm}

import scala.collection.mutable
import RichTerm.term_tight_codec
import RichTerm.typ_tight_codec
import qrhl.isabelle.Codecs._

import scala.collection.immutable.ListSet
import qrhl.Utils.listSetUpcast

/** Represents a logic environment in which programs and expressions are interpreted.
  * @param cVariables All declared classical variables
  * @param qVariables All declared quantum variables
  * @param ambientVariables All declared ambient variables (i.e., unspecified values, can be used in programs but not written)
  * @param programs All declared programs (both concrete and abstract (adversary) ones)
  */
final class Environment private
  (val cVariables : Map[String,CVariable],
   val qVariables : Map[String,QVariable],
   val ambientVariables : Map[String,pure.Typ],
   val cqVariables12 : Set[String],
//   val indexedNames : Set[String], // all variable names together, program variables indexed with 1/2
//   val nonindexedNames : Set[String], // all variable names together, without 1/2-index
   val programs : Map[String,ProgramDecl]) {
  def getCVariable(res: String): CVariable =
    cVariables.getOrElse(res, throw UserException(s"Classical variable $res not declared"))
  def getQVariable(res: String): QVariable =
    qVariables.getOrElse(res, throw UserException(s"Quantum variable $res not declared"))
  def getProgVariable(name: String): Variable =
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
  def variableExistsForPredicate(name:String) : Boolean = cqVariables12.contains(name) || ambientVariables.contains(name)
//  /** Variable declared as indexed program variable or ambient variable or program */
//  def variableExistsForGoal(name:String) : Boolean = cqVariables12.contains(name) || ambientVariables.contains(name) || programs.contains(name)

  def declareVariable(name: String, typ: pure.Typ, quantum:Boolean=false): Environment = {
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
      copy(qVariables = qVariables.updated(name, QVariable(name,typ)),
        cqVariables12=cqVariables12++newIdxNames)
    else
      copy(cVariables = cVariables.updated(name, CVariable(name,typ)),
        cqVariables12=cqVariables12++newIdxNames)
  }

  def declareAmbientVariable(name: String, typ:pure.Typ) : Environment = {
    assert(!variableExists(name))
    copy(ambientVariables=ambientVariables.updated(name, typ))
  }

  def declareProgram(decl: ProgramDecl) : Environment = {
    if (programs.contains(decl.name))
      throw UserException(s"A program with name ${decl.name} was already declared.")
    if (variableExists(decl.name))
      throw UserException(s"Program name ${decl.name} conflicts with an existing variable name")
    copy(programs=programs.updated(decl.name, decl))
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


  private def copy(cVariables:Map[String,CVariable]=cVariables,
                   qVariables:Map[String,QVariable]=qVariables,
                   ambientVariables:Map[String,pure.Typ]=ambientVariables,
                   programs:Map[String,ProgramDecl]=programs,
                   cqVariables12:Set[String]=cqVariables12) =
    new Environment(cVariables=cVariables, qVariables=qVariables, programs=programs,
      ambientVariables=ambientVariables, cqVariables12=cqVariables12)
}

object Environment {
  val empty = new Environment(cVariables=Map.empty, qVariables=Map.empty,
    ambientVariables=Map.empty, programs=Map.empty, cqVariables12=Set.empty)
}

sealed trait ProgramDecl {
  /** All variables used by this program (classical, classical-written, quantum, ambient, program names), recursively. */
  val variablesRecursive : VariableUse
//  val variables : (List[CVariable],List[QVariable])
//  val subprograms : List[ProgramDecl]
  val name: String
  val numOracles : Int
  def declareInIsabelle(context: Isabelle.Context): Isabelle.Context
  def toStringMultiline : String
}

final case class AbstractProgramDecl(name:String, cvars:List[CVariable], qvars:List[QVariable], innerCVars:List[CVariable],
                                     innerQVars:List[QVariable], numOracles:Int) extends ProgramDecl {
  override val variablesRecursive: VariableUse = {
    val cvars2 = ListSet(cvars: _*)
    val qvars2 = ListSet(qvars: _*)
    VariableUse(freeVariables = cvars2 ++ qvars2, written = cvars2, ambient = ListSet.empty,
      programs = ListSet.empty, overwritten = ListSet.empty, oracles=ListSet((1 to numOracles) map (_.toString) :_*),
      inner = ListSet(innerCVars:_*) ++ ListSet(innerQVars:_*),
      covered = if (numOracles==0) MaybeAllSet.all else MaybeAllSet.empty)
  }

  def declareInIsabelle(isabelle: Isabelle.Context): Isabelle.Context = {
    val op = Operation.implicitly[(BigInt,String,List[(String,Typ)],List[(String,Typ)],List[(String,Typ)],BigInt),BigInt]("declare_abstract_program")
    val vars = variablesRecursive
    val cvars = vars.classical map { v => (v.name, v.valueTyp) }
    val cwvars = vars.written collect { case v : CVariable => (v.name, v.valueTyp) }
    val qvars = vars.quantum map { v => (v.name, v.valueTyp) }
    val id = isabelle.isabelle.invoke(op, (isabelle.contextId, name, cvars.toList, cwvars.toList, qvars.toList, BigInt(numOracles)))
    new Context(isabelle.isabelle,id)
  }

  /*  {
      val cvarsAll = new mutable.LinkedHashSet[CVariable]()
      cvarsAll ++= cvars
      val qvarsAll = new mutable.LinkedHashSet[QVariable]()
      qvarsAll ++= qvars
      val ambAll = new mutable.LinkedHashSet[String]()
      val callsAll = new mutable.LinkedHashSet[ProgramDecl]()
      callsAll ++= calls
      for (p <- calls) {
        val (c, q, a, pr) = p.variablesRecursive
        cvarsAll ++= c
        qvarsAll ++= q
        ambAll ++= a
        callsAll ++= pr
      }
      (cvarsAll.toList, qvarsAll.toList, ambAll.toList, callsAll.toList)
    }*/
  override def toStringMultiline: String = {
    val calls = if (numOracles==0) "" else " calls " + Seq.fill(numOracles)("?").mkString(", ")
    val vars = (cvars ::: qvars) map { _.name } mkString ", "
    s"adversary $name vars $vars$calls"
  }
}

final case class ConcreteProgramDecl(environment: Environment, name:String, oracles:List[String], program:Block) extends ProgramDecl {
  override val numOracles: Int = oracles.length
  lazy val ambientVars: List[String] = {
    val vars = new mutable.LinkedHashSet[String]
    def scan(st:Statement) : Unit = st match {
      case Local(_,body) => scan(body)
      case Block(sts@_*) => sts.foreach(scan)
      case Call(_,_*) =>
      case Assign(_,e) =>
        vars ++= e.variables.filter(environment.ambientVariables.contains)
      case Sample(_,e) =>
        vars ++= e.variables.filter(environment.ambientVariables.contains)
      case QApply(_,e) =>
        vars ++= e.variables.filter(environment.ambientVariables.contains)
      case While(e,body) =>
        vars ++= e.variables.filter(environment.ambientVariables.contains)
        scan(body)
      case IfThenElse(e,thenBranch,elseBranch) =>
        vars ++= e.variables.filter(environment.ambientVariables.contains)
        scan(thenBranch)
        scan(elseBranch)
      case Measurement(_, _,e) =>
        vars ++= e.variables.filter(environment.ambientVariables.contains)
      case QInit(_,e) =>
        vars ++= e.variables.filter(environment.ambientVariables.contains)
    }
    scan(program)
    vars.toList
  }

  override lazy val variablesRecursive: VariableUse =
    program.variableUse(environment)

  /*{
    val qvars = new mutable.LinkedHashSet[QVariable]
    val cvars = new mutable.LinkedHashSet[CVariable]
    def scan(st:Statement) : Unit = st match {
      case Block(sts@_*) => sts.foreach(scan)
      case Call(n) =>
        val (c,q) = environment.programs(n).variablesRecursive
        cvars ++= c
        qvars ++= q
      case Assign(v,e) =>
        cvars += v
        cvars ++= e.variables.flatMap(environment.cVariables.get)
      case Sample(v,e) =>
        cvars += v
        cvars ++= e.variables.flatMap(environment.cVariables.get)
      case QApply(loc,e) =>
        qvars ++= loc
        cvars ++= e.variables.flatMap(environment.cVariables.get)
      case While(e,body) =>
        cvars ++= e.variables.flatMap(environment.cVariables.get)
        scan(body)
      case IfThenElse(e,thenBranch,elseBranch) =>
        cvars ++= e.variables.flatMap(environment.cVariables.get)
        scan(thenBranch)
        scan(elseBranch)
      case Measurement(res,loc,e) =>
        cvars += res
        qvars ++= loc
        cvars ++= e.variables.flatMap(environment.cVariables.get)
      case QInit(loc,e) =>
        qvars ++= loc
        cvars ++= e.variables.flatMap(environment.cVariables.get)
    }
    scan(program)
//    println(s"variablesRecursive $name, $cvars, $qvars")
    (cvars.toList, qvars.toList)
  }*/
  def declareInIsabelle(context: Isabelle.Context): Isabelle.Context = {
    val op = Operation.implicitly[(BigInt,String,List[(String,Typ)],List[(String,Typ)],List[(String,Typ)],List[String],Statement),BigInt]("declare_concrete_program")
    val vars = variablesRecursive
    val cvars = vars.classical map { v => (v.name, v.valueTyp) }
    val cwvars = vars.written collect { case v : CVariable => (v.name, v.valueTyp) }
    val qvars = vars.quantum map { v => (v.name, v.valueTyp) }
    val id = context.isabelle.invoke(op, (context.contextId, name, cvars.toList, cwvars.toList, qvars.toList, oracles, program))
    new Context(context.isabelle, id)
  }

  override def toStringMultiline: String = {
    val args = if (oracles.isEmpty) "" else "(" + oracles.mkString(",") + ")"
    s"program $name$args = {\n${this.program.toStringMultiline("  ")}\n}"
  }
}

