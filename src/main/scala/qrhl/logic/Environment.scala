package qrhl.logic

import qrhl.UserException

import scala.collection.mutable

// Environments
final class Environment private
  (val cVariables : Map[String,CVariable],
   val qVariables : Map[String,QVariable],
   val ambientVariables : Map[String,Typ], // variables used in the ambient logic
   val indexedNames : Set[String], // all variable names together, program variables indexed with 1/2
   val nonindexedNames : Set[String], // all variable names together, without 1/2-index
   val programs : Map[String,ProgramDecl]) {
//  def getCVariable(name: String): CVariable = cVariables(name)

  def declareVariable(name: String, typ: Typ, quantum:Boolean=false): Environment = {
    assert(!nonindexedNames.contains(name))
    val nonidxNames = nonindexedNames + name

    val newIdxNames = List(Variable.index1(name),Variable.index2(name))
    for (n <- newIdxNames)
      if (indexedNames.contains(n))
        throw UserException(s"Indexed form $n of variable $name already defined")
//    assert(!indexedNames.contains(n))
    val idxNames = indexedNames ++ newIdxNames

    assert(!cVariables.contains(name))
    assert(!qVariables.contains(name))
    if (quantum)
      copy(qVariables = qVariables.updated(name, QVariable(name,typ)),
        indexedNames=idxNames, nonindexedNames = nonidxNames)
    else
      copy(cVariables = cVariables.updated(name, CVariable(name,typ)),
        indexedNames=idxNames, nonindexedNames = nonidxNames)
  }

  def declareAmbientVariable(name: String, typ:Typ) : Environment = {
    assert(!nonindexedNames.contains(name))
    assert(!indexedNames.contains(name))
    copy(ambientVariables=ambientVariables.updated(name, typ),
      indexedNames = indexedNames+name,
      nonindexedNames = nonindexedNames+name)
  }

  def declareProgram(name: String, program: Block): Environment = {
    if (programs.contains(name))
      throw UserException(s"A program with name $name was already declared.")
    copy(programs=programs.updated(name, ConcreteProgramDecl(this,name,program)))
  }


  private def copy(cVariables:Map[String,CVariable]=cVariables,
                   qVariables:Map[String,QVariable]=qVariables,
                   ambientVariables:Map[String,Typ]=ambientVariables,
                   indexedNames : Set[String]=indexedNames,
                   nonindexedNames : Set[String]=nonindexedNames,
                   programs:Map[String,ProgramDecl]=programs) =
    new Environment(cVariables=cVariables, qVariables=qVariables, programs=programs,
      indexedNames=indexedNames, ambientVariables=ambientVariables, nonindexedNames=nonindexedNames)
}

object Environment {
  val empty = new Environment(cVariables=Map.empty, qVariables=Map.empty,
    ambientVariables=Map.empty, indexedNames=Set.empty, programs=Map.empty,
    nonindexedNames=Set.empty)
}

sealed trait ProgramDecl {
  val variablesRecursive : (List[CVariable],List[QVariable])
//  val variables : (List[CVariable],List[QVariable])
//  val subprograms : List[ProgramDecl]
  val name: String }
final case class AbstractProgramDecl(name:String) extends ProgramDecl {
  override val variablesRecursive: (List[CVariable], List[QVariable]) = ???
}
final case class ConcreteProgramDecl(environment: Environment, name:String, program:Block) extends ProgramDecl {
  override val variablesRecursive: (List[CVariable], List[QVariable]) = {
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
    }
    scan(program)
//    println(s"variablesRecursive $name, $cvars, $qvars")
    (cvars.toList, qvars.toList)
  }
}

