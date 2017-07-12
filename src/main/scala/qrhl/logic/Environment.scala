package qrhl.logic

import qrhl.UserException

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
    val newIdxNames = List(Variable.index1(name),Variable.index2(name))
    for (n <- newIdxNames) assert(!indexedNames.contains(n))
    val idxNames = indexedNames ++ newIdxNames

    assert(!nonindexedNames.contains(name))
    val nonidxNames = nonindexedNames + name

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

  def declareProgram(name: String, program: Block): _root_.qrhl.logic.Environment = {
    if (programs.contains(name))
      throw UserException(s"A program with name $name was already declared.")
    copy(programs=programs.updated(name, ConcreteProgramDecl(name,program)))
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

sealed trait ProgramDecl { val name: String }
final case class AbstractProgramDecl(name:String) extends ProgramDecl
final case class ConcreteProgramDecl(name:String, program:Block) extends ProgramDecl

