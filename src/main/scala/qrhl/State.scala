package qrhl

import java.nio.file.{Files, Path, Paths}

import info.hupel.isabelle.Operation
import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.{Type, Context => IContext, Typ => ITyp}
import org.log4s
import qrhl.isabelle.Isabelle
import qrhl.logic._
import qrhl.toplevel.{Command, Parser, ParserContext}

import scala.annotation.tailrec

sealed trait Subgoal {
  def simplify(isabelle: Isabelle.Context, facts: List[String]): Subgoal

  /** Checks whether all isabelle terms in this goal are well-typed.
    * Should always succeed, unless there are bugs somewhere. */
  def checkWelltyped(): Unit

  /** This goal as a boolean expression. If it cannot be expressed in Isabelle, a different,
    * logically weaker expression is returned. */
  def toExpression: Expression

  def checkVariablesDeclared(environment: Environment): Unit

  def containsAmbientVar(x: String) : Boolean

  @tailrec
  final def addAssumptions(assms: List[Expression]): Subgoal = assms match {
    case Nil => this
    case a::as => addAssumption(a).addAssumptions(as)
  }

  def addAssumption(assm: Expression): Subgoal
}

object QRHLSubgoal {
  private val logger = log4s.getLogger
}

final case class QRHLSubgoal(left:Block, right:Block, pre:Expression, post:Expression, assumptions:List[Expression]) extends Subgoal {
  override def toString: String = {
    val assms = if (assumptions.isEmpty) "" else
      s"Assumptions:\n${assumptions.map(a => s"* $a\n").mkString}\n"
    s"${assms}Pre:   $pre\nLeft:  ${left.toStringNoParens}\nRight: ${right.toStringNoParens}\nPost:  $post"
  }

  override def checkVariablesDeclared(environment: Environment): Unit = {
    for (x <- pre.variables)
      if (!environment.variableExistsForPredicate(x))
        throw UserException(s"Undeclared variable $x in precondition")
    for (x <- post.variables)
      if (!environment.variableExistsForPredicate(x))
        throw UserException(s"Undeclared variable $x in postcondition")
    for (x <- left.variablesDirect)
      if (!environment.variableExistsForProg(x))
        throw UserException(s"Undeclared variable $x in left program")
    for (x <- right.variablesDirect)
      if (!environment.variableExistsForProg(x))
        throw UserException(s"Undeclared variable $x in left program")
    for (a <- assumptions; x <- a.variables)
      if (!environment.variableExists(x))
        throw UserException(s"Undeclared variable $x in assumptions")
  }

  /** Returns the expression "True" */
  override def toExpression: Expression = Expression.trueExp(pre.isabelle)

  /** Not including ambient vars in nested programs (via Call) */
  override def containsAmbientVar(x: String): Boolean = {
    pre.variables.contains(x) || post.variables.contains(x) ||
      left.variablesDirect.contains(x) || right.variablesDirect.contains(x) ||
      assumptions.exists(_.variables.contains(x))
  }

  override def addAssumption(assm: Expression): QRHLSubgoal = {
    assert(assm.typ.isabelleTyp==HOLogic.boolT)
    QRHLSubgoal(left,right,pre,post,assm::assumptions)
  }

  /** Checks whether all isabelle terms in this goal are well-typed.
    * Should always succeed, unless there are bugs somewhere. */
  override def checkWelltyped(): Unit = {
    for (a <- assumptions) a.checkWelltyped(HOLogic.boolT)
    left.checkWelltyped()
    right.checkWelltyped()
    pre.checkWelltyped(Isabelle.predicateT)
    post.checkWelltyped(Isabelle.predicateT)
  }

  override def simplify(isabelle: Isabelle.Context, facts: List[String]): QRHLSubgoal = {
//    if (assumptions.nonEmpty) QRHLSubgoal.logger.warn("Not using assumptions for simplification")
    val assms2: List[Expression] =
      assumptions.map(_.simplify(isabelle,facts)).filter(_.isabelleTerm!=HOLogic.True)
    QRHLSubgoal(left, right, pre.simplify(isabelle,facts), post.simplify(isabelle,facts), assms2)
  }
}

final case class AmbientSubgoal(goal: Expression) extends Subgoal {
  override def toString: String = goal.toString

  override def checkVariablesDeclared(environment: Environment): Unit =
    for (x <- goal.variables)
      if (!environment.variableExists(x))
        throw UserException(s"Undeclared variable $x")

  /** This goal as a boolean expression. */
  override def toExpression: Expression = goal

  override def containsAmbientVar(x: String): Boolean = goal.variables.contains(x)

  override def addAssumption(assm: Expression): AmbientSubgoal = {
    assert(assm.typ.isabelleTyp == HOLogic.boolT)
    AmbientSubgoal(assm.implies(goal))
  }

  /** Checks whether all isabelle terms in this goal are well-typed.
    * Should always succeed, unless there are bugs somewhere. */
  override def checkWelltyped(): Unit = goal.checkWelltyped(HOLogic.boolT)

  override def simplify(isabelle: Isabelle.Context, facts: List[String]): AmbientSubgoal =
    AmbientSubgoal(goal.simplify(isabelle,facts))
}

trait Tactic {
  def apply(state: State, goal : Subgoal) : List[Subgoal]
}

case class UserException(msg:String) extends RuntimeException(msg)

/** A path together with a last-modification time. */
class FileTimeStamp(val file:Path) {
  private val time = Files.getLastModifiedTime(file)
  /** Returns whether the file has changed since the FileTimeStamp was created. */
  def changed : Boolean = time!=Files.getLastModifiedTime(file)

  override def toString: String = s"$file@$time"
}

class State private (val environment: Environment,
                     val goal: List[Subgoal],
                     val currentLemma: Option[(String,Expression)],
                     val isabelle: Option[Isabelle.Context],
                     val boolT: Typ,
                     val predicateT: Typ,
                     val dependencies: List[FileTimeStamp],
                     val programT: Typ) {
  def qed: State = {
    assert(currentLemma.isDefined)
    assert(goal.isEmpty)

    val (name,prop) = currentLemma.get
    val isa = if (name!="") isabelle.map(_.addAssumption(name,prop.isabelleTerm)) else isabelle
    copy(isabelle=isa, currentLemma=None)
  }

  def declareProgram(name: String, program: Block): State = {
    for (x <- program.variablesDirect)
      if (!environment.variableExistsForProg(x))
        throw UserException(s"Undeclared variable $x in program")

    if (isabelle.isEmpty) throw UserException("Missing isabelle command.")
    if (this.environment.variableExists(name))
      throw UserException(s"Name $name already used for a variable or program.")
    val isa = isabelle.get.declareVariable(name, programT.isabelleTyp)

    copy(environment = environment.declareProgram(name, program))
  }

  def declareAdversary(name: String, cvars: Seq[CVariable], qvars: Seq[QVariable]): State = {
    copy(environment = environment.declareAdversary(name, cvars, qvars))
  }


  def applyTactic(tactic:Tactic) : State = goal match {
    case Nil =>
      throw UserException("No pending proof")
    case (subgoal::subgoals) =>
      copy(goal=tactic.apply(this,subgoal)++subgoals)
  }

  private def copy(environment:Environment=environment,
                   goal:List[Subgoal]=goal,
                   isabelle:Option[Isabelle.Context]=isabelle,
                   boolT:Typ=boolT,
                   predicateT:Typ=predicateT,
                   programT:Typ=programT,
                   dependencies:List[FileTimeStamp]=dependencies,
                   currentLemma:Option[(String,Expression)]=currentLemma) : State =
    new State(environment=environment, goal=goal, isabelle=isabelle, boolT=boolT, predicateT=predicateT,
      currentLemma=currentLemma, programT=programT, dependencies=dependencies)

  def openGoal(name:String, goal:Subgoal) : State = this.currentLemma match {
    case None =>
      goal.checkVariablesDeclared(environment)
      copy(goal=List(goal), currentLemma=Some((name,goal.toExpression)))
    case _ => throw UserException("There is still a pending proof.")
  }

  override def toString: String = goal match {
    case Nil => "No current goal."
    case _ =>
      s"${goal.size} subgoals:\n\n" + goal.mkString("\n\n")
  }

  lazy val parserContext = ParserContext(isabelle=isabelle, environment=environment, boolT = boolT, predicateT = predicateT)

  def parseCommand(str:String): Command = {
    implicit val parserContext: ParserContext = this.parserContext
    Parser.parseAll(Parser.command,str) match {
      case Parser.Success(cmd2,_) => cmd2
      case res @ Parser.NoSuccess(msg, _) =>
        throw UserException(msg)
    }
  }

  def parseExpression(typ:Typ, str:String): Expression = {
    implicit val parserContext: ParserContext = this.parserContext
    Parser.parseAll(Parser.expression(typ),str) match {
      case Parser.Success(cmd2,_) => cmd2
      case res @ Parser.NoSuccess(msg, _) =>
        throw UserException(msg)
    }
  }

  def loadIsabelle(path:String, theory:Option[String]) : State = {
    assert(isabelle.isEmpty)
    val isa = new Isabelle(path)
    // since this is likely to happen when an existing Isabelle is reloaded, give the GC a chance to remove that existing Isabelle
    System.gc()
    loadIsabelle(isa,theory)
  }

  def loadIsabelle(isabelle: Isabelle, theory:Option[String]) : State = {
    val (isa,files) = theory match {
      case None =>
        (isabelle.getQRHLContextWithFiles(), dependencies)
      case Some(thy) =>
        val filename = Paths.get(thy+".thy")
        (isabelle.getQRHLContextWithFiles(thy), new FileTimeStamp(filename) :: dependencies)
    }
    copy(isabelle = Some(isa), boolT = Typ.bool(isa), predicateT=Typ(isa,"QRHL_Core.predicate"), programT=Typ(isa,"QRHL_Core.program"), dependencies=files)
  }

  def filesChanged : List[Path] = {
    dependencies.filter(_.changed).map(_.file)
  }

  private def declare_quantum_variable(isabelle: Isabelle.Context, name: String, typ: ITyp) : Isabelle.Context = {
    isabelle.map(id => isabelle.isabelle.invoke(State.declare_quantum_variable, (name,typ,id)))
  }

  private def declare_classical_variable(isabelle: Isabelle.Context, name: String, typ: ITyp) : Isabelle.Context = {
    isabelle.map(id => isabelle.isabelle.invoke(State.declare_classical_variable, (name,typ,id)))
  }

  def declareVariable(name: String, typ: Typ, quantum: Boolean = false): State = {
    val newEnv = environment.declareVariable(name, typ, quantum = quantum)
      .declareAmbientVariable(name+"_var", typ)
      .declareAmbientVariable(Variable.index1(name)+"_var", typ)
      .declareAmbientVariable(Variable.index2(name)+"_var", typ)
    if (isabelle.isEmpty) throw UserException("Missing isabelle command.")
    val isa = isabelle.get
    val typ1 = typ.isabelleTyp
    val typ2 = if (quantum) Type("QRHL_Core.qvariable",List(typ1)) else typ1
    var newIsa = isa.declareVariable(name, typ2)
      .declareVariable(Variable.index1(name), typ2)
      .declareVariable(Variable.index2(name), typ2)
    if (quantum) {
      newIsa = declare_quantum_variable(newIsa, name, typ1)
    }
    else {
      newIsa = declare_classical_variable(newIsa, name, typ1)
    }
    copy(environment = newEnv, isabelle = Some(newIsa))
  }

  def declareAmbientVariable(name: String, typ: Typ): State = {
    val newEnv = environment.declareAmbientVariable(name, typ)
    if (isabelle.isEmpty) throw UserException("Missing isabelle command.")
    val isa = isabelle.get.declareVariable(name, typ.isabelleTyp)
    copy(environment = newEnv, isabelle = Some(isa))
  }
}

object State {
  val empty = new State(environment=Environment.empty,goal=Nil,isabelle=None,
    boolT=null, predicateT=null, dependencies=Nil, programT=null, currentLemma=None)
//  private[State] val defaultIsabelleTheory = "QRHL"

  val declare_quantum_variable: Operation[(String, ITyp, BigInt), BigInt] =
    Operation.implicitly[(String,ITyp,BigInt), BigInt]("declare_quantum_variable")

  val declare_classical_variable: Operation[(String, ITyp, BigInt), BigInt] =
    Operation.implicitly[(String,ITyp,BigInt), BigInt]("declare_classical_variable")
}
