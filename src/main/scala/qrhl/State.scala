package qrhl

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.ml
import info.hupel.isabelle.pure.{Type, Typ => ITyp, Context => IContext}
import qrhl.isabelle.Isabelle
import qrhl.logic._
import qrhl.toplevel.ParserContext

sealed trait Subgoal {
  /** This goal as a boolean expression. If it cannot be expressed in Isabelle, a different,
    * logically weaker expression is returned. */
  def toExpression: Expression

  def checkVariablesDeclared(environment: Environment): Unit
}

final case class QRHLSubgoal(left:Block, right:Block, pre:Expression, post:Expression) extends Subgoal {
  override def toString: String = s"Pre:   $pre\nLeft:  ${left.toStringNoParens}\nRight: ${right.toStringNoParens}\nPost:  $post"

  override def checkVariablesDeclared(environment: Environment): Unit = {
    for (x <- pre.variables)
      if (!environment.variableExistsForAssertion(x))
        throw UserException(s"Undeclared variable $x in precondition")
    for (x <- post.variables)
      if (!environment.variableExistsForAssertion(x))
        throw UserException(s"Undeclared variable $x in postcondition")
    for (x <- left.variablesDirect)
      if (!environment.variableExistsForProg(x))
        throw UserException(s"Undeclared variable $x in left program")
    for (x <- right.variablesDirect)
      if (!environment.variableExistsForProg(x))
        throw UserException(s"Undeclared variable $x in left program")
  }

  /** Returns the expression "True" */
  override def toExpression: Expression = Expression(pre.isabelle, HOLogic.True)
}

final case class AmbientSubgoal(goal: Expression) extends Subgoal {
  override def toString: String = goal.toString

  override def checkVariablesDeclared(environment: Environment): Unit =
    for (x <- goal.variables)
      if (!environment.variableExists(x))
        throw UserException(s"Undeclared variable $x")

  /** This goal as a boolean expression. */
  override def toExpression: Expression = goal
}

trait Tactic {
  def apply(state: State, goal : Subgoal) : List[Subgoal]
}

case class UserException(msg:String) extends RuntimeException(msg)

class State private (val environment: Environment,
                     val goal: List[Subgoal],
                     val currentLemma: Option[(String,Expression)],
                     val isabelle: Option[Isabelle.Context],
                     val boolT: Typ,
                     val assertionT: Typ,
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
                   assertionT:Typ=assertionT,
                   programT:Typ=programT,
                   currentLemma:Option[(String,Expression)]=currentLemma) : State =
    new State(environment=environment, goal=goal, isabelle=isabelle, boolT=boolT, assertionT=assertionT,
      currentLemma=currentLemma, programT=programT)

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

  lazy val parserContext = ParserContext(isabelle=isabelle, environment=environment, boolT = boolT, assertionT = assertionT)

  def loadIsabelle(path:String, theory:Option[String]) : State = {
    assert(isabelle.isEmpty)
    val isa = new Isabelle(path)
    loadIsabelle(isa,theory)
  }

  def loadIsabelle(isabelle: Isabelle, theory:Option[String]) : State = {
    val isa = theory match {
      case None => isabelle.getContext(State.defaultIsabelleTheory)
      case Some(thy) => isabelle.getContextFile(thy)
    }
    copy(isabelle = Some(isa), boolT = Typ.bool(isa), assertionT=Typ(isa,"QRHL.assertion"), programT=Typ(isa,"QRHL.program"))
  }

  private def addQVariableNameAssumption(isabelle: Isabelle.Context, name: String, typ: ITyp) : Isabelle.Context = {
    val mlExpr = ml.Expr.uncheckedLiteral[String => ITyp => IContext => IContext]("QRHL.addQVariableNameAssumption")
    isabelle.map(mlExpr(name)(implicitly)(typ))
  }

  def declareVariable(name: String, typ: Typ, quantum: Boolean = false): State = {
    val newEnv = environment.declareVariable(name, typ, quantum = quantum)
    if (isabelle.isEmpty) throw UserException("Missing isabelle command.")
    val isa = isabelle.get
    val typ1 = typ.isabelleTyp
    val typ2 = if (quantum) Type("QRHL.qvariable",List(typ1)) else typ1
    var newIsa = isa.declareVariable(name, typ2)
      .declareVariable(Variable.index1(name), typ2)
      .declareVariable(Variable.index2(name), typ2)
    if (quantum) {
      newIsa = addQVariableNameAssumption(newIsa, Variable.index1(name), typ1)
      newIsa = addQVariableNameAssumption(newIsa, Variable.index2(name), typ1)
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
    boolT=null, assertionT=null, programT=null, currentLemma=None)
  private[State] val defaultIsabelleTheory = "QRHL_Protocol"
}