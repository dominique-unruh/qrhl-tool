package qrhl.logic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure
import info.hupel.isabelle.pure.{App, Const, Free, Term}
import qrhl.isabelle.Isabelle

import scala.collection.mutable


// Programs
sealed trait Statement {
  def programTerm : Term


  /** Returns all variables used in the statement.
    * @param recurse Recurse into programs embedded via Call
    * @return (cvars,qvars,avars,pnames) Classical, quantum, ambient variables, program declarations. */
  def cqapVariables(environment: Environment, recurse: Boolean) : (List[CVariable],List[QVariable],List[String],List[ProgramDecl]) = {
    val cvars = new mutable.LinkedHashSet[CVariable]()
    val qvars = new mutable.LinkedHashSet[QVariable]()
    val avars = new mutable.LinkedHashSet[String]()
    val progs = new mutable.LinkedHashSet[ProgramDecl]()
    cqapVariables(environment,cvars,qvars,avars,progs,recurse=recurse)
    (cvars.toList,qvars.toList,avars.toList,progs.toList)
  }

  def cqapVariables(environment : Environment, cvars : mutable.Set[CVariable], qvars: mutable.Set[QVariable],
                   avars : mutable.Set[String], progs : mutable.Set[ProgramDecl], recurse:Boolean): Unit = {
    def collectExpr(e:Expression):Unit = e.caVariables(environment,cvars,avars)
    def collect(s:Statement) : Unit = s match {
      case Block(ss @ _*) => ss.foreach(collect)
      case Assign(v,e) => cvars += v; collectExpr(e)
      case Sample(v,e) => cvars += v; collectExpr(e)
      case Call(name) =>
        val p = environment.programs(name)
        progs += p
        if (recurse) {
          val (cv,qv,av,ps) = p.variablesRecursive
          cvars ++= cv; qvars ++= qv; avars ++= av; progs ++= ps
        }
      case While(e,body) => collectExpr(e); collect(body)
      case IfThenElse(e,p1,p2) => collectExpr(e); collect(p1); collect(p2)
      case QInit(vs,e) => qvars ++= vs; collectExpr(e)
      case Measurement(v,vs,e) => cvars += v; collectExpr(e); qvars ++= vs
      case QApply(vs,e) => qvars ++= vs; collectExpr(e)
    }
    collect(this)
  }

  def checkWelltyped(): Unit

  /** All ambient and program variables.
    * Not including nested programs (via Call) */
  def variablesDirect : Set[String] = {
    val vars = new mutable.SetBuilder[String,Set[String]](Set.empty)
    def collect(s:Statement) : Unit = s match {
      case Block(ss @ _*) => ss.foreach(collect)
      case Assign(v,e) => vars += v.name; vars ++= e.variables
      case Sample(v,e) => vars += v.name; vars ++= e.variables
      case Call(name) =>
      case While(e,body) => vars ++= e.variables; collect(body)
      case IfThenElse(e,p1,p2) => vars ++= e.variables; collect(p1); collect(p2)
      case QInit(vs,e) => vars ++= vs.map(_.name); vars ++= e.variables
      case Measurement(v,vs,e) => vars += v.name; vars ++= vs.map(_.name); vars ++= e.variables
      case QApply(vs,e) => vars ++= vs.map(_.name); vars ++= e.variables
    }
    collect(this)
    vars.result
  }

  /** Including nested programs (via Call). (Missing ambient variables from nested calls.) */
  def variablesAll(env:Environment) : Set[String] = {
    val vars = new mutable.SetBuilder[String,Set[String]](Set.empty)
    def collect(s:Statement) : Unit = s match {
      case Block(ss @ _*) => ss.foreach(collect)
      case Assign(v,e) => vars += v.name; vars ++= e.variables
      case Sample(v,e) => vars += v.name; vars ++= e.variables
      case Call(name) =>
        val (cvars,qvars,_,_) = env.programs(name).variablesRecursive
        vars ++= cvars.map(_.name)
        vars ++= qvars.map(_.name)
      case While(e,body) => vars ++= e.variables; collect(body)
      case IfThenElse(e,p1,p2) => vars ++= e.variables; collect(p1); collect(p2)
      case QInit(vs,e) => vars ++= vs.map(_.name); vars ++= e.variables
      case Measurement(v,vs,e) => vars += v.name; vars ++= vs.map(_.name); vars ++= e.variables
      case QApply(vs,e) => vars ++= vs.map(_.name); vars ++= e.variables
    }
    collect(this)
    vars.result
  }

  def inline(name: String, program: Statement): Statement
}

object Statement {
  def decodeFromListTerm(context: Isabelle.Context, t:Term) : Block = {
    val statements = Isabelle.dest_list(t).map(decodeFromTerm(context,_))
    Block(statements:_*)
  }

  def decodeFromTerm(context: Isabelle.Context, t:Term) : Statement = t match {
    case App(Const(Isabelle.block.name,_), statements) => decodeFromListTerm(context, statements)
    case App(App(Const(Isabelle.assignName,_),x),e) =>
      Assign(CVariable.fromTerm_var(context, x),Expression.decodeFromExpression(context, e))
    case App(App(Const(Isabelle.sampleName,_),x),e) =>
      Sample(CVariable.fromTerm_var(context, x),Expression.decodeFromExpression(context, e))
    case Free(name,_) => Call(name)
    case App(App(Const(Isabelle.whileName,_),e),body) =>
      While(Expression.decodeFromExpression(context,e), decodeFromListTerm(context, body))
    case App(App(App(Const(Isabelle.ifthenelseName,_),e),thenBody),elseBody) =>
      IfThenElse(Expression.decodeFromExpression(context,e),
        decodeFromListTerm(context, thenBody), decodeFromListTerm(context, elseBody))
    case App(App(Const(Isabelle.qinitName, _), vs), e) =>
      QInit(QVariable.fromQVarList(context, vs), Expression.decodeFromExpression(context,e))
    case App(App(Const(Isabelle.qapplyName, _), vs), e) =>
      QApply(QVariable.fromQVarList(context, vs), Expression.decodeFromExpression(context,e))
    case App(App(App(Const(Isabelle.measurementName, _), x), vs), e) =>
      Measurement(CVariable.fromTerm_var(context, x), QVariable.fromQVarList(context, vs),
        Expression.decodeFromExpression(context,e))
  }
}

class Block(val statements:List[Statement]) extends Statement {
  lazy val programListTerm: Term = Isabelle.mk_list(Isabelle.programT, statements.map(_.programTerm))
  override lazy val programTerm : Term = Isabelle.block $ programListTerm

  override def equals(o: Any): Boolean = o match {
    case Block(st @ _*) => statements==st
    case _ => false
  }

  override def toString: String = statements match {
    case Nil => "{}"
    case List(s) => s.toString
    case _ => "{ " + statements.map{ _.toString}.mkString(" ") + " }"
  }
  def toStringNoParens: String = statements match {
    case Nil => "skip;"
    case _ => statements.map{ _.toString }.mkString(" ")
  }
  def length : Int = statements.size

  def inline(environment: Environment, name: String): Block = {
    inline(name: String, environment.programs(name).asInstanceOf[ConcreteProgramDecl].program)
  }

  override def inline(name:String, program:Statement): Block = {
    val programStatements = program match {
      case Block(st @_*) => st
      case _ => List(program)
    }
    val newStatements = for (s <- statements;
                             s2 <- s match {
                               case Call(name2) if name==name2 => programStatements
                               case _ => List(s.inline(name,program))
                             }) yield s2
    Block(newStatements : _*)
  }

  override def checkWelltyped(): Unit =
    for (s <- statements) s.checkWelltyped()
}

object Block {
  def apply(statements: Statement*) : Block = new Block(statements.toList)
  val empty = Block()
  def unapplySeq(block: Block): Some[Seq[Statement]] = Some(block.statements)
}


final case class Assign(variable:CVariable, expression:Expression) extends Statement {
  override def toString: String = s"""${variable.name} <- $expression;"""
  override def inline(name: String, statement: Statement): Statement = this

  override def checkWelltyped(): Unit =
    expression.checkWelltyped(variable.typ)

  override lazy val programTerm: Term =
    Isabelle.assign(variable.typ.isabelleTyp) $ variable.isabelleTerm_var $ expression.encodeAsExpression
}
final case class Sample(variable:CVariable, expression:Expression) extends Statement {
  override def toString: String = s"""${variable.name} <$$ $expression;"""
  override def inline(name: String, statement: Statement): Statement = this

  override def checkWelltyped(): Unit =
    expression.checkWelltyped(Isabelle.distrT(variable.isabelleTyp))

  override lazy val programTerm: Term =
    Isabelle.sample(variable.typ.isabelleTyp) $ variable.isabelleTerm_var $ expression.encodeAsExpression
}
final case class IfThenElse(condition:Expression, thenBranch: Block, elseBranch: Block) extends Statement {
  override def inline(name: String, program: Statement): Statement =
    IfThenElse(condition,thenBranch.inline(name,program),elseBranch.inline(name,program))
  override def toString: String = s"if ($condition) $thenBranch else $elseBranch;"

  override def checkWelltyped(): Unit = {
    condition.checkWelltyped(HOLogic.boolT)
    thenBranch.checkWelltyped()
    elseBranch.checkWelltyped()
  }
  override lazy val programTerm: Term =
    Isabelle.ifthenelse $ condition.encodeAsExpression $ thenBranch.programListTerm $ elseBranch.programListTerm
}
final case class While(condition:Expression, body: Block) extends Statement {
  override def inline(name: String, program: Statement): Statement =
    While(condition,body.inline(name,program))
  override def toString: String = s"while ($condition) $body"

  override def checkWelltyped(): Unit = {
    condition.checkWelltyped(HOLogic.boolT)
    body.checkWelltyped()
  }
  override lazy val programTerm: Term =
    Isabelle.whileProg $ condition.encodeAsExpression $ body.programListTerm
}
final case class QInit(location:List[QVariable], expression:Expression) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"${location.map(_.name).mkString(",")} <q $expression;"

  override def checkWelltyped(): Unit = {
    val expected = pure.Type("Complex_L2.vector",List(Isabelle.tupleT(location.map(_.typ.isabelleTyp):_*)))
    expression.checkWelltyped(expected)
  }
  override lazy val programTerm: Term =
    Isabelle.qinit(Isabelle.tupleT(location.map(_.typ.isabelleTyp):_*)) $ Isabelle.qvarTuple_var(location) $ expression.encodeAsExpression
}
final case class QApply(location:List[QVariable], expression:Expression) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"on ${location.map(_.name).mkString(",")} apply $expression;"

  override def checkWelltyped(): Unit = {
    val varType = Isabelle.tupleT(location.map(_.typ.isabelleTyp):_*)
    val expected = pure.Type("Bounded_Operators.bounded",List(varType,varType))
    expression.checkWelltyped(expected)
  }
  override lazy val programTerm: Term =
    Isabelle.qapply(Isabelle.tupleT(location.map(_.typ.isabelleTyp):_*)) $ Isabelle.qvarTuple_var(location) $ expression.encodeAsExpression
}
final case class Measurement(result:CVariable, location:List[QVariable], e:Expression) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"${result.name} <- measure ${location.map(_.name).mkString(",")} in $e;"

  override def checkWelltyped(): Unit = {
    val expected = pure.Type("QRHL_Core.measurement",List(result.isabelleTyp, Isabelle.tupleT(location.map(_.typ.isabelleTyp):_*)))
    e.checkWelltyped(expected)
  }
  override lazy val programTerm: Term =
    Isabelle.measurement(Isabelle.tupleT(location.map(_.typ.isabelleTyp):_*), result.typ.isabelleTyp) $
      result.isabelleTerm_var $ Isabelle.qvarTuple_var(location) $ e.encodeAsExpression
}
final case class Call(name:String) extends Statement {
  override def toString: String = s"call $name;"
  override def inline(name: String, program: Statement): Statement = this

  override def checkWelltyped(): Unit = {}
  override lazy val programTerm: Term = Free(name,Isabelle.programT)
}
