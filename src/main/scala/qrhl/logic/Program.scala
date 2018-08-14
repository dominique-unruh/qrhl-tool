package qrhl.logic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure
import info.hupel.isabelle.pure.{App, Const, Free, Term}
import qrhl.UserException
import qrhl.isabelle.Isabelle

import scala.collection.mutable


// Programs
sealed trait Statement {
  def programTerm(context: Isabelle.Context) : Term


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
      case Call(name, args @ _*) =>
        val p = environment.programs(name)
        progs += p
        args.foreach(collect)
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

  def checkWelltyped(context: Isabelle.Context): Unit

  /** All ambient and program variables.
    * Not including nested programs (via Call) */
  def variablesDirect : Set[String] = {
    val vars = new mutable.SetBuilder[String,Set[String]](Set.empty)
    def collect(s:Statement) : Unit = s match {
      case Block(ss @ _*) => ss.foreach(collect)
      case Assign(v,e) => vars += v.name; vars ++= e.variables
      case Sample(v,e) => vars += v.name; vars ++= e.variables
      case Call(_) =>
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
      case Call(name, args @ _*) =>
        val (cvars,qvars,_,_) = env.programs(name).variablesRecursive
        vars ++= cvars.map(_.name)
        vars ++= qvars.map(_.name)
        args.foreach(collect)
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
    case App(App(Const(Isabelle.instantiateOraclesName,_), Free(name,_)), args) =>
      throw UserException("Not yet implemented. Tell Dominique.")
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
    case _ => throw new RuntimeException(s"term $t cannot be decoded as a statement")
  }
}

class Block(val statements:List[Statement]) extends Statement {
  def programListTerm(context: Isabelle.Context): Term = Isabelle.mk_list(Isabelle.programT, statements.map(_.programTerm(context)))
  override def programTerm(context: Isabelle.Context) : Term = Isabelle.block $ programListTerm(context)

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
                               case Call(name2, args @ _*) if name==name2 =>
                                 assert(args.isEmpty, s"Cannot inline $s, oracles not supported.")
                                 programStatements
                               case _ => List(s.inline(name,program))
                             }) yield s2
    Block(newStatements : _*)
  }

  override def checkWelltyped(context: Isabelle.Context): Unit =
    for (s <- statements) s.checkWelltyped(context)
}

object Block {
  def apply(statements: Statement*) : Block = new Block(statements.toList)
  val empty = Block()
  def unapplySeq(block: Block): Some[Seq[Statement]] = Some(block.statements)
}


final case class Assign(variable:CVariable, expression:Expression) extends Statement {
  override def toString: String = s"""${variable.name} <- $expression;"""
  override def inline(name: String, statement: Statement): Statement = this

  override def checkWelltyped(context: Isabelle.Context): Unit =
    expression.checkWelltyped(context, variable.valueTyp)

  override def programTerm(context: Isabelle.Context): Term =
    Isabelle.assign(variable.valueTyp) $ variable.variableTerm $ expression.encodeAsExpression(context)
}
final case class Sample(variable:CVariable, expression:Expression) extends Statement {
  override def toString: String = s"""${variable.name} <$$ $expression;"""
  override def inline(name: String, statement: Statement): Statement = this

  override def checkWelltyped(context: Isabelle.Context): Unit =
    expression.checkWelltyped(context, Isabelle.distrT(variable.valueTyp))

  override def programTerm(context: Isabelle.Context): Term =
    Isabelle.sample(variable.valueTyp) $ variable.variableTerm $ expression.encodeAsExpression(context)
}
final case class IfThenElse(condition:Expression, thenBranch: Block, elseBranch: Block) extends Statement {
  override def inline(name: String, program: Statement): Statement =
    IfThenElse(condition,thenBranch.inline(name,program),elseBranch.inline(name,program))
  override def toString: String = s"if ($condition) $thenBranch else $elseBranch;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    condition.checkWelltyped(context, HOLogic.boolT)
    thenBranch.checkWelltyped(context)
    elseBranch.checkWelltyped(context)
  }
  override def programTerm(context: Isabelle.Context): Term =
    Isabelle.ifthenelse $ condition.encodeAsExpression(context) $ thenBranch.programListTerm(context) $ elseBranch.programListTerm(context)
}
final case class While(condition:Expression, body: Block) extends Statement {
  override def inline(name: String, program: Statement): Statement =
    While(condition,body.inline(name,program))
  override def toString: String = s"while ($condition) $body"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    condition.checkWelltyped(context, HOLogic.boolT)
    body.checkWelltyped(context)
  }
  override def programTerm(context: Isabelle.Context): Term =
    Isabelle.whileProg $ condition.encodeAsExpression(context) $ body.programListTerm(context)
}
final case class QInit(location:List[QVariable], expression:Expression) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"${location.map(_.name).mkString(",")} <q $expression;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    val expected = Isabelle.vectorT(Isabelle.tupleT(location.map(_.valueTyp):_*))
    expression.checkWelltyped(context, expected)
  }
  override def programTerm(context: Isabelle.Context): Term =
    Isabelle.qinit(Isabelle.tupleT(location.map(_.valueTyp):_*)) $ Isabelle.qvarTuple_var(location) $ expression.encodeAsExpression(context)
}
final case class QApply(location:List[QVariable], expression:Expression) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"on ${location.map(_.name).mkString(",")} apply $expression;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    val varType = Isabelle.tupleT(location.map(_.valueTyp):_*)
    val expected = pure.Type("Bounded_Operators.bounded",List(varType,varType))
    expression.checkWelltyped(context, expected)
  }
  override def programTerm(context: Isabelle.Context): Term =
    Isabelle.qapply(Isabelle.tupleT(location.map(_.valueTyp):_*)) $ Isabelle.qvarTuple_var(location) $ expression.encodeAsExpression(context)
}
final case class Measurement(result:CVariable, location:List[QVariable], e:Expression) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"${result.name} <- measure ${location.map(_.name).mkString(",")} in $e;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    val expected = pure.Type("QRHL_Core.measurement",List(result.variableTyp, Isabelle.tupleT(location.map(_.valueTyp):_*)))
    e.checkWelltyped(context, expected)
  }
  override def programTerm(context: Isabelle.Context): Term =
    Isabelle.measurement(Isabelle.tupleT(location.map(_.valueTyp):_*), result.valueTyp) $
      result.variableTerm $ Isabelle.qvarTuple_var(location) $ e.encodeAsExpression(context)
}
final case class Call(name:String, args:Call*) extends Statement {
  override def toString: String = "call "+toStringShort+";"
  def toStringShort: String =
    if (args.isEmpty) name else s"call $name(${args.map(_.toStringShort).mkString(",")})"
  override def inline(name: String, program: Statement): Statement = this

  override def checkWelltyped(context: Isabelle.Context): Unit = {}
  override def programTerm(context: Isabelle.Context): Term = {
    if (args.nonEmpty)
      throw UserException("Not yet implemented. Tell Dominique.")
    Free(name, Isabelle.programT)
  }
}
