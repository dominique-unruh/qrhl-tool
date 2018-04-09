package qrhl.logic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure
import qrhl.isabelle.Isabelle

import scala.collection.mutable


// Programs
sealed trait Statement {
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

class Block(val statements:List[Statement]) extends Statement {
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
}
final case class Sample(variable:CVariable, expression:Expression) extends Statement {
  override def toString: String = s"""${variable.name} <$$ $expression;"""
  override def inline(name: String, statement: Statement): Statement = this

  override def checkWelltyped(): Unit =
    expression.checkWelltyped(Isabelle.distrT(variable.isabelleTyp))
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
}
final case class While(condition:Expression, body: Block) extends Statement {
  override def inline(name: String, program: Statement): Statement =
    While(condition,body.inline(name,program))
  override def toString: String = s"while ($condition) $body"

  override def checkWelltyped(): Unit = {
    condition.checkWelltyped(HOLogic.boolT)
    body.checkWelltyped()
  }
}
final case class QInit(location:List[QVariable], expression:Expression) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"${location.map(_.name).mkString(",")} <q $expression;"

  override def checkWelltyped(): Unit = {
    val expected = pure.Type("Bounded_Operator.vector",List(Isabelle.tupleT(location.map(_.typ.isabelleTyp):_*)))
    expression.checkWelltyped(expected)
  }
}
final case class QApply(location:List[QVariable], expression:Expression) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"on ${location.map(_.name).mkString(",")} apply $expression;"

  override def checkWelltyped(): Unit = {
    val varType = Isabelle.tupleT(location.map(_.typ.isabelleTyp):_*)
    val expected = pure.Type("Bounded_Operator.bounded",List(varType,varType))
    expression.checkWelltyped(expected)

  }
}
final case class Measurement(result:CVariable, location:List[QVariable], e:Expression) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"${result.name} <- measure ${location.map(_.name).mkString(",")} in $e;"

  override def checkWelltyped(): Unit = {
    val expected = pure.Type("QRHL_Core.measurement",List(result.isabelleTyp, Isabelle.tupleT(location.map(_.typ.isabelleTyp):_*)))
    e.checkWelltyped(expected)
  }
}
final case class Call(name:String) extends Statement {
  override def toString: String = s"call $name;"
  override def inline(name: String, program: Statement): Statement = this

  override def checkWelltyped(): Unit = {}
}
