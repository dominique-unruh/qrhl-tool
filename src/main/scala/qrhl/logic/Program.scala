package qrhl.logic

import scala.collection.mutable


// Programs
sealed trait Statement {
  /** Not including nested programs (via Call) */
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

  /** Including nested programs (via Call) */
  def variablesAll(env:Environment) : Set[String] = {
    val vars = new mutable.SetBuilder[String,Set[String]](Set.empty)
    def collect(s:Statement) : Unit = s match {
      case Block(ss @ _*) => ss.foreach(collect)
      case Assign(v,e) => vars += v.name; vars ++= e.variables
      case Sample(v,e) => vars += v.name; vars ++= e.variables
      case Call(name) => env.programs(name)
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
}

object Block {
  def apply(statements: Statement*) : Block = new Block(statements.toList)
  val empty = Block()
  def unapplySeq(block: Block): Some[Seq[Statement]] = Some(block.statements)
}


final case class Assign(variable:CVariable, expression:Expression) extends Statement {
  override def toString: String = s"""${variable.name} <- $expression;"""
  override def inline(name: String, statement: Statement): Statement = this
}
final case class Sample(variable:CVariable, expression:Expression) extends Statement {
  override def toString: String = s"""${variable.name} <$$ $expression;"""
  override def inline(name: String, statement: Statement): Statement = this
}
final case class IfThenElse(condition:Expression, thenBranch: Block, elseBranch: Block) extends Statement {
  override def inline(name: String, program: Statement): Statement =
    IfThenElse(condition,thenBranch.inline(name,program),elseBranch.inline(name,program))
  override def toString: String = s"if ($condition) $thenBranch else $elseBranch;"
}
final case class While(condition:Expression, body: Block) extends Statement {
  override def inline(name: String, program: Statement): Statement =
    While(condition,body.inline(name,program))
  override def toString: String = s"while ($condition) $body;"
}
final case class QInit(location:List[QVariable], expression:Expression) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"${location.map(_.name).mkString(",")} <q $expression;"
}
final case class QApply(location:List[QVariable], expression:Expression) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"on ${location.map(_.name).mkString(",")} apply $expression;"
}
final case class Measurement(result:CVariable, location:List[QVariable], e:Expression) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"${result.name} <- measure ${location.map(_.name).mkString(",")} in $e;"
}
final case class Call(name:String) extends Statement {
  override def toString: String = s"call $name;"
  override def inline(name: String, program: Statement): Statement = this
}
