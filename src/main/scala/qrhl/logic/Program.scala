package qrhl.logic

import info.hupel.isabelle.api.XML
import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.{Codec, Operation, XMLResult, pure}
import info.hupel.isabelle.pure.{App, Const, Free, Term}
import qrhl.UserException
import qrhl.isabelle.{Isabelle, RichTerm}

import scala.collection.mutable

// Implicits
import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec
import Statement.codec


// Programs
sealed trait Statement {
  def toBlock: Block = Block(this)

  @deprecated("too slow, use programTerm instead","now")
  def programTermOLD(context: Isabelle.Context) : Term

  def programTerm(context: Isabelle.Context): RichTerm = {
    context.isabelle.invoke(Statement.statement_to_term_op, (context.contextId, this))
  }


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
    def collectExpr(e:RichTerm):Unit = e.caVariables(environment,cvars,avars)
    def collect(s:Statement) : Unit = s match {
      case Block(ss @ _*) => ss.foreach(collect)
      case Assign(v,e) => cvars += v; collectExpr(e)
      case Sample(v,e) => cvars += v; collectExpr(e)
      case Call(name, args @ _*) =>
        val p = environment.programs(name)
        progs += p
        if (recurse) {
          val (cv,qv,av,ps) = p.variablesRecursive
          cvars ++= cv; qvars ++= qv; avars ++= av; progs ++= ps
        }
        args.foreach(collect)
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
      case Call(_, _*) =>
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
  @deprecated("Too slow","now")
  def decodeFromListTerm(context: Isabelle.Context, t:Term) : Block = {
    val statements = Isabelle.dest_list(t).map(decodeFromTerm(context,_))
    Block(statements:_*)
  }

  @deprecated("Too slow","now")
  def decodeFromTerm(context: Isabelle.Context, t:Term) : Statement = t match {
    case App(Const(Isabelle.block.name,_), statements) => decodeFromListTerm(context, statements)
    case App(App(Const(Isabelle.assignName,_),x),e) =>
      Assign(CVariable.fromTerm_var(context, x),RichTerm.decodeFromExpression(context, e))
    case App(App(Const(Isabelle.sampleName,_),x),e) =>
      Sample(CVariable.fromTerm_var(context, x),RichTerm.decodeFromExpression(context, e))
    case Free(name,_) => Call(name)
    case App(App(Const(Isabelle.instantiateOracles.name,_), Free(name,_)), args) =>
      val args2 = Isabelle.dest_list(args).map(decodeFromTerm(context,_).asInstanceOf[Call])
      Call(name,args2 : _*)
    case App(App(Const(Isabelle.whileName,_),e),body) =>
      While(RichTerm.decodeFromExpression(context,e), decodeFromListTerm(context, body))
    case App(App(App(Const(Isabelle.ifthenelseName,_),e),thenBody),elseBody) =>
      IfThenElse(RichTerm.decodeFromExpression(context,e),
        decodeFromListTerm(context, thenBody), decodeFromListTerm(context, elseBody))
    case App(App(Const(Isabelle.qinitName, _), vs), e) =>
      QInit(QVariable.fromQVarList(context, vs), RichTerm.decodeFromExpression(context,e))
    case App(App(Const(Isabelle.qapplyName, _), vs), e) =>
      QApply(QVariable.fromQVarList(context, vs), RichTerm.decodeFromExpression(context,e))
    case App(App(App(Const(Isabelle.measurementName, _), x), vs), e) =>
      Measurement(CVariable.fromTerm_var(context, x), QVariable.fromQVarList(context, vs),
        RichTerm.decodeFromExpression(context,e))
    case _ => throw new RuntimeException(s"term $t cannot be decoded as a statement")
  }

  implicit object codec extends Codec[Statement] {
    override val mlType: String = "Programs.statement"

    def encode_call(c : Call): XML.Tree = c match {
      case Call(name,args@_*) => XML.Elem(("call",List(("name",name))), args.map(encode_call).toList)
    }

    private def enc_term(t: RichTerm) = RichTerm.term_tight_codec.encode(t.isabelleTerm)

    override def encode(t: Statement): XML.Tree = t match {
      case Block(stmts@_*) => XML.Elem(("block", Nil), stmts.map(encode).toList)
      case Assign(v, rhs) => XML.Elem(("assign", List(("lhs", v.name))), List(enc_term(rhs)))
      case Sample(v, rhs) => XML.Elem(("sample", List(("lhs", v.name))), List(enc_term(rhs)))
      case call: Call => encode_call(call)
      case Measurement(v, loc, exp) => XML.Elem(("measurement", List(("lhs", v.name))),
        enc_term(exp) :: loc.map { l => Codec.string.encode(l.name) })
      case QInit(loc, exp) => XML.Elem(("qinit", Nil),
        enc_term(exp) :: loc.map { l => Codec.string.encode(l.name) })
      case QApply(loc, exp) => XML.Elem(("qapply", Nil),
        enc_term(exp) :: loc.map { l => Codec.string.encode(l.name) })
      case IfThenElse(e, p1, p2) => XML.Elem(("ifte", Nil),
        List(enc_term(e), encode(p1), encode(p2)))
      case While(e, p1) => XML.Elem(("while", Nil),
        List(enc_term(e), encode(p1)))
    }

    override def decode(tree: XML.Tree): XMLResult[Statement] = ???
  }

  // TODO: implement on Isabelle side or remove
  val statement_to_term_op: Operation[(BigInt, Statement), RichTerm] =
    Operation.implicitly[(BigInt, Statement), RichTerm]("statement_to_term")

  val statements_to_term_op: Operation[(BigInt, List[Statement]), RichTerm] =
    Operation.implicitly[(BigInt, List[Statement]), RichTerm]("statements_to_term")
}

class Block(val statements:List[Statement]) extends Statement {
  @deprecated("too slow", "now")
  def programListTermOld(context: Isabelle.Context): Term = Isabelle.mk_list(Isabelle.programT, statements.map(_.programTermOLD(context)))

  def programListTerm(context: Isabelle.Context): RichTerm =
    context.isabelle.invoke(Statement.statements_to_term_op, (context.contextId, this.statements))


  override def programTermOLD(context: Isabelle.Context) : Term = Isabelle.block $ programListTermOld(context)

  override def toBlock: Block = this

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
    environment.programs(name) match {
      case decl : ConcreteProgramDecl =>
        inline(name: String, decl.program)
      case _ : AbstractProgramDecl =>
        throw UserException(s"Cannot inline '$name'. It is an abstract program (declared with 'adversary').")
    }
//    inline(name: String, environment.programs(name).asInstanceOf[ConcreteProgramDecl].program)
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


final case class Assign(variable:CVariable, expression:RichTerm) extends Statement {
  override def toString: String = s"""${variable.name} <- $expression;"""
  override def inline(name: String, statement: Statement): Statement = this

  override def checkWelltyped(context: Isabelle.Context): Unit =
    expression.checkWelltyped(context, variable.valueTyp)

  override def programTermOLD(context: Isabelle.Context): Term =
    Isabelle.assign(variable.valueTyp) $ variable.variableTerm $ expression.encodeAsExpression(context).isabelleTerm
}
final case class Sample(variable:CVariable, expression:RichTerm) extends Statement {
  override def toString: String = s"""${variable.name} <$$ $expression;"""
  override def inline(name: String, statement: Statement): Statement = this

  override def checkWelltyped(context: Isabelle.Context): Unit =
    expression.checkWelltyped(context, Isabelle.distrT(variable.valueTyp))

  override def programTermOLD(context: Isabelle.Context): Term =
    Isabelle.sample(variable.valueTyp) $ variable.variableTerm $ expression.encodeAsExpression(context).isabelleTerm
}
final case class IfThenElse(condition:RichTerm, thenBranch: Block, elseBranch: Block) extends Statement {
  override def inline(name: String, program: Statement): Statement =
    IfThenElse(condition,thenBranch.inline(name,program),elseBranch.inline(name,program))
  override def toString: String = s"if ($condition) $thenBranch else $elseBranch;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    condition.checkWelltyped(context, HOLogic.boolT)
    thenBranch.checkWelltyped(context)
    elseBranch.checkWelltyped(context)
  }
  override def programTermOLD(context: Isabelle.Context): Term =
    Isabelle.ifthenelse $ condition.encodeAsExpression(context).isabelleTerm $ thenBranch.programListTermOld(context) $ elseBranch.programListTermOld(context)
}

final case class While(condition:RichTerm, body: Block) extends Statement {
  override def inline(name: String, program: Statement): Statement =
    While(condition,body.inline(name,program))
  override def toString: String = s"while ($condition) $body"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    condition.checkWelltyped(context, HOLogic.boolT)
    body.checkWelltyped(context)
  }
  override def programTermOLD(context: Isabelle.Context): Term =
    Isabelle.whileProg $ condition.encodeAsExpression(context).isabelleTerm $ body.programListTermOld(context)
}

final case class QInit(location:List[QVariable], expression:RichTerm) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"${location.map(_.name).mkString(",")} <q $expression;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    val expected = Isabelle.vectorT(Isabelle.tupleT(location.map(_.valueTyp):_*))
    expression.checkWelltyped(context, expected)
  }
  override def programTermOLD(context: Isabelle.Context): Term =
    Isabelle.qinit(Isabelle.tupleT(location.map(_.valueTyp):_*)) $ Isabelle.qvarTuple_var(location) $ expression.encodeAsExpression(context).isabelleTerm
}
final case class QApply(location:List[QVariable], expression:RichTerm) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"on ${location.map(_.name).mkString(",")} apply $expression;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    val varType = Isabelle.tupleT(location.map(_.valueTyp):_*)
    val expected = pure.Type("Bounded_Operators.bounded",List(varType,varType))
    expression.checkWelltyped(context, expected)
  }
  override def programTermOLD(context: Isabelle.Context): Term =
    Isabelle.qapply(Isabelle.tupleT(location.map(_.valueTyp):_*)) $ Isabelle.qvarTuple_var(location) $ expression.encodeAsExpression(context).isabelleTerm
}
final case class Measurement(result:CVariable, location:List[QVariable], e:RichTerm) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"${result.name} <- measure ${location.map(_.name).mkString(",")} in $e;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    val expected = pure.Type("QRHL_Core.measurement",List(result.variableTyp, Isabelle.tupleT(location.map(_.valueTyp):_*)))
    e.checkWelltyped(context, expected)
  }
  override def programTermOLD(context: Isabelle.Context): Term =
    Isabelle.measurement(Isabelle.tupleT(location.map(_.valueTyp):_*), result.valueTyp) $
      result.variableTerm $ Isabelle.qvarTuple_var(location) $ e.encodeAsExpression(context).isabelleTerm
}
final case class Call(name:String, args:Call*) extends Statement {
  override def toString: String = "call "+toStringShort+";"
  def toStringShort: String =
    if (args.isEmpty) name else s"$name(${args.map(_.toStringShort).mkString(",")})"
  override def inline(name: String, program: Statement): Statement = this

  override def checkWelltyped(context: Isabelle.Context): Unit = {}
  override def programTermOLD(context: Isabelle.Context): Term = {
    if (args.nonEmpty) {
      val argTerms = args.map(_.programTermOLD(context)).toList
      val argList = Isabelle.mk_list(Isabelle.programT, argTerms)
      Isabelle.instantiateOracles $ Free(name, Isabelle.oracle_programT) $ argList
    } else
      Free(name, Isabelle.programT)
  }
}
