package qrhl.logic

import info.hupel.isabelle.api.XML
import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.{Codec, Operation, XMLResult, pure}
import info.hupel.isabelle.pure.{App, Const, Free, Term, Typ}
import qrhl.UserException
import qrhl.isabelle.{Isabelle, RichTerm}

import scala.annotation.tailrec
import scala.collection.{AbstractIterator, mutable}

// Implicits
import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec
import Statement.codec


sealed trait VarTerm[+A] extends Iterable[A] {
//  override def apply(idx: Int): A = ???
  def map[B](f:A=>B) : VarTerm[B]
  /** Not thread safe */
  override def iterator: Iterator[A] = new AbstractIterator[A] {
    private var stack : List[VarTerm[A]] = List(VarTerm.this)
    /** Has the additional side effect of making sure that [stack.head] is a VTSingle if it exists */
    @tailrec override def hasNext: Boolean = stack match {
      case Nil => false
      case (_:VTUnit.type)::_ => // pattern VTUnit::_ leads to an implicit equality check, which calls the iterator!?
        stack = stack.tail
        hasNext
      case VTCons(a,b)::_ =>
        stack = a::b::stack.tail
        hasNext
      case VTSingle(_)::_ => true
    }

    override def next(): A =
      if (hasNext) { val result = stack.head.asInstanceOf[VTSingle[A]].v; stack = stack.tail; result }
      else throw new RuntimeException("Iterator.next called on empty iterator")
  }
}
object VarTerm {
  def varlist[A](elems: A*) : VarTerm[A] = {
    var result : VarTerm[A] = VTUnit
    for (e <- elems.reverseIterator) {
      result = result match {
        case VTUnit => VTSingle(e)
        case _ => VTCons(VTSingle(e),result)
      }
    }
    result
  }

  object codecString extends Codec[VarTerm[String]] {
    override lazy val mlType: String = "string tree"
    override def encode(t: VarTerm[String]): XML.Tree = t match {
      case VTUnit => XML.Elem(("u",Nil),Nil)
      case VTCons(a,b) => XML.Elem(("c",Nil),List(encode(a),encode(b)))
      case VTSingle(v) => XML.Elem(("s",Nil),List(XML.Text(v)))
    }

    override def decode(xml: XML.Tree): XMLResult[VarTerm[String]] = xml match {
      case XML.Elem(("c",Nil),List(aXml,bXml)) =>
        for (a <- decode(aXml);
             b <- decode(bXml))
          yield VTCons(a,b)
      case XML.Elem(("s",Nil),List(XML.Text(s))) => Right(VTSingle(s))
      case XML.Elem(("u",Nil),Nil) => Right(VTUnit)
      case _ => Left(("No a valid varterm",List(xml)))
    }
  }
}

case object VTUnit extends VarTerm[Nothing] {
  override def map[B](f: Nothing => B): VTUnit.type = VTUnit
//  override def length: Int = 0
  override def iterator: Iterator[Nothing] = Iterator.empty
}
case class VTSingle[+A](v:A) extends VarTerm[A] {
  override def map[B](f: A => B): VarTerm[B] = VTSingle(f(v))
//  override def length: Int = 1
  override def iterator: Iterator[A] = Iterator.single(v)
}
case class VTCons[+A](a:VarTerm[A], b:VarTerm[A]) extends VarTerm[A] {
  override def map[B](f: A => B): VarTerm[B] = VTCons(a.map(f),b.map(f))
//  override def length: Int = a.length + b.length
}

// Programs
sealed trait Statement {
  def toBlock: Block = Block(this)
Nil
//  @deprecated("too slow, use programTerm instead","now")
//  def programTermOLD(context: Isabelle.Context) : Term

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
      case Assign(v,e) => cvars ++= v; collectExpr(e)
      case Sample(v,e) => cvars ++= v; collectExpr(e)
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
      case Measurement(v,vs,e) => cvars ++= v; collectExpr(e); qvars ++= vs
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
      case Assign(v,e) => vars ++= v.map[String](_.name); vars ++= e.variables
      case Sample(v,e) => vars ++= v.map[String](_.name); vars ++= e.variables
      case Call(_, _*) =>
      case While(e,body) => vars ++= e.variables; collect(body)
      case IfThenElse(e,p1,p2) => vars ++= e.variables; collect(p1); collect(p2)
      case QInit(vs,e) => vars ++= vs.map[String](_.name); vars ++= e.variables
      case Measurement(v,vs,e) => vars ++= v.map[String](_.name); vars ++= vs.map[String](_.name); vars ++= e.variables
      case QApply(vs,e) => vars ++= vs.map[String](_.name); vars ++= e.variables
    }
    collect(this)
    vars.result
  }

  /** Including nested programs (via Call). (Missing ambient variables from nested calls.) */
  def variablesAll(env:Environment) : Set[String] = {
    val vars = new mutable.SetBuilder[String,Set[String]](Set.empty)
    def collect(s:Statement) : Unit = s match {
      case Block(ss @ _*) => ss.foreach(collect)
      case Assign(v,e) => vars ++= v.map[String](_.name); vars ++= e.variables
      case Sample(v,e) => vars ++= v.map[String](_.name); vars ++= e.variables
      case Call(name, args @ _*) =>
        val (cvars,qvars,_,_) = env.programs(name).variablesRecursive
        vars ++= cvars.map(_.name)
        vars ++= qvars.map(_.name)
        args.foreach(collect)
      case While(e,body) => vars ++= e.variables; collect(body)
      case IfThenElse(e,p1,p2) => vars ++= e.variables; collect(p1); collect(p2)
      case QInit(vs,e) => vars ++= vs.map[String](_.name); vars ++= e.variables
      case Measurement(v,vs,e) => vars ++= v.map[String](_.name); vars ++= vs.map[String](_.name); vars ++= e.variables
      case QApply(vs,e) => vars ++= vs.map[String](_.name); vars ++= e.variables
    }
    collect(this)
    vars.result
  }

  def inline(name: String, program: Statement): Statement
}

object Statement {
/*
  def decodeFromListTerm(context: Isabelle.Context, t:Term) : Block = {
    val statements = Isabelle.dest_list(t).map(decodeFromTerm(context,_))
    Block(statements:_*)
  }
*/

/*  def decodeFromTerm(context: Isabelle.Context, t:Term) : Statement = t match {
    case App(Const(Isabelle.block.name,_), statements) => decodeFromListTerm(context, statements)
    case App(App(Const(Isabelle.assignName,_),x),e) =>
      Assign(CVariable.fromCVarList(context, x), RichTerm.decodeFromExpression(context, e))
    case App(App(Const(Isabelle.sampleName,_),x),e) =>
      Sample(CVariable.fromCVarList(context, x),RichTerm.decodeFromExpression(context, e))
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
      Measurement(CVariable.fromCVarList(context, x), QVariable.fromQVarList(context, vs),
        RichTerm.decodeFromExpression(context,e))
    case _ => throw new RuntimeException(s"term $t cannot be decoded as a statement")
  }*/

  implicit object codec extends Codec[Statement] {
    override val mlType: String = "Programs.statement"

    def encode_call(c : Call): XML.Tree = c match {
      case Call(name,args@_*) => XML.Elem(("call",List(("name",name))), args.map(encode_call).toList)
    }


    import scalaz._
    import std.list._
    import syntax.traverse._
    import Isabelle.applicativeXMLResult

    def decode_call(xml : XML.Tree): XMLResult[Call] = xml match {
      case XML.Elem(("call",List(("name",name))), argsXml) =>
        for (args <- argsXml.traverse(decode_call))
          yield Call(name, args : _*)
    }

//    def string_list_encode(l:List[String]) = XML.Elem(("l",Nil), l.map( s => Codec.string.encode(s)))
//    def string_list_decode(xml:XML.Tree): XMLResult[List[String]] = xml match {
//      case XML.Elem(("l",Nil), l) => l.traverse(Codec.string.decode)
//    }

    override def encode(t: Statement): XML.Tree = t match {
      case Block(stmts@_*) => XML.Elem(("block", Nil), stmts.map(encode).toList)
      case Assign(v, rhs) => XML.Elem(("assign", Nil), List(VarTerm.codecString.encode(v.map[String](_.name)), RichTerm.codec.encode(rhs)))
      case Sample(v, rhs) => XML.Elem(("sample", Nil), List(VarTerm.codecString.encode(v.map[String](_.name)), RichTerm.codec.encode(rhs)))
      case call: Call => encode_call(call)
      case Measurement(v, loc, exp) => XML.Elem(("measurement", Nil),
        List(VarTerm.codecString.encode(v.map[String](_.name)), VarTerm.codecString.encode(loc.map[String](_.name)), RichTerm.codec.encode(exp)))
      case QInit(loc, exp) => XML.Elem(("qinit", Nil),
        List(VarTerm.codecString.encode(loc.map[String](_.name)), RichTerm.codec.encode(exp)))
      case QApply(loc, exp) => XML.Elem(("qapply", Nil),
        List(VarTerm.codecString.encode(loc.map[String](_.name)), RichTerm.codec.encode(exp)))
      case IfThenElse(e, p1, p2) => XML.Elem(("ifte", Nil),
        List(RichTerm.codec.encode(e), encode(p1), encode(p2)))
      case While(e, p1) => XML.Elem(("while", Nil),
        List(RichTerm.codec.encode(e), encode(p1)))
    }

//    def mk_cvar_list(names : List[String], typ : Typ) : List[CVariable] = names match {
//      case Nil =>
//        assert(typ == Isabelle.unitT)
//        Nil
//      case List(x) =>
//        List(CVariable(x,typ))
//      case x::xs =>
//        val (xT,xsT) = Isabelle.dest_prodT(typ)
//        CVariable(x,xT) :: mk_cvar_list(xs, xsT)
//    }

    def mk_cvar_term(names : VarTerm[String], typ : Typ) : VarTerm[CVariable] = names match {
      case VTUnit =>
        assert(typ == Isabelle.unitT)
        VTUnit
      case VTSingle(x) =>
        VTSingle(CVariable(x,typ))
      case VTCons(a,b) =>
        val (aT,bT) = Isabelle.dest_prodT(typ)
        VTCons(mk_cvar_term(a,aT), mk_cvar_term(b,bT))
    }

//    def mk_qvar_list(names : List[String], typ : Typ) : List[QVariable] = names match {
//      case Nil =>
//        assert(typ == Isabelle.unitT)
//        Nil
//      case List(x) =>
//        List(QVariable(x,typ))
//      case x::xs =>
//        val (xT,xsT) = Isabelle.dest_prodT(typ)
//        QVariable(x,xT) :: mk_qvar_list(xs, xsT)
//    }

    def mk_qvar_term(names : VarTerm[String], typ : Typ) : VarTerm[QVariable] = names match {
      case VTUnit =>
        assert(typ == Isabelle.unitT)
        VTUnit
      case VTSingle(x) =>
        VTSingle(QVariable(x,typ))
      case VTCons(a,b) =>
        val (aT,bT) = Isabelle.dest_prodT(typ)
        VTCons(mk_qvar_term(a,aT), mk_qvar_term(b,bT))
    }


    override def decode(xml: XML.Tree): XMLResult[Statement] = xml match {
      case XML.Elem(("block", Nil), stmtsXml) =>
        for (stmts <- stmtsXml.traverse(decode))
          yield Block(stmts : _*)
      case XML.Elem(("assign", Nil), List(lhsXml,rhsXml)) =>
        for (lhs <- VarTerm.codecString.decode(lhsXml);
             rhs <- RichTerm.codec.decode(rhsXml))
          yield Assign(mk_cvar_term(lhs, rhs.typ), rhs)
      case XML.Elem(("sample", Nil), List(lhsXml,rhsXml)) =>
        for (lhs <- VarTerm.codecString.decode(lhsXml);
             rhs <- RichTerm.codec.decode(rhsXml))
          yield Sample(mk_cvar_term(lhs, Isabelle.dest_distrT(rhs.typ)), rhs)
      case call @ XML.Elem(("call",_),_) => decode_call(call)
      case XML.Elem(("measurement", Nil), List(lhsXml,locXml,expXml)) =>
        for (lhs <- VarTerm.codecString.decode(lhsXml);
             loc <- VarTerm.codecString.decode(locXml);
             exp <- RichTerm.codec.decode(expXml);
             (vT,locT) = Isabelle.dest_measurementT(exp.typ))
          yield Measurement(mk_cvar_term(lhs,vT), mk_qvar_term(loc,locT), exp)
      case XML.Elem(("qinit", Nil), List(locXML,expXML)) =>
        for (loc <- VarTerm.codecString.decode(locXML);
             exp <- RichTerm.codec.decode(expXML))
          yield QInit(mk_qvar_term(loc, Isabelle.dest_vectorT(exp.typ)), exp)
      case XML.Elem(("qapply", Nil), List(locXML,expXML)) =>
        for (loc <- VarTerm.codecString.decode(locXML);
             exp <- RichTerm.codec.decode(expXML))
          yield QApply(mk_qvar_term(loc, Isabelle.dest_boundedT(exp.typ)._1), exp)
      case XML.Elem(("ifte", Nil), List(eXml,p1Xml,p2Xml)) =>
        for (e <- RichTerm.codec.decode(eXml);
             p1 <- decode(p1Xml);
             p2 <- decode(p2Xml))
          yield IfThenElse(e, p1.asInstanceOf[Block], p2.asInstanceOf[Block])
      case XML.Elem(("while", Nil), List(eXml,p1Xml)) =>
        for (e <- RichTerm.codec.decode(eXml);
             p1 <- decode(p1Xml))
          yield While(e, p1.asInstanceOf[Block])
    }
  }

  val statement_to_term_op: Operation[(BigInt, Statement), RichTerm] =
    Operation.implicitly[(BigInt, Statement), RichTerm]("statement_to_term")

  val statements_to_term_op: Operation[(BigInt, List[Statement]), RichTerm] =
    Operation.implicitly[(BigInt, List[Statement]), RichTerm]("statements_to_term")
}

class Block(val statements:List[Statement]) extends Statement {
//  @deprecated("too slow", "now")
//  def programListTermOld(context: Isabelle.Context): Term = Isabelle.mk_list(Isabelle.programT, statements.map(_.programTermOLD(context)))

  def programListTerm(context: Isabelle.Context): RichTerm =
    context.isabelle.invoke(Statement.statements_to_term_op, (context.contextId, this.statements))


//  override def programTermOLD(context: Isabelle.Context) : Term = Isabelle.block $ programListTermOld(context)

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


final case class Assign(variable:VarTerm[CVariable], expression:RichTerm) extends Statement {
  override def toString: String = s"""${Variable.vartermToString(variable)} <- $expression;"""
  override def inline(name: String, statement: Statement): Statement = this

  override def checkWelltyped(context: Isabelle.Context): Unit =
    expression.checkWelltyped(context, Isabelle.tupleT(variable.map[Typ](_.valueTyp)))

//  override def programTermOLD(context: Isabelle.Context): Term =
//    Isabelle.assign(variable.valueTyp) $ variable.variableTerm $ expression.encodeAsExpression(context).isabelleTerm
}
final case class Sample(variable:VarTerm[CVariable], expression:RichTerm) extends Statement {
  override def toString: String = s"""${Variable.vartermToString(variable)} <$$ $expression;"""
  override def inline(name: String, statement: Statement): Statement = this

  override def checkWelltyped(context: Isabelle.Context): Unit =
    expression.checkWelltyped(context, Isabelle.distrT(Isabelle.tupleT(variable.map[Typ](_.valueTyp))))

//  override def programTermOLD(context: Isabelle.Context): Term =
//    Isabelle.sample(variable.valueTyp) $ variable.variableTerm $ expression.encodeAsExpression(context).isabelleTerm
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
//  override def programTermOLD(context: Isabelle.Context): Term =
//    Isabelle.ifthenelse $ condition.encodeAsExpression(context).isabelleTerm $ thenBranch.programListTermOld(context) $ elseBranch.programListTermOld(context)
}

final case class While(condition:RichTerm, body: Block) extends Statement {
  override def inline(name: String, program: Statement): Statement =
    While(condition,body.inline(name,program))
  override def toString: String = s"while ($condition) $body"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    condition.checkWelltyped(context, HOLogic.boolT)
    body.checkWelltyped(context)
  }
//  override def programTermOLD(context: Isabelle.Context): Term =
//    Isabelle.whileProg $ condition.encodeAsExpression(context).isabelleTerm $ body.programListTermOld(context)
}

final case class QInit(location:VarTerm[QVariable], expression:RichTerm) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"${Variable.vartermToString(location)} <q $expression;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    val expected = Isabelle.vectorT(Isabelle.tupleT(location.map[Typ](_.valueTyp)))
    expression.checkWelltyped(context, expected)
  }
//  override def programTermOLD(context: Isabelle.Context): Term =
//    Isabelle.qinit(Isabelle.tupleT(location.map(_.valueTyp):_*)) $ Isabelle.qvarTuple_var(location) $ expression.encodeAsExpression(context).isabelleTerm
}
final case class QApply(location:VarTerm[QVariable], expression:RichTerm) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"on ${Variable.vartermToString(location)} apply $expression;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    val varType = Isabelle.tupleT(location.map[Typ](_.valueTyp))
    val expected = pure.Type("Bounded_Operators.bounded",List(varType,varType))
    expression.checkWelltyped(context, expected)
  }
//  override def programTermOLD(context: Isabelle.Context): Term =
//    Isabelle.qapply(Isabelle.tupleT(location.map(_.valueTyp):_*)) $ Isabelle.qvarTuple_var(location) $ expression.encodeAsExpression(context).isabelleTerm
}
final case class Measurement(result:VarTerm[CVariable], location:VarTerm[QVariable], e:RichTerm) extends Statement {
  override def inline(name: String, program: Statement): Statement = this
  override def toString: String = s"${Variable.vartermToString(result)} <- measure ${Variable.vartermToString(location)} in $e;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    val expected = pure.Type("QRHL_Core.measurement",List(
      Isabelle.tupleT(result.map[Typ](_.valueTyp)),
      Isabelle.tupleT(location.map[Typ](_.valueTyp))))
    e.checkWelltyped(context, expected)
  }
//  override def programTermOLD(context: Isabelle.Context): Term =
//    Isabelle.measurement(Isabelle.tupleT(location.map(_.valueTyp):_*), result.valueTyp) $
//      result.variableTerm $ Isabelle.qvarTuple_var(location) $ e.encodeAsExpression(context).isabelleTerm
}
final case class Call(name:String, args:Call*) extends Statement {
  override def toString: String = "call "+toStringShort+";"
  def toStringShort: String =
    if (args.isEmpty) name else s"$name(${args.map(_.toStringShort).mkString(",")})"
  override def inline(name: String, program: Statement): Statement = this

  override def checkWelltyped(context: Isabelle.Context): Unit = {}
//  override def programTermOLD(context: Isabelle.Context): Term = {
//    if (args.nonEmpty) {
//      val argTerms = args.map(_.programTermOLD(context)).toList
//      val argList = Isabelle.mk_list(Isabelle.programT, argTerms)
//      Isabelle.instantiateOracles $ Free(name, Isabelle.oracle_programT) $ argList
//    } else
//      Free(name, Isabelle.programT)
//  }
}
