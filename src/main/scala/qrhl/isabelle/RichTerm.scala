package qrhl.isabelle

import info.hupel.isabelle.api.XML
import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.hol.HOLogic.boolT
import info.hupel.isabelle.pure.{Abs, App, Bound, Const, Free, TFree, TVar, Term, Type, Var, Typ => ITyp}
import info.hupel.isabelle.{Codec, DecodingException, Operation, XMLResult, pure}
import org.log4s
import org.log4s.Logger
import qrhl.logic.{CVariable, Environment, Variable}

import scala.collection.mutable
import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec
import Isabelle.applicativeXMLResult

import scala.collection.mutable.ListBuffer

final class RichTerm private(val id: Option[BigInt]=None, val typ: pure.Typ, _isabelleTerm:Option[Term]=None, _pretty:Option[String]=None) {
  class debug_codec[A](codec : Codec[A]) extends Codec[A] { // TODO remove
    override val mlType: String = codec.mlType

    override def encode(t: A): XML.Tree = codec.encode(t)

    override def decode(tree: XML.Tree): XMLResult[A] = {
      RichTerm.logger.debug(tree.toString)
      codec.decode(tree)
    }
  }

  lazy val isabelleTerm : Term = _isabelleTerm match {
    case Some(te) => te
    case None =>
      val retrieve_term_op = Operation.implicitly[BigInt, Term]("retrieve_term")(implicitly, term_tight_codec) // TODO move
//      try {
      Isabelle.theContext.isabelle.invoke(retrieve_term_op, id.get)
//      } catch {
//        case e @ DecodingException(msg,body) => print(body); throw e
//      }
  }

  def encodeAsExpression(context: Isabelle.Context) : RichTerm =
    context.isabelle.invoke(RichTerm.termToExpressionOp, (context.contextId, isabelleTerm))

  def stripAssumption(number: Int): RichTerm = RichTerm(typ,RichTerm.stripAssumption(isabelleTerm,number))

  override def equals(o: scala.Any): Boolean = o match {
    case o : RichTerm => typ == o.typ && isabelleTerm == o.isabelleTerm
    case _ => false
  }

  def checkWelltyped(context:Isabelle.Context, ityp:ITyp): Unit = {
    assert(ityp==this.typ,s"$ityp != ${this.typ}")
    assert(context.checkType(isabelleTerm) == typ)
  }

  /** Free variables */
  private def freeVars(term: Term): Set[String] = {
    val fv = new mutable.SetBuilder[String,Set[String]](Set.empty)
    def collect(t:Term) : Unit = t match {
      case Free(v,_) => fv += v
//      case App(App(App(Const(Isabelle.probability_old.name,_),t1),t2),t3) =>
//        fv += Isabelle.dest_string(t1)
//        collect(t2); collect(t3)
      case Const(_,_) | Bound(_) | Var(_,_) =>
      case App(t1,t2) => collect(t1); collect(t2)
      case Abs(_,_,body) => collect(body)
    }
    collect(term)
    fv.result
  }

  def variables : Set[String] = freeVars(isabelleTerm)

  /** Finds all classical and ambient variables in an expression. The expression is assumed not to have indexed variables. */
  def caVariables(environment: Environment, cvars : mutable.Set[CVariable], avars : mutable.Set[String]): Unit = {
//    val cvars = mutable.LinkedHashSet[CVariable]()
//    val avars = mutable.LinkedHashSet[String]()
    for (v<-variables) environment.cVariables.get(v) match {
      case Some(cv) => cvars += cv
      case None => avars += v
    }
  }

  override lazy val toString: String = _pretty match {
    case Some(s) => s
    case _ => id match {
      case Some(id2) =>
        val retrieve_term_string_op = Operation.implicitly[BigInt,String]("retrieve_term_string") // TODO move
        Isabelle.symbolsToUnicode(Isabelle.theContext.isabelle.invoke(retrieve_term_string_op, id.get))
      case None => Isabelle.theContext.prettyExpression (isabelleTerm)
    }
  }

//  val isabelleTerm : Term = isabelleTerm
  def simplify(isabelle: Option[Isabelle.Context], facts:List[String]): (RichTerm,Isabelle.Thm) = simplify(isabelle.get,facts)

  def simplify(context: Isabelle.Context, facts:List[String], thms:ListBuffer[Isabelle.Thm]) : RichTerm = {
    val (t,thm) = context.simplify(isabelleTerm, facts)
    thms += thm
    t
  }

  def simplify(context: Isabelle.Context, facts:List[String]): (RichTerm,Isabelle.Thm) =
    context.simplify(isabelleTerm, facts)

  def map(f : Term => Term) : RichTerm = RichTerm(typ, f(isabelleTerm))

  def substitute(v:CVariable, repl:RichTerm) : RichTerm = {
    assert(repl.typ==v.valueTyp)
    map(RichTerm.substitute(v.name, repl.isabelleTerm, _))
  }

  def index1(environment: Environment): RichTerm = index(environment, left=true)
  def index2(environment: Environment): RichTerm = index(environment, left=false)
  def index(environment: Environment, left: Boolean): RichTerm = {
    def idx(t:Term) : Term = t match {
      case App(t1,t2) => App(idx(t1),idx(t2))
      case Free(name,typ2) =>
        if (environment.ambientVariables.contains(name)) t
        else Free(Variable.index(left=left,name), typ2)
      case Const(_,_) | Bound(_) | Var(_,_) => t
      case Abs(name,typ2,body) => Abs(name,typ2,idx(body))
    }
    new RichTerm(typ = typ, _isabelleTerm = Some(idx(isabelleTerm)))
  }


  def leq(e: RichTerm): RichTerm = {
      val t = e.isabelleTerm
      val predicateT = Isabelle.predicateT // Should be the type of t
      val newT =  Const ("Orderings.ord_class.less_eq", ITyp.funT(predicateT, ITyp.funT(predicateT, boolT))) $ isabelleTerm $ t
      RichTerm(Isabelle.boolT,newT)
  }

  def implies(e: RichTerm): RichTerm = {
    val t = e.isabelleTerm
    val newT = HOLogic.imp $ isabelleTerm $ t
//    val typ = Typ.bool(null)
    RichTerm(Isabelle.boolT,newT)
  }

  def not: RichTerm = {
    assert(typ==HOLogic.boolT)
    RichTerm(typ,Const("HOL.Not",HOLogic.boolT -->: HOLogic.boolT) $ isabelleTerm)
  }

}


object RichTerm {
  private val logger: Logger = log4s.getLogger

  implicit object typ_tight_codec extends Codec[ITyp] {
    override val mlType: String = "term"

    def decode_class(tree: XML.Tree): XMLResult[String] = tree match {
      case XML.Elem((c,Nil),Nil) => Right(c)
      case xml => Left(("invalid encoding of class",List(xml)))
    }
    def encode_class(c : String): XML.Tree = XML.Elem((c,Nil),Nil)

    override def encode(t: ITyp): XML.Tree = t match {
      case Type(name, typs) => XML.Elem(("t", Nil), XML.Text(name) :: typs.map(encode))
      case TFree(name, sort) => XML.Elem(("f", Nil), XML.Text(name) :: sort.map(encode_class))
      case TVar((name, idx), sort) => XML.Elem(("v", List((name, idx.toString))), sort.map(encode_class))
    }

    import scalaz._
    import std.list._
    import syntax.traverse._

    override def decode(tree: XML.Tree): XMLResult[ITyp] = tree match {
      case XML.Elem(("t",Nil), XML.Text(name) :: xmls) =>
        for (ts <- xmls.map(decode).sequence) yield Type(name,ts)
      case XML.Elem (("f",Nil), XML.Text(name) :: xmls) =>
        for (sort <- xmls.map(decode_class).sequence) yield TFree(name,sort)
      case xml @ XML.Elem(("v",List((name,idx))), xmls) =>
//        try {
        val i = Integer.parseInt(idx)
        for (sort <- xmls.map(decode_class).sequence) yield TVar((name,i),sort)
//        } catch {
//          case e : NumberFormatException =>
//            Right(())
//        }
      case xml =>
        logger.debug(xml.toString)
        Left(("invalid encoding for a type",List(xml)))
    }
  }

  implicit object term_tight_codec extends Codec[Term] {
    override val mlType: String = "term"

    override def encode(t: Term): XML.Tree = t match {
      case Const(name, typ) => XML.Elem(("c", Nil), List(XML.Text(name), typ_tight_codec.encode(typ)))
      case App(t1, t2) => XML.Elem(("a", Nil), List(encode(t1), encode(t2)))
      case Free(name, typ) => XML.Elem(("f", Nil), List(XML.Text(name), typ_tight_codec.encode(typ)))
      case Var((name, idx), typ) => XML.Elem(("v", List((name, idx.toString))), List(typ_tight_codec.encode(typ)))
      case Abs(name, typ, body) => XML.Elem(("A", Nil), List(XML.Text(name), typ_tight_codec.encode(typ), encode(body)))
      case Bound(i) => XML.Elem(("b", Nil), List(XML.Text(i.toString)))
    }


    override def decode(tree: XML.Tree): XMLResult[Term] = tree match {
      case XML.Elem(("c",Nil),List(XML.Text(name),typXml)) =>
        for (typ <- typ_tight_codec.decode(typXml)) yield Const(name,typ)

      case XML.Elem(("a",Nil),List(xml1, xml2)) =>
        for (t1 <- decode(xml1);
             t2 <- decode(xml2))
          yield t1 $ t2

      case XML.Elem(("f",Nil), List(XML.Text(name), xml)) =>
        for (typ <- typ_tight_codec.decode(xml))
          yield Free(name,typ)

      case XML.Elem(("v",List((name,idx))), List(xml1)) =>
        val i = Integer.parseInt(idx)
        for (typ <- typ_tight_codec.decode(xml1))
          yield Var((name,i),typ)

      case XML.Elem(("A",Nil), List(XML.Text(name), xmlTyp, xmlBody)) =>
        for (typ <- typ_tight_codec.decode(xmlTyp);
             body <- decode(xmlBody))
          yield Abs(name,typ,body)

      case XML.Elem(("A",Nil), List(xmlTyp, xmlBody)) =>
        for (typ <- typ_tight_codec.decode(xmlTyp);
             body <- decode(xmlBody))
          yield Abs("",typ,body)

      case XML.Elem (("b",Nil), List(XML.Text(idx))) =>
        val i = Integer.parseInt(idx)
        Right(Bound(i))

      case xml =>
        logger.debug(xml.toString)
        Left(("invalid encoding for a term",List(xml)))
    }
  }

  implicit object codec extends Codec[RichTerm] {
    override val mlType: String = "term"
    override def encode(e: RichTerm): XML.Tree = e.id match {
      case None => XML.Elem(("richterm",Nil), List(term_tight_codec.encode(e.isabelleTerm)))
      case Some(id2) => XML.Elem(("richterm",List(("id",id2.toString))),Nil)
    }

    override def decode(tree: XML.Tree): XMLResult[RichTerm] = tree match {
      case XML.Elem(("richterm",List(("id",id))),List(typXml)) =>
        for (typ <- typ_tight_codec.decode(typXml))
          yield RichTerm(id=BigInt(id), typ = typ)
    }
  }

  def decodeFromExpression(context:Isabelle.Context, t: Term): RichTerm = {
    context.isabelle.invoke(decodeFromExpressionOp, (context.contextId, t))
//    Expression(typ, term)
  }

  val decodeFromExpressionOp: Operation[(BigInt,Term), RichTerm] =
    Operation.implicitly[(BigInt,Term), RichTerm]("expression_to_term")

  val termToExpressionOp: Operation[(BigInt, Term), RichTerm] =
    Operation.implicitly[(BigInt, Term), RichTerm]("term_to_expression")

  def trueExp(isabelle: Isabelle.Context): RichTerm = RichTerm(Isabelle.boolT, HOLogic.True)

  private val readExpressionOp : Operation[(BigInt, String, ITyp), RichTerm] = Operation.implicitly[(BigInt, String, ITyp), RichTerm]("read_expression")
  def apply(context: Isabelle.Context, str:String, typ:pure.Typ) : RichTerm = {
    context.isabelle.invoke(readExpressionOp,(context.contextId,Isabelle.unicodeToSymbols(str),typ))
//    val term = context.readTerm(Isabelle.unicodeToSymbols(str),typ)
//    Expression(typ, term)
  }

  def apply(typ: pure.Typ, term:Term) : RichTerm =
    new RichTerm(typ=typ, _isabelleTerm = Some(term))

  private val cache = new mutable.WeakHashMap[BigInt,RichTerm]()
  def apply(id : BigInt, typ : ITyp) : RichTerm =
    cache.getOrElseUpdate(id, new RichTerm(id = Some(id), typ = typ))

  def unapply(e: RichTerm): Option[Term] = Some(e.isabelleTerm)

  def substitute(v: String, repl: Term, term: Term): Term = {
      def subst(t:Term) : Term = t match {
        case App(t1,t2) => App(subst(t1),subst(t2))
        case Free(name, _) =>
          if (v==name) repl else t
        case Const(_,_) | Bound(_) | Var(_,_) => t
        case Abs(name,typ,body) => Abs(name,typ,subst(body))
      }
      subst(term)
  }

  def stripAssumption(term:Term,number:Int) : Term = term match {
    case App(App(Const("HOL.implies",_),assm0),rest) =>
      assert(number>=0)
      if (number==0) rest
      else
        HOLogic.imp $ assm0 $ stripAssumption(rest,number-1)
    case _ => throw qrhl.UserException("Not enough assumptions")
  }
}
