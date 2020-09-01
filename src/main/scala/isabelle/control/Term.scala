package isabelle.control

import scala.annotation.tailrec
import scala.concurrent.ExecutionContext

sealed abstract class Term {
  val mlValue : MLValue[Term]
  implicit val isabelle : Isabelle
  def pretty(ctxt: Context)(implicit ec: ExecutionContext): String =
    Term.stringOfTerm[Context,Term,String](ctxt.mlValue, mlValue).retrieveNow
  val concrete : Term
  def $(that: Term): Term = App(this, that)
}

final class MLValueTerm(val mlValue: MLValue[Term])(implicit val isabelle: Isabelle, ec: ExecutionContext) extends Term {
  lazy val concrete : Term = ??? // see MLValueTyp.concrete for an example

  // TODO: should check if concrete has already been loaded, and if so, print the concrete Term
  override def toString: String = s"‹Terme${mlValue.stateString}›"
}

final class Const private[control] (val name: String, val typ: Typ, val initialMlValue: MLValue[Term]=null)
                                  (implicit val isabelle: Isabelle) extends Term {
  lazy val mlValue : MLValue[Term] = if (initialMlValue!=null) initialMlValue else ???
  @inline override val concrete: Const = this
  override def toString: String = name
}

object Const {
  def apply(name: String, typ: Typ)(implicit isabelle: Isabelle) = new Const(name, typ)

  @tailrec
  def unapply(term: Term): Option[(String, Typ)] = term match {
    case const : Const => Some((const.name,const.typ))
    case term : MLValueTerm => unapply(term.concrete)
  }
}

final class Free private (val name: String, val typ: Typ, val initialMlValue: MLValue[Term]=null)
                         (implicit val isabelle: Isabelle) extends Term {
  lazy val mlValue : MLValue[Term] = if (initialMlValue!=null) initialMlValue else ???
  @inline override val concrete: Free = this
  override def toString: String = name
}

object Free {
  def apply(name: String, typ: Typ)(implicit isabelle: Isabelle) = new Free(name, typ)

  @tailrec
  def unapply(term: Term): Option[(String, Typ)] = term match {
    case free : Free => Some((free.name,free.typ))
    case term : MLValueTerm => unapply(term.concrete)
  }
}

final class Var private(val name: String, val index: Int, val typ: Typ, val initialMlValue: MLValue[Term]=null)
                       (implicit val isabelle: Isabelle) extends Term {
  lazy val mlValue : MLValue[Term] = if (initialMlValue!=null) initialMlValue else ???
  @inline override val concrete: Var = this
  override def toString: String = s"?$name$index"
}

object Var {
  def apply(name: String, index: Int, typ: Typ)(implicit isabelle: Isabelle) = new Var(name, index, typ)

  @tailrec
  def unapply(term: Term): Option[(String, Int, Typ)] = term match {
    case v : Var => Some((v.name,v.index,v.typ))
    case term : MLValueTerm => unapply(term.concrete)
  }
}

final class App private (val fun: Term, val arg: Term, val initialMlValue: MLValue[Term]=null)
                        (implicit val isabelle: Isabelle) extends Term {
  lazy val mlValue : MLValue[Term] = if (initialMlValue!=null) initialMlValue else ???
  @inline override val concrete: App = this
  override def toString: String = s"($fun $$ $arg)"
}

object App {
  def apply(fun: Term, arg: Term)(implicit isabelle: Isabelle) = new App(fun, arg)

  @tailrec
  def unapply(term: Term): Option[(Term, Term)] = term match {
    case app : App => Some((app.fun,app.arg))
    case term : MLValueTerm => unapply(term.concrete)
  }
}

final class Abs private (val name: String, val typ: Typ, val body: Term, val initialMlValue: MLValue[Term]=null)
                        (implicit val isabelle: Isabelle) extends Term {
  lazy val mlValue : MLValue[Term] = if (initialMlValue!=null) initialMlValue else ???
  @inline override val concrete: Abs = this
  override def toString: String = s"(λ$name. $body)"
}

object Abs {
  def apply(name: String, typ: Typ, body: Term)(implicit isabelle: Isabelle) = new Abs(name,typ,body)

  @tailrec
  def unapply(term: Term): Option[(String, Typ, Term)] = term match {
    case abs : Abs => Some((abs.name,abs.typ,abs.body))
    case term : MLValueTerm => unapply(term.concrete)
  }
}


final class Bound private (val index: Int, val initialMlValue: MLValue[Term]=null)
                          (implicit val isabelle: Isabelle) extends Term {
  lazy val mlValue : MLValue[Term] = if (initialMlValue!=null) initialMlValue else ???
  @inline override val concrete: Bound = this
  override def toString: String = s"Bound $index"
}

object Bound {
  def apply(index: Int)(implicit isabelle: Isabelle) = new Bound(index)

  @tailrec
  def unapply(term: Term): Option[Int] = term match {
    case bound : Bound => Some(bound.index)
    case term : MLValueTerm => unapply(term.concrete)
  }
}



object Term {
  private implicit var isabelle: Isabelle = _
  private var readTerm: MLValue[Context => String => Term] = _
  private var stringOfTerm: MLValue[Context => Term => String] = _
//  private[control] var whatTerme: MLValue[Term => Int] = _
//  private[control] var numArgs: MLValue[Term => Int] = _
//  private[control] var TermeName: MLValue[Term => String] = _
//  private[control] var getArg: MLValue[Term => Int => Term] = _

  // TODO Ugly hack, fails if there are several Isabelle objects
  def init(isabelle: Isabelle): Unit = synchronized {
    if (this.isabelle == null) {
      this.isabelle = isabelle
      implicit val _ = isabelle
      Typ.init(isabelle)
      isabelle.executeMLCodeNow("exception E_Term of term")
      readTerm = MLValue.compileFunction[Context, String => Term]("fn (E_Context ctxt) => E_ExnExn (fn (E_String str) => Syntax.read_term ctxt str |> E_Term)")
      stringOfTerm = MLValue.compileFunction[Context, Term => String]("fn (E_Context ctxt) => E_ExnExn (fn (E_Term term) => Syntax.string_of_term ctxt term |> E_String)")
//      whatTerme = MLValue.compileFunction[Term, Int]("fn (E_Term Term) => (case Term of Terme _ => 1 | TFree _ => 2 | TVar _ => 3) |> E_Int")
//      TermeName = MLValue.compileFunction[Term, String]("fn (E_Term Term) => (case Term of Terme (name,_) => name | TFree (name,_) => name | TVar ((name,_),_) => name) |> E_String")
//      numArgs = MLValue.compileFunction[Term, Int]("fn (E_Term Term) => (case Term of Terme (_,args) => length args | TFree (_,sort) => length sort | TVar (_,sort) => length sort) |> E_Int")
//      getArg = MLValue.compileFunction[Term, Int => Term]("fn (E_Term (Terme (_,args))) => E_ExnExn (fn (E_Int i) => nth args i |> E_Term)")
    }
  }

  def apply(context: Context, string: String)(implicit ec: ExecutionContext): MLValueTerm = {
    new MLValueTerm(readTerm[Context, String, Term](context.mlValue, MLValue(string)))
  }
}

object TestTerme {
  import ExecutionContext.Implicits.global

  def main(args: Array[String]): Unit = {
    implicit val isabelle : Isabelle = new Isabelle
    Term.init(isabelle)
    val ctxt = Context("Main")
    val term = Term(ctxt, "(1::nat)")
    println("****", term.pretty(ctxt))
    term match {
      case Const(one,typ) => println(s"XXXX ${(one, typ.pretty(ctxt))}")
    }
  }
}
