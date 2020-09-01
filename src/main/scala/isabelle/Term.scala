package isabelle

import isabelle.control.{Isabelle, MLValue}

import scala.annotation.tailrec
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Awaitable, ExecutionContext}

sealed abstract class Term {
  val mlValue : MLValue[Term]
  implicit val isabelle : Isabelle
  def pretty(ctxt: Context)(implicit ec: ExecutionContext): String =
    Term.stringOfTerm[Context,Term,String](ctxt.mlValue, mlValue).retrieveNow
  val concrete : Term
  def $(that: Term): Term = App(this, that)
}

final class CTerm private (val ctermMlValue: MLValue[CTerm])(implicit val isabelle: Isabelle, ec: ExecutionContext) extends Term {
  override lazy val mlValue: MLValue[Term] = Term.termOfCterm[CTerm, Term](ctermMlValue)
  override def pretty(ctxt: Context)(implicit ec: ExecutionContext): String = pretty
  def pretty : String = ???
  lazy val concrete: Term = new MLValueTerm(mlValue).concrete
}

object CTerm {
  def apply(ctxt: Context, term: Term)(implicit isabelle: Isabelle, ec: ExecutionContext) : CTerm = {
    implicit val _ = ctxt
    new CTerm(Term.ctermOfTerm[Context,Term,CTerm](ctxt.mlValue, term.mlValue))
  }
}

final class MLValueTerm(val mlValue: MLValue[Term])(implicit val isabelle: Isabelle, ec: ExecutionContext) extends Term {
  @inline private def await[A](awaitable: Awaitable[A]) : A = Await.result(awaitable, Duration.Inf)

  lazy val concrete : Term =
    Term.whatTerm[Term,Int](mlValue).retrieveNow match {
      case 1 =>
        val name = Term.termName[Term,String](mlValue).retrieve
        val typ = new MLValueTyp(Term.termTyp[Term,Typ](mlValue))
        new Const(await(name), typ, mlValue)
      case 2 =>
        val name = Term.termName[Term,String](mlValue).retrieve
        val typ = new MLValueTyp(Term.termTyp[Term,Typ](mlValue))
        new Free(await(name), typ, mlValue)
      case 3 =>
        val name = Term.termName[Term,String](mlValue).retrieve
        val typ = new MLValueTyp(Term.termTyp[Term,Typ](mlValue))
        ??? // Var
      case 4 => ??? // Bound
      case 5 => ??? // App
      case 6 =>
        val name = Term.termName[Term,String](mlValue).retrieve
        val typ = new MLValueTyp(Term.termTyp[Term,Typ](mlValue))
        ??? // Abs
    }
  // TODO: should check if concrete has already been loaded, and if so, print the concrete Term
  override def toString: String = s"‹Terme${mlValue.stateString}›"
}

final class Const private[isabelle] (val name: String, val typ: Typ, val initialMlValue: MLValue[Term]=null)
                                  (implicit val isabelle: Isabelle, ec: ExecutionContext) extends Term {
  lazy val mlValue : MLValue[Term] =
    if (initialMlValue!=null) initialMlValue
    else Term.makeConst[String,Typ,Term](MLValue(name),typ.mlValue)
  @inline override val concrete: Const = this
  override def toString: String = name
}

object Const {
  def apply(name: String, typ: Typ)(implicit isabelle: Isabelle, ec: ExecutionContext) = new Const(name, typ)

  @tailrec
  def unapply(term: Term): Option[(String, Typ)] = term match {
    case const : Const => Some((const.name,const.typ))
    case term : MLValueTerm => unapply(term.concrete)
  }
}

final class Free private[isabelle] (val name: String, val typ: Typ, val initialMlValue: MLValue[Term]=null)
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
  private[isabelle] var termOfCterm: MLValue[CTerm => Term] = _
  private[isabelle] var ctermOfTerm: MLValue[Context => Term => CTerm] = _

  private[isabelle] var whatTerm : MLValue[Term => Int] = _
  private[isabelle] var termName: MLValue[Term => String] = _
  private[isabelle] var termTyp: MLValue[Term => Typ] = _
  private[isabelle] var makeConst: MLValue[String => Typ => Term] = _

  // TODO Ugly hack, fails if there are several Isabelle objects
  def init(isabelle: Isabelle)(implicit ec: ExecutionContext): Unit = synchronized {
    if (this.isabelle == null) {
      this.isabelle = isabelle
      implicit val _ = isabelle
      Typ.init(isabelle)
      isabelle.executeMLCodeNow("exception E_Term of term;; exception E_CTerm of cterm")
      readTerm = MLValue.compileFunction[Context, String => Term]("fn (E_Context ctxt) => E_ExnExn (fn (E_String str) => Syntax.read_term ctxt str |> E_Term)")
      stringOfTerm = MLValue.compileFunction[Context, Term => String]("fn (E_Context ctxt) => E_ExnExn (fn (E_Term term) => Syntax.string_of_term ctxt term |> E_String)")
      whatTerm = MLValue.compileFunction[Term, Int]("fn (E_Term term) => (case term of Const _ => 1 | Free _ => 2 | Var _ => 3 | Bound _ => 4 | Abs _ => 5 | _ $ _ => 6) |> E_Int")
      termName = MLValue.compileFunction[Term, String]("fn (E_Term term) => (case term of Const (name,_) => name | Free (name,_) => name | Var ((name,_),_) => name | Abs(name,_,_) => name) |> E_String")
      termTyp = MLValue.compileFunction[Term, Typ]("fn (E_Term term) => (case term of Const (_,typ) => typ | Free (_,typ) => typ | Var (_,typ) => typ | Abs(_,typ,_) => typ) |> E_Typ")
      termOfCterm = MLValue.compileFunction[CTerm, Term]("fn (E_CTerm cterm) => E_Term (Thm.term_of cterm)")
      ctermOfTerm = MLValue.compileFunction[Context, Term => CTerm]("fn (E_Context ctxt) => E_ExnExn (fn (E_Term term) => E_CTerm (Thm.cterm_of ctxt term))")
      makeConst = MLValue.compileFunction[String, Typ => Term]("fn (E_String name) => E_ExnExn (fn (E_Typ typ) => E_Term (Const (name, typ)))")
    }
  }

  def apply(context: Context, string: String)(implicit ec: ExecutionContext): MLValueTerm = {
    new MLValueTerm(readTerm[Context, String, Term](context.mlValue, MLValue(string)))
  }
}

object TestTerm {
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

    val cterm = CTerm(ctxt, Const("HOL.True", Type("HOL.bool")))
    val termAgain = cterm.concrete
    println(s"termAgain: ${termAgain.pretty(ctxt)}")
  }
}
