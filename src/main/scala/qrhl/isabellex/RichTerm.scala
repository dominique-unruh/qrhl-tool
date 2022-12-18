package qrhl.isabellex

import qrhl.logic.{CVariable, Environment, Variable}

import scala.collection.mutable.ListBuffer
import IsabelleX.globalIsabelle
import de.unruh.isabelle.pure.{Abs, App, Bound, Const, Free, Term, Thm, Typ, Var}
import hashedcomputation.{Hash, HashTag, Hashable, HashedValue}

// Implicits
import scala.concurrent.ExecutionContext.Implicits.global
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._
import qrhl.isabellex.Implicits._

final class RichTerm private(val typ: Typ, val isabelleTerm:Term, _pretty:Option[String]=None) extends HashedValue {
  override def hash: Hash[RichTerm.this.type] =
    HashTag()(Hashable.hash(typ), Hashable.hash(isabelleTerm))

  def stripAssumption(number: Int): RichTerm = RichTerm(typ,RichTerm.stripAssumption(isabelleTerm,number))

  override def equals(o: scala.Any): Boolean = o match {
    case o : RichTerm => typ == o.typ && isabelleTerm == o.isabelleTerm
    case _ => false
  }

  def checkWelltyped(context:IsabelleX.ContextX, typ:Typ): Unit = {
    assert(typ == this.typ, s"$typ != ${this.typ}")
    assert(context.checkType(isabelleTerm) == typ)
  }

  /** Free variables */
    // TODO use IsabelleX.freeVars instead
  private def freeVars(term: Term): Set[String] = {
    //noinspection DuplicatedCode
    val fv = Set.newBuilder[String]
    def collect(t:Term) : Unit = t match {
      case Free(v,_) => fv += v
//      case App(App(App(Const(Isabelle.probability_old.name,_),t1),t2),t3) =>
//        fv += Isabelle.dest_string(t1)
//        collect(t2); collect(t3)
      case Const(_,_) | Bound(_) | Var(_,_,_) =>
      case App(t1,t2) => collect(t1); collect(t2)
      case Abs(_,_,body) => collect(body)
    }
    collect(term)
    fv.result()
  }

  def variables : Set[String] = freeVars(isabelleTerm)

  override lazy val toString: String = _pretty match {
    case Some(s) => s
    case _ => //noinspection ScalaDeprecation
      IsabelleX.theContext.prettyTerm (isabelleTerm)
  }

//  val isabelleTerm : Term = isabelleTerm
  def simplify(isabelle: Option[IsabelleX.ContextX], facts:List[String]): (RichTerm,Thm) = simplify(isabelle.get,facts)

  def simplify(context: IsabelleX.ContextX, facts:List[String], thms:ListBuffer[Thm]) : RichTerm = {
    val (t,thm) = context.simplify(isabelleTerm, facts)
    thms += thm
    t
  }

  def simplify(context: IsabelleX.ContextX, facts:List[String]): (RichTerm,Thm) =
    context.simplify(isabelleTerm, facts)

  def map(f : Term => Term) : RichTerm = RichTerm(typ, f(isabelleTerm))

  def substitute(v:CVariable, repl:RichTerm) : RichTerm = {
    assert(repl.typ==v.valueTyp)
    map(RichTerm.substitute(v.basename, repl.isabelleTerm, _))
  }

  def index1(environment: Environment): RichTerm = index(environment, left=true)
  def index2(environment: Environment): RichTerm = index(environment, left=false)
  def index(environment: Environment, left: Boolean): RichTerm = {
    def idx(t:Term) : Term = t match {
      case App(t1,t2) => App(idx(t1),idx(t2))
      case Free(name,typ2) =>
        if (environment.ambientVariables.contains(name)) t
        else Free(Variable.index(left=left,name), typ2)
      case Const(_,_) | Bound(_) | Var(_,_,_) => t
      case Abs(name,typ2,body) => Abs(name,typ2,idx(body))
    }
    new RichTerm(typ = typ, isabelleTerm = idx(isabelleTerm))
  }


  def leq(e: RichTerm): RichTerm = {
      val t = e.isabelleTerm
      val predicateT = globalIsabelle.predicateT // Should be the type of t
      val newT =  Const ("Orderings.ord_class.less_eq", predicateT -->: predicateT -->: globalIsabelle.boolT) $ isabelleTerm $ t
      RichTerm(globalIsabelle.boolT,newT)
  }

  def implies(e: RichTerm): RichTerm = {
    val t = e.isabelleTerm
    val newT = globalIsabelle.implies(isabelleTerm, t)
//    val typ = Typ.bool(null)
    RichTerm(globalIsabelle.boolT,newT)
  }

  def not: RichTerm = {
    assert(typ == globalIsabelle.boolT)
    RichTerm(typ, globalIsabelle.not(isabelleTerm))
  }
}


object RichTerm {
  def apply(context: IsabelleX.ContextX, str:String, typ:Typ) : RichTerm = {
    RichTerm(Term(context.context,IsabelleX.symbols.unicodeToSymbols(str),typ))
//    RichTerm(readExpressionOp[(Context,String,Typ), Term](MLValue((context.context,IsabelleX.symbols.unicodeToSymbols(str),typ))).retrieveNow)
  }

  def apply(term:Term) : RichTerm = RichTerm(typ=term.fastType, term)

  def apply(typ: Typ, term:Term) : RichTerm =
    new RichTerm(typ=typ, isabelleTerm = term)

  def unapply(e: RichTerm): Option[Term] = Some(e.isabelleTerm)

  def substitute(v: String, repl: Term, term: Term): Term = {
      def subst(t:Term) : Term = t match {
        case App(t1,t2) => App(subst(t1),subst(t2))
        case Free(name, _) =>
          if (v==name) repl else t
        case Const(_,_) | Bound(_) | Var(_,_,_) => t
        case Abs(name,typ,body) => Abs(name,typ,subst(body))
      }
      subst(term)
  }

  def stripAssumption(term:Term,number:Int) : Term = term match {
    case App(App(Const("HOL.implies",_),assm0),rest) =>
      assert(number>=0)
      if (number==0) rest
      else
        globalIsabelle.implies(assm0, stripAssumption(rest,number-1))
    case _ => throw qrhl.UserException("Not enough assumptions")
  }
}
