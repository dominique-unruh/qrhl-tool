package qrhl.logic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.hol.HOLogic.boolT
import info.hupel.isabelle.pure.{Abs, App, Bound, Const, Free, Term, Var, Typ => ITyp, Type => IType}
import qrhl.isabelle.Isabelle

import scala.collection.mutable





final class Expression private (val isabelle:Isabelle.Context, val typ: Typ, val isabelleTerm:Term) {
  def stripAssumption(number: Int): Expression = Expression(isabelle,typ,Expression.stripAssumption(isabelleTerm,number))

  def checkWelltyped(typ:Typ): Unit = checkWelltyped(typ.isabelleTyp)
  def checkWelltyped(ityp:ITyp): Unit = {
    assert(ityp==this.typ.isabelleTyp)
    assert(isabelle.checkType(isabelleTerm) == typ.isabelleTyp)
  }

  /** Free variables, including those encoded as a string in "probability ... ... str" */
  private def freeVars(term: Term): Set[String] = {
    val fv = new mutable.SetBuilder[String,Set[String]](Set.empty)
    def collect(t:Term) : Unit = t match {
      case Free(v,_) => fv += v
      case App(App(App(Const("QRHL_Core.probability",_),t1),t2),t3) =>
        fv += Isabelle.dest_string(t1)
        collect(t2); collect(t3)
      case Const(_,_) | Bound(_) | Var(_,_) =>
      case App(t1,t2) => collect(t1); collect(t2)
      case Abs(_,_,body) => collect(body)
    }
    collect(term)
    fv.result
  }

  def variables : Set[String] = freeVars(isabelleTerm)

  override lazy val toString: String = isabelle.prettyExpression(isabelleTerm)
//  val isabelleTerm : Term = isabelleTerm
  def simplify(isabelle: Option[Isabelle.Context], facts:List[String]): Expression = simplify(isabelle.get,facts)
  def simplify(isabelle: Isabelle.Context, facts:List[String]): Expression = Expression(isabelle, typ, isabelle.simplify(isabelleTerm,facts))

  def map(f : Term => Term) : Expression = new Expression(isabelle, typ, f(isabelleTerm))
  def substitute(v:CVariable, repl:Expression) : Expression = {
    assert(repl.typ==v.typ)
    map(Expression.substitute(v.name, repl.isabelleTerm, _))
  }

  def index1(environment: Environment): Expression = index(environment, left=true)
  def index2(environment: Environment): Expression = index(environment, left=false)
  def index(environment: Environment, left: Boolean): Expression = {
    def idx(t:Term) : Term = t match {
      case App(t1,t2) => App(idx(t1),idx(t2))
      case Free(name,typ) =>
        if (environment.ambientVariables.contains(name)) t
        else Free(Variable.index(left=left,name), typ)
      case Const(_,_) | Bound(_) | Var(_,_) => t
      case Abs(name,typ,body) => Abs(name,typ,idx(body))
    }
    new Expression(isabelle,typ,idx(isabelleTerm))
  }


  def leq(e: Expression): Expression = {
      val t = e.isabelleTerm
      val predicateT = Isabelle.predicateT // Should be the type of t
      val newT =  Const ("Orderings.ord_class.less_eq", ITyp.funT(predicateT, ITyp.funT(predicateT, boolT))) $ isabelleTerm $ t
      val typ = Typ.bool(isabelle)
      new Expression(isabelle,typ,newT)
  }

  def implies(e: Expression): Expression = {
    val t = e.isabelleTerm
    val newT = HOLogic.imp $ isabelleTerm $ t
    val typ = Typ.bool(isabelle)
    new Expression(isabelle,typ,newT)
  }

  def not: Expression = {
    assert(typ.isabelleTyp==HOLogic.boolT)
    new Expression(isabelle,typ,Const("HOL.Not",HOLogic.boolT -->: HOLogic.boolT) $ isabelleTerm)
  }


}


object Expression {
  def trueExp(isabelle: Isabelle.Context): Expression = Expression(isabelle, Typ.bool(isabelle), HOLogic.True)

  def apply(isabelle:Isabelle.Context, str:String, typ:Typ) : Expression = {
    val term = isabelle.readTerm(Isabelle.unicodeToSymbols(str),typ.isabelleTyp)
    Expression(isabelle, typ, term)
  }
  def apply(isabelle:Isabelle.Context, typ: Typ, term:Term) : Expression = {
    new Expression(isabelle, typ, term)
  }

  def unapply(e: Expression): Option[Term] = Some(e.isabelleTerm)

  def substitute(v: String, repl: Term, term: Term): Term = {
      def subst(t:Term) : Term = t match {
        case App(t1,t2) => App(subst(t1),subst(t2))
        case Free(name,typ) =>
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
