package qrhl.logic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.hol.HOLogic.boolT
import info.hupel.isabelle.pure.{Abs, App, Bound, Const, Free, Term, Var, Typ => ITyp, Type => IType}
import qrhl.isabelle.Isabelle

// Expressions
/*sealed trait Expression {
  def simplify(isabelle: Option[Isabelle.Context]) : Expression

  def index1: Expression = index(true)
  def index2: Expression = index(false)
  def index(left:Boolean): Expression

  def substitute(v: CVariable, value: Expression): Expression

  def leq(e: Expression): Expression
  @deprecated
  def unmarkedString : String = toString
}*/


/*object Expression {
  def apply(isabelle: Option[Isabelle.Context], str: String, typ: Typ): Expression = isabelle match {
    case Some(isa) => IsabelleExpression(isa, str, typ)
    case None => ???
  }
}*/




final class Expression private (val isabelle:Isabelle.Context, term:Term) {
  def variables : Set[String] = Isabelle.freeVars(term)

  override lazy val toString: String = isabelle.prettyExpression(term)
  val isabelleTerm : Term = term
  def simplify(isabelle: Option[Isabelle.Context]): Expression = simplify(isabelle.get)
  def simplify(isabelle: Isabelle.Context): Expression = Expression(isabelle, isabelle.simplify(term))

  def map(f : Term => Term) : Expression = new Expression(isabelle, f(term))
  def substitute(v:CVariable, repl:Expression) : Expression = map(Expression.substitute(v.name, repl.isabelleTerm, _))

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
    new Expression(isabelle,idx(term))
  }


  def leq(e: Expression): Expression = e match {
    case e2 : Expression =>
      val t = e2.isabelleTerm
      val assertionT = Typ(isabelle,"assertion").isabelleTyp  // Should be the type of t
      val newT =  Const ("Orderings.ord_class.less_eq", ITyp.funT(assertionT, ITyp.funT(assertionT, boolT))) $ term $ t
      new Expression(isabelle,newT)
  }
}


object Expression {
  def apply(isabelle:Isabelle.Context, str:String, typ:Typ) : Expression = {
    val term = isabelle.readTerm(Isabelle.unicodeToSymbols(str),typ.isabelleTyp)
    Expression(isabelle,term)
  }
  def apply(isabelle:Isabelle.Context, term:Term) : Expression = {
    new Expression(isabelle,term)
  }

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
}
