package qrhl.logic

import info.hupel.isabelle.Operation
import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.hol.HOLogic.boolT
import info.hupel.isabelle.pure.{Abs, App, Bound, Const, Free, Term, Var, Typ => ITyp}
import info.hupel.isabelle.pure
import qrhl.isabelle.Isabelle

import scala.collection.mutable





final class Expression private (val typ: pure.Typ, val isabelleTerm:Term) {
  def encodeAsExpression(context: Isabelle.Context) : Term =
    context.isabelle.invoke(Expression.termToExpressionOp, (context.contextId, isabelleTerm))

  def stripAssumption(number: Int): Expression = Expression(typ,Expression.stripAssumption(isabelleTerm,number))

  override def equals(o: scala.Any): Boolean = o match {
    case o : Expression => typ == o.typ && isabelleTerm == o.isabelleTerm
    case _ => false
  }


  def checkWelltyped(context:Isabelle.Context, ityp:ITyp): Unit = {
    assert(ityp==this.typ,s"$ityp != ${this.typ}")
    assert(context.checkType(isabelleTerm) == typ)
  }

  /** Free variables, including those encoded as a string in "probability ... ... str" */
  private def freeVars(term: Term): Set[String] = {
    val fv = new mutable.SetBuilder[String,Set[String]](Set.empty)
    def collect(t:Term) : Unit = t match {
      case Free(v,_) => fv += v
        // TODO: what about Encoding.probability?
      case App(App(App(Const(Isabelle.probability_old.name,_),t1),t2),t3) =>
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

  /** Finds all classical and ambient variables in an expression. The expression is assumed not to have indexed variables. */
  def caVariables(environment: Environment, cvars : mutable.Set[CVariable], avars : mutable.Set[String]): Unit = {
//    val cvars = mutable.LinkedHashSet[CVariable]()
//    val avars = mutable.LinkedHashSet[String]()
    for (v<-variables) environment.cVariables.get(v) match {
      case Some(cv) => cvars += cv
      case None => avars += v
    }
  }

  override lazy val toString: String = Isabelle.theContext.prettyExpression(isabelleTerm)
//  val isabelleTerm : Term = isabelleTerm
  def simplify(isabelle: Option[Isabelle.Context], facts:List[String]): Expression = simplify(isabelle.get,facts)
  def simplify(context: Isabelle.Context, facts:List[String]): Expression = Expression(typ, context.simplify(isabelleTerm,facts))

  def map(f : Term => Term) : Expression = new Expression(typ, f(isabelleTerm))
  def substitute(v:CVariable, repl:Expression) : Expression = {
    assert(repl.typ==v.valueTyp)
    map(Expression.substitute(v.name, repl.isabelleTerm, _))
  }

  def index1(environment: Environment): Expression = index(environment, left=true)
  def index2(environment: Environment): Expression = index(environment, left=false)
  def index(environment: Environment, left: Boolean): Expression = {
    def idx(t:Term) : Term = t match {
      case App(t1,t2) => App(idx(t1),idx(t2))
      case Free(name,typ2) =>
        if (environment.ambientVariables.contains(name)) t
        else Free(Variable.index(left=left,name), typ2)
      case Const(_,_) | Bound(_) | Var(_,_) => t
      case Abs(name,typ2,body) => Abs(name,typ2,idx(body))
    }
    new Expression(typ,idx(isabelleTerm))
  }


  def leq(e: Expression): Expression = {
      val t = e.isabelleTerm
      val predicateT = Isabelle.predicateT // Should be the type of t
      val newT =  Const ("Orderings.ord_class.less_eq", ITyp.funT(predicateT, ITyp.funT(predicateT, boolT))) $ isabelleTerm $ t
      new Expression(Isabelle.boolT,newT)
  }

  def implies(e: Expression): Expression = {
    val t = e.isabelleTerm
    val newT = HOLogic.imp $ isabelleTerm $ t
//    val typ = Typ.bool(null)
    new Expression(Isabelle.boolT,newT)
  }

  def not: Expression = {
    assert(typ==HOLogic.boolT)
    new Expression(typ,Const("HOL.Not",HOLogic.boolT -->: HOLogic.boolT) $ isabelleTerm)
  }

}


object Expression {
  def decodeFromExpression(context:Isabelle.Context, t: Term): Expression = {
    val (term,typ) = context.isabelle.invoke(decodeFromExpressionOp, (context.contextId, t))
    Expression(typ, term)
  }

  val decodeFromExpressionOp: Operation[(BigInt,Term), (Term, ITyp)] =
    Operation.implicitly[(BigInt,Term), (Term,ITyp)]("expression_to_term")

  val termToExpressionOp: Operation[(BigInt, Term), Term] =
    Operation.implicitly[(BigInt, Term), Term]("term_to_expression")

  def trueExp(isabelle: Isabelle.Context): Expression = Expression(Isabelle.boolT, HOLogic.True)

  def apply(context: Isabelle.Context, str:String, typ:pure.Typ) : Expression = {
    val term = context.readTerm(Isabelle.unicodeToSymbols(str),typ)
    Expression(typ, term)
  }

  def apply(typ: pure.Typ, term:Term) : Expression =
    new Expression(typ, term)

  def unapply(e: Expression): Option[Term] = Some(e.isabelleTerm)

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
