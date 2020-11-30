package qrhl.isabellex

import org.log4s
import org.log4s.Logger
import qrhl.logic.{CVariable, Environment, ExprVariableUse, QVariable, Variable, VariableUse}

import scala.collection.mutable
import de.unruh.isabelle.control
import qrhl.{UserException, Utils, logic}

import scala.collection.immutable.ListSet
import scala.collection.mutable.ListBuffer
import IsabelleX.{globalIsabelle => GIsabelle}
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.{Abs, App, Bound, Const, Free, Term, Thm, Typ, Var}
import hashedcomputation.{Hash, Hashable, HashedValue}
import qrhl.isabellex.IsabelleX.globalIsabelle.Ops

// Implicits
import scala.concurrent.ExecutionContext.Implicits.global
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._
import qrhl.isabellex.Implicits._

final class RichTerm private(val typ: Typ, val isabelleTerm:Term, _pretty:Option[String]=None) extends HashedValue {
  override def hash: Hash[RichTerm.this.type] =
    Hash.hashString(s"RichTerm: ${Hashable.hash(typ)} ${Hashable.hash(isabelleTerm)}") // TODO better hash

  def renameCVariables(renaming: List[(Variable, Variable)]): RichTerm = {
    def s(t: Term) : Term = t match {
      case Const(name, typ) => t
      case Free(name, typ) =>
        renaming.find { case (x,y) => x.isClassical && x.name == name } match {
          case None => t
          case Some((x,y)) =>
            assert(y.isClassical)
            assert(x.valueTyp == y.valueTyp)
            Free(y.name, typ)
        }
      case Var(name, index, typ) => t
      case Bound(index) => t
      case Abs(name, typ, body) => Abs(name, typ, s(body))
      case App(fun, arg) => App(s(fun), s(arg))
    }
    RichTerm(typ, s(isabelleTerm))
  }

  def renameCVariable(from: CVariable, to: CVariable): RichTerm = {
    assert(from.valueTyp==to.valueTyp)
    val fromTerm = from.valueTerm
    val toTerm = to.valueTerm
    def rename(t: Term): Term = t match {
      case App(t,u) => App(rename(t), rename(u))
      case Abs(name,typ,body) => Abs(name,typ,rename(body))
      case _ : Bound | _ : Const | _ : Var => t
      case v : Free if v==fromTerm => toTerm
      case v : Free if v==toTerm =>
        throw UserException(s"Replacing ${from.name} by ${to.name}, but ${to.name} already occurs in $this")
      case _ : Free => t
    }

    RichTerm(typ, rename(isabelleTerm))
  }

  def encodeAsExpression(context: IsabelleX.ContextX) : RichTerm =
    RichTerm(Ops.termToExpressionOp(MLValue((context.context, isabelleTerm))).retrieveNow)

  def stripAssumption(number: Int): RichTerm = RichTerm(typ,RichTerm.stripAssumption(isabelleTerm,number))

  override def equals(o: scala.Any): Boolean = o match {
    case o : RichTerm => typ == o.typ && isabelleTerm == o.isabelleTerm
    case _ => false
  }

  def checkWelltyped(context:IsabelleX.ContextX, Typ:Typ): Unit = {
    assert(Typ==this.typ,s"$Typ != ${this.typ}")
    assert(context.checkType(isabelleTerm) == typ)
  }

  /** Free variables */
  private def freeVars(term: Term): Set[String] = {
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

  /** Finds all classical and ambient variables in an expression.
   * The quantum variables are an estimate, it is possible to have terms that contain quantum variables that are not detected by this function.
   * @param deindex If true, indexed program variables are replaced by their unindexed counterparts
   * */
  def variables(environment: Environment, deindex: Boolean=false): ExprVariableUse = {
    val avars = new ListBuffer[String]
    val pvars = new ListBuffer[Variable]

    val C = new Utils.MapMatch(environment.cVariables)
    val Q = new Utils.MapMatch(environment.qVariables)
    val A = new Utils.MapMatch(environment.ambientVariables)

    for (v<-variables) v match {
      case C(cv) => pvars += cv
      case Q(qv) => pvars += qv
      case A(_) => v
      case Variable.Indexed(C(cv), left) =>
        pvars += (if (deindex) cv else cv.index(left))
      case Variable.Indexed(Q(qv), left) =>
        pvars += (if (deindex) qv else qv.index(left))
      case _ => throw UserException(s"Internal error: Encountered unknown free variable $v in term $this. This should not happen.")
    }

    ExprVariableUse(program = ListSet(pvars.toSeq:_*), ambient = ListSet(avars.toSeq:_*))
  }

//    /** Finds all classical and ambient variables in an expression. The expression is assumed not to have indexed variables. */
//  def caVariables(environment: Environment, vars : VariableUse[mutable.Set]): Unit = {
////    val cvars = mutable.LinkedHashSet[CVariable]()
////    val avars = mutable.LinkedHashSet[String]()
//    for (v<-variables) environment.cVariables.get(v) match {
//      case Some(cv) => vars.cvars += cv
//      case None => vars.avars += v
//    }
//  }

  override lazy val toString: String = _pretty match {
    case Some(s) => s
    case _ => IsabelleX.theContext.prettyExpression (isabelleTerm)
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
      case Const(_,_) | Bound(_) | Var(_,_,_) => t
      case Abs(name,typ2,body) => Abs(name,typ2,idx(body))
    }
    new RichTerm(typ = typ, isabelleTerm = idx(isabelleTerm))
  }


  def leq(e: RichTerm): RichTerm = {
      val t = e.isabelleTerm
      val predicateT = GIsabelle.predicateT // Should be the type of t
      val newT =  Const ("Orderings.ord_class.less_eq", predicateT -->: predicateT -->: GIsabelle.boolT) $ isabelleTerm $ t
      RichTerm(GIsabelle.boolT,newT)
  }

  def implies(e: RichTerm): RichTerm = {
    val t = e.isabelleTerm
    val newT = GIsabelle.implies(isabelleTerm, t)
//    val typ = Typ.bool(null)
    RichTerm(GIsabelle.boolT,newT)
  }

  def not: RichTerm = {
    assert(typ==GIsabelle.boolT)
    RichTerm(typ,GIsabelle.not(isabelleTerm))
  }

}


object RichTerm {
  private val logger: Logger = log4s.getLogger

  def decodeFromExpression(context:IsabelleX.ContextX, t: Term): RichTerm =
    RichTerm(Ops.decodeFromExpressionOp(MLValue((context.context,t))).retrieveNow)

  def trueExp(isabelle: IsabelleX.ContextX): RichTerm = RichTerm(GIsabelle.boolT, GIsabelle.True_const)

//  private val readExpressionOp =
//    MLValue.compileFunction[(Context, String, Typ), Term]("QRHL_Operations.read_expression")

  def apply(context: IsabelleX.ContextX, str:String, typ:Typ) : RichTerm = {
    RichTerm(Term(context.context,IsabelleX.symbols.unicodeToSymbols(str),typ))
//    RichTerm(readExpressionOp[(Context,String,Typ), Term](MLValue((context.context,IsabelleX.symbols.unicodeToSymbols(str),typ))).retrieveNow)
  }

  //    val term = context.readTerm(Isabelle.unicodeToSymbols(str),typ)
//    Expression(typ, term)

  def apply(term:Term) : RichTerm = RichTerm(typ=IsabelleX.fastype_of(term), term)

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
        GIsabelle.implies(assm0, stripAssumption(rest,number-1))
    case _ => throw qrhl.UserException("Not enough assumptions")
  }
}
