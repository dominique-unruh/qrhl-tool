package qrhl.logic

import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.{Abs, App, Bound, Const, Context, Free, Term, Thm, Typ, Type, Var}
import hashedcomputation.{Hash, HashTag, HashedValue}
import qrhl.UserException
import qrhl.isabellex.IsabelleX.{ContextX, globalIsabelle}
import qrhl.isabellex.IsabelleX.globalIsabelle.{Ops, cl2T, clT}
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.logic.Variable.{Index12, NoIndex}

import scala.collection.immutable.ListSet
import scala.collection.mutable.ListBuffer

// Implicits
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._
import qrhl.isabellex.Implicits._

class Expression(val term: RichTerm) extends HashedValue {
  override def equals(obj: Any): Boolean = obj match {
    case e: Expression => term == e.term
    case e: ExpressionInstantiated => this == e.abstractMemory
    case _ => false
  }

  def renameCVariables(renaming: List[(CVariable, CVariable)]): Expression = {
    val mem2: Term = renaming.foldRight[Term](Bound(0)) { case ((x,y),mem) =>
      val varTyp = x.valueTyp
      assert(y.valueTyp == varTyp)
      assert(x.memTyp == memTyp)
      assert(y.memTyp == memTyp)
      x.setter(y.getter(Bound(0)), mem)
    }
    Expression.fromTerm(
      Abs("mem", memTyp, term.isabelleTerm $ mem2))
  }

  /*  // TODO: Do this by substition of mem and then cleaning the expression
  def renameCVariables(renaming: List[(Variable with Nonindexed, Variable with Nonindexed)]): Expression = {
    def s(t: Term): Term = t match {
      case Const(_, _) => t
      case Free(name, typ) =>
        renaming.find { case (x, _) => x.isClassical && x.name == name } match {
          case None => t
          case Some((x, y)) =>
            assert(y.isClassical)
            assert(x.valueTyp == y.valueTyp)
            Free(y.name, typ)
        }
      case Var(_, _, _) => t
      case Bound(_) => t
      case Abs(name, typ, body) => Abs(name, typ, s(body))
      case App(fun, arg) => App(s(fun), s(arg))
    }

    new Expression(RichTerm(term.typ, s(term.isabelleTerm)))
  }*/

/*  def renameCVariable(from: Variable with Nonindexed, to: Variable with Nonindexed): Expression = {
    assert(from.valueTyp == to.valueTyp)
    val fromTerm = from.variableTermShort
    val toTerm = to.variableTermShort

    def rename(t: Term): Term = t match {
      case App(t, u) => App(rename(t), rename(u))
      case Abs(name, typ, body) => Abs(name, typ, rename(body))
      case _: Bound | _: Const | _: Var => t
      case v: Free if v == fromTerm => toTerm
      case v: Free if v == toTerm =>
        throw UserException(s"Replacing ${from.name} by ${to.name}, but ${to.name} already occurs in $this")
      case _: Free => t
    }

    new Expression(RichTerm(term.typ, rename(term.isabelleTerm)))
  }*/

  def simplify(context: ContextX, facts: List[String], thms: ListBuffer[Thm]) =
    new Expression(term.simplify(context, facts, thms))

  def castIndexed: ExpressionIndexed = {
    assert(memTyp == cl2T)
    new ExpressionIndexed(term)
  }
  def castNonindexed: ExpressionNonindexed = {
    assert(memTyp == clT)
    new ExpressionNonindexed(term)
  }

  lazy val (memTyp, rangeTyp) = term.typ match {
    case Type("fun", memTyp, rangeTyp) => (memTyp, rangeTyp)
    case typ => throw UserException(s"Internal error: encountered expression of invalid type ${IsabelleX.theContext.prettyTyp(typ)}")
  }
  def checkWelltyped(context: ContextX): Unit = {
    term.checkWelltyped(context, term.typ)
    memTyp
  }

  override def hash: Hash[Expression.this.type] =
    HashTag()(term.hash)

  def shortform(context: ContextX): RichTerm = {
    RichTerm(Ops.decodeFromExpressionOp(context.context,term.isabelleTerm).retrieveNow)
  }

  def leq(other: Expression): RichTerm = {
    assert(other.memTyp == memTyp)
    assert(other.rangeTyp == rangeTyp)

    RichTerm(globalIsabelle.all("mem", memTyp,
      globalIsabelle.less_eq(rangeTyp) $ (term.isabelleTerm $ Bound(0)) $ (other.term.isabelleTerm $ Bound(0))
    ))
  }

  def clean(ctxt: Context): Expression = Expression.fromTerm(Ops.clean_expression(ctxt, term.isabelleTerm).retrieveNow)
}

object Expression {
  def fromString(context: Context, string: String, rangeTyp: Typ, indexed: Boolean): Expression =
    fromString(context, string, rangeTyp, globalIsabelle.clT(indexed = indexed))

  def fromString(context: Context, string: String, rangeTyp: Typ, memTyp: Typ): Expression =
    Expression.fromTerm(
      Ops.readExpressionOp(context, IsabelleX.symbols.unicodeToSymbols(string), rangeTyp, memTyp).retrieveNow)

  def fromTerm(term: Term) = new Expression(RichTerm(term))
  def fromTerm(term: RichTerm) = new Expression(term)
  def constant(term: Term, typ: Typ): Expression = fromTerm(Abs("mem", typ, term))
}


class ExpressionInstantiated(val termInst: RichTerm, val memTyp: Typ) extends HashedValue {
  override def equals(obj: Any): Boolean = obj match {
    case e : ExpressionInstantiated => termInst == e.termInst && memTyp == e.memTyp
    case e : Expression => abstractMemory == e
    case _ => false
  }
  override def hash: Hash[ExpressionInstantiated.this.type] =
    HashTag()(termInst.hash)
  def rangeTyp: Typ = termInst.typ
  def memoryVariable: Free = Free("_memory", memTyp)
  def abstractMemory =
    new Expression(RichTerm(Abs("mem", cl2T, globalIsabelle.abstract_over(memoryVariable, termInst.isabelleTerm))))
  // TODO: inefficient: The ML code for decodeFromExpression converts back to instantiated form
  def shortform(context: ContextX): RichTerm = abstractMemory.shortform(context)
  def prettyShortform: String = shortform(IsabelleX.theContext).toString
  def renameCVariables(renaming: List[(CVariable, CVariable)]): Expression =
    abstractMemory.renameCVariables(renaming)

  def castIndexed: ExpressionInstantiatedIndexed = {
    assert(memTyp == cl2T)
    new ExpressionInstantiatedIndexed(termInst)
  }

  def castNonindexed: ExpressionInstantiatedNonindexed = {
    assert(memTyp == clT)
    new ExpressionInstantiatedNonindexed(termInst)
  }
}

class ExpressionInstantiatedNonindexed(term: RichTerm)
  extends ExpressionInstantiated(term, clT) with HashedValue {
  def variables(ctxt: Context, environment: Environment): ExprVariableUse = {
    val (pvars, others) = Ops.variables_in_expression(ctxt, term.isabelleTerm).retrieveNow
    val pvars2 = pvars map { case (cq, name, index, typ) =>
      if (index != NoIndex)
        throw UserException(s"Encountered indexed variable ${name}1/2 in expression $this")
      if (cq)
        CVariable.fromName(name, typ)
      else
        QVariable.fromName(name, typ)
    }

    for (v <- others)
      if (!environment.ambientVariables.contains(v))
        throw UserException(s"Internal error: Encountered unknown free variable $v in term $this. This should not happen.")

    ExprVariableUse(program = ListSet(pvars2: _*), ambient = ListSet(others: _*))
  }

  override def renameCVariables(renaming: List[(CVariable, CVariable)]): ExpressionNonindexed =
    abstractMemory.renameCVariables(renaming).castNonindexed
}

class ExpressionInstantiatedIndexed(term: RichTerm)
  extends ExpressionInstantiated(term, cl2T) with HashedValue {

  def variables(ctxt: Context, environment: Environment): ExprVariableUseI = {
    val (pvars, others) = Ops.variables_in_expression(ctxt, term.isabelleTerm).retrieveNow
    val pvars2 = pvars map { case (cq, name, index, typ) =>
      if (index == NoIndex)
        throw UserException(s"Encountered non-indexed variable $name in expression $this")
      if (cq)
        CVariable.fromName(name, typ, index = index.asInstanceOf[Index12])
      else
        QVariable.fromName(name, typ, index = index.asInstanceOf[Index12])
    }

    for (v <- others)
      if (!environment.ambientVariables.contains(v))
        throw UserException(s"Internal error: Encountered unknown free variable $v in term $this. This should not happen.")

    new ExprVariableUseI(program = ListSet(pvars2: _*), ambient = ListSet(others: _*))
  }

  override def abstractMemory: ExpressionIndexed = super.abstractMemory.castIndexed

  override def renameCVariables(renaming: List[(CVariable, CVariable)]): ExpressionIndexed =
    abstractMemory.renameCVariables(renaming).castIndexed
}

object ExpressionInstantiatedIndexed {
  def fromTerm(term: Term) = new ExpressionInstantiatedIndexed(RichTerm(term))
  def fromTerm(term: RichTerm) = new ExpressionInstantiatedIndexed(term)
}

class ExpressionIndexed(term: RichTerm) extends Expression(term) with HashedValue {
  override def checkWelltyped(context: ContextX): Unit = {
    super.checkWelltyped(context)
    assert(memTyp == cl2T)
  }

  override def hash: Hash[ExpressionIndexed.this.type] =
    HashTag()(term.hash)

  override def castIndexed: this.type = this

  def instantiateMemory = new ExpressionInstantiatedIndexed(term.longformInstantiate(indexed=true))

  def variables(ctxt: Context, environment: Environment): ExprVariableUse =
    instantiateMemory.variables(ctxt, environment)

  override def simplify(context: ContextX, facts: List[String], thms: ListBuffer[Thm]): ExpressionIndexed = {
    super.simplify(context, facts, thms).castIndexed
  }

  override def clean(ctxt: Context): ExpressionIndexed = clean(ctxt).castIndexed

  def renameCVariablesCQ(renaming: List[(Variable with Indexed, Variable with Indexed)]): ExpressionIndexed =
    renameCVariables(renaming collect { case (a: CVariable, b: CVariable) => (a, b) })

  override def renameCVariables(renaming: List[(CVariable, CVariable)]): ExpressionIndexed =
    super.renameCVariables(renaming).castIndexed
}

object ExpressionIndexed {
  /** Parses an indexed expression in shortform. */
  def fromString(context: Context, string: String, rangeTyp: Typ): ExpressionIndexed =
    Expression.fromString(context, string, rangeTyp, indexed = true).castIndexed
  def fromTerm(term: Term) = new ExpressionIndexed(RichTerm(term))
  def fromTerm(term: RichTerm) = new ExpressionIndexed(term)
  def constant(term: Term): ExpressionIndexed =
    fromTerm(Abs("mem", cl2T, term))
}

class ExpressionNonindexed(term: RichTerm) extends Expression(term) {
  def renameCVariablesCQ(renaming: List[(Variable with Nonindexed, Variable with Nonindexed)]): ExpressionNonindexed =
    renameCVariables(renaming collect { case (a:CVariable, b:CVariable) => (a,b) })

  override def renameCVariables(renaming: List[(CVariable, CVariable)]): ExpressionNonindexed =
    super.renameCVariables(renaming).castNonindexed

  override def castNonindexed: this.type = this

  override def simplify(context: ContextX, facts: List[String], thms: ListBuffer[Thm]): ExpressionNonindexed =
    super.simplify(context, facts, thms).castNonindexed

  override def checkWelltyped(context: ContextX): Unit = {
    super.checkWelltyped(context)
    assert(memTyp == clT)
  }

  def instantiateMemory = new ExpressionInstantiatedNonindexed(term.longformInstantiate(indexed = false))

  def variables(ctxt: Context, environment: Environment): ExprVariableUse =
    instantiateMemory.variables(ctxt, environment)

  def index(ctxt: Context, side: Index12): ExpressionIndexed = {
    val fstSnd = side match {
      case Variable.Index1 => globalIsabelle.fst(cl2T, cl2T)
      case Variable.Index2 => globalIsabelle.snd(cl2T, cl2T)
    }
    ExpressionIndexed.fromTerm(
      Abs("mem", cl2T, term.isabelleTerm $ (fstSnd $ Bound(0))))
      .clean(ctxt)
  }

  override def clean(ctxt: Context): ExpressionNonindexed = clean(ctxt).castNonindexed
}

object ExpressionNonindexed {
  def constant(term: Term): ExpressionNonindexed =
    fromTerm(Abs("mem", clT, term))

  def fromTerm(term: Term) = new ExpressionNonindexed(RichTerm(term))
  def fromTerm(term: RichTerm) = new ExpressionNonindexed(term)

  /** Parses an indexed expression in longform */
  def fromString(context: Context, string: String, rangeTyp: Typ): ExpressionNonindexed =
    Expression.fromString(context, string, rangeTyp, indexed = false).castNonindexed
}
