package qrhl.logic

import qrhl.isabellex.{IsabelleConsts, IsabelleX}
import IsabelleX.{globalIsabelle => GIsabelle}
import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.MLValue.Converter
import de.unruh.isabelle.mlvalue.{MLValue, MLValueConverter}
import de.unruh.isabelle.pure.{App, Bound, Const, Free, Term, Typ}
import hashedcomputation.{Hash, HashTag, Hashable, HashedValue, RawHash}
import qrhl.logic.Variable.{Index1, Index2, NoIndex}
import qrhl.AllSet
import GIsabelle.Ops.qrhl_ops
import GIsabelle.Ops
import qrhl.isabellex.IsabelleX.globalIsabelle.{cl2T, clT, isabelleControl}

import scala.collection.immutable.ListSet
import scala.concurrent.{ExecutionContext, Future}

// Implicits
import hashedcomputation.Implicits._
import qrhl.isabellex.Implicits._
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._
import qrhl.isabellex.MLValueConverters.Implicits._

// Variables
sealed trait Variable extends HashedValue {
  def unindex: Variable

  //  def rename(name: String): Variable

  /** Renames this variable.
   * @param renaming - the substitution as an association list. Must not contain pairs (x,x), nor two pairs (x,y), (x,y'). */
  def substitute(renaming: List[(Variable, Variable)]): Variable =
    renaming.find { case (x,y) => x==this }match {
      case None => this
      case Some((x,y)) => y
    }

  def isClassical: Boolean
  @inline final def isQuantum: Boolean = !isClassical
  def isIndexed: Boolean = theIndex != NoIndex

  def name: String = theIndex match {
    case Variable.NoIndex => basename
    case Variable.Index1 => basename + "1"
    case Variable.Index2 => basename + "2"
  }

  // Without the 1/2 suffix for indexed variables
  val basename:String
  @deprecated("same as name") val variableName: String = name
  def index1: Variable
  def index2: Variable
  val theIndex: Variable.Index
  final def index(left:Boolean): Variable = {
    assert(!isIndexed)
    if (left) index1 else index2
  }
  def variableTyp: Typ = GIsabelle.variableT(valueTyp, classical=isClassical, indexed=isIndexed)
  def valueTyp : Typ

  /** term describing the variable in short form.
   * For non-indexed variables, short form is just the variable.
   * For indexed variables, short form would be e.g. Free(x2,typ), and long form "qregister_chain qFst (Free(x2,typ))".
   *
   * For classical variables, the type of the shortform is the valueType, for quantum variables, it is the type of the variable.
   *
   * */
  def variableTermShort: Term =
    Free(name, if (isClassical) valueTyp else variableTyp)

  def variableTermLong: Term =
    if (isIndexed)
      Ops.varterm_to_variable2(isClassical, VTSingle(name, theIndex, valueTyp)).retrieveNow
    else
      Ops.varterm_to_variable1(isClassical, VTSingle(name, theIndex, valueTyp)).retrieveNow

  def classicalQuantumWord : String
}

object Variable {
  implicit object ordering extends Ordering[Variable] {
    // Implicits
    import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl
    import scala.concurrent.ExecutionContext.Implicits.global

    def compareSame(x: Variable, y:Variable): Int = {
      val nameComp = Ordering.String.compare(x.name, y.name)
      if (nameComp==0)
        GIsabelle.Ops.compareTyps(x.valueTyp, y.valueTyp).retrieveNow
      else
        nameComp
    }
    override def compare(x: Variable, y: Variable): Int = (x,y) match {
      case (_ : QVariable, _ : CVariable) => +1
      case (_ : CVariable, _ : QVariable) => -1
      case _ => compareSame(x,y)
    }
  }

  def quantum(vars: ListSet[Variable]): ListSet[QVariable] = vars collect { case v : QVariable => v }
  def quantum(vars: Traversable[Variable]): Traversable[QVariable] = vars collect { case v : QVariable => v }
  def quantum(vars: Set[Variable]): Set[QVariable] = vars collect { case v : QVariable => v }
  def classical(vars: ListSet[Variable]): ListSet[CVariable] = vars collect { case v : CVariable => v }
  def classical(vars: Traversable[Variable]): Traversable[CVariable] = vars collect { case v : CVariable => v }
  def classical(vars: Set[Variable]): Set[CVariable] = vars collect { case v : CVariable => v }

  //  def varlistToString(vars: List[Variable]) = vars match {
//    case Nil => "()"
//    case List(x) => x.name;
//    case _ => s"(${vars.mkString(",")})"
//  }

  def vartermToString[A](toStr:A=>String, vars: VarTerm[A]): String = vars match {
    case VTUnit => "()"
    case VTSingle(x) => toStr(x)
    case VTCons(VTSingle(x),xs) => toStr(x) + "," + vartermToString(toStr,xs)
    case VTCons(VTUnit,xs) => "()," + vartermToString(toStr,xs)
    case VTCons(a,b) => s"(${vartermToString(toStr,a)}),${vartermToString(toStr,b)}"
  }

  def vartermToString(vars: VarTerm[Variable]): String = vartermToString[Variable](_.name, vars)
  /*def vartermToString(vars: VarTerm[Variable]): String = vars match {
    case VTUnit => "()"
    case VTSingle(x) => x.name
    case VTCons(VTSingle(x),xs) => x.name + "," + vartermToString(xs)
    case VTCons(VTUnit,xs) => "()," + vartermToString(xs)
    case VTCons(a,b) => s"(${vartermToString(a)},${vartermToString(b)})"
  }*/

  def index1(name:String) : String = name+"1"
  def index2(name:String) : String = name+"2"
  def index(left:Boolean, name:String) : String =
    if (left) index1(name) else index2(name)

/*
  class Indexed(left: Boolean) {
    def unapply(variable: Variable) : Option[Variable] = variable match {
      case Indexed(var2, `left`) => Some(var2)
      case _ => None
    }
  }
*/

  object Indexed {
    def unapply(name: String): Option[(String, Boolean)] = {
      if (name.isEmpty) return None
      def basename = name.substring(0, name.length-1)

      name.last match {
        case '1' => Some((basename, true))
        case '2' => Some((basename, false))
        case _ => None
      }
    }
    def unapply(variable: Variable): Option[(Variable, Boolean)] = {
      if (variable.isIndexed) Some(variable.unindex, variable.theIndex==Index1)
      else None
    }
  }

  object IndexedC {
    def unapply(v: CVariable): Option[(CVariable, Boolean)] = {
      if (v.isIndexed) Some((v.unindex, v.theIndex==Index1))
      else None
    }
  }

  def varsNamesToString(vars: Iterable[String]): String =
    if (vars.isEmpty) "∅" else
      vars.mkString(", ")

  def varsToString(vars: Iterable[Variable]): String = vars match {
    case _ : AllSet[_] => "all variables"
    case _ => varsNamesToString(vars.map(_.name))
  }

  sealed trait Index
  final case object NoIndex extends Index
  final case object Index1 extends Index
  final case object Index2 extends Index

  implicit object IndexConverter extends Converter[Index] {
    private val isabelleControl = null // Hide global implicit
    override def mlType(implicit isabelle: Isabelle): String = s"$qrhl_ops.index"

    override def retrieve(value: MLValue[Index])(implicit isabelle: Isabelle): Future[Index] = {
      implicit val ec: ExecutionContext = isabelle.executionContext
      GIsabelle.Ops.retrieveIndex(value).retrieve.map {
        case 0 => NoIndex
        case 1 => Index1
        case 2 => Index2
      }
    }

    override def store(value: Index)(implicit isabelle: Isabelle): MLValue[Index] = {
      implicit val ec: ExecutionContext = isabelle.executionContext
      val int = value match {
        case NoIndex => 0
        case Index1 => 1
        case Index2 => 2
      }
      GIsabelle.Ops.storeIndex(int)
    }

    override def exnToValue(implicit isabelle: Isabelle): String = s"fn E_Int 0 => $qrhl_ops.NoIndex | E_Int 1 => $qrhl_ops.Index1 | E_Int 2 => $qrhl_ops.Index2"

    override def valueToExn(implicit isabelle: Isabelle): String = s"fn $qrhl_ops.NoIndex => E_Int 0 | $qrhl_ops.Index1 => E_Int 1 | $qrhl_ops.Index2 => E_Int 2"
  }
}

final class QVariable private (override val basename:String, override val valueTyp: Typ, val theIndex: Variable.Index) extends Variable {
  override val hash: Hash[QVariable.this.type] =
    HashTag()(RawHash.hashString(name), Hashable.hash(valueTyp))

  override def index1: QVariable = { assert(theIndex==NoIndex); new QVariable(basename, valueTyp, Index1) }
  override def index2: QVariable = { assert(theIndex==NoIndex); new QVariable(basename, valueTyp, Index2) }
  override def toString: String = s"quantum var $name : ${IsabelleX.pretty(valueTyp)}"
  override def unindex: QVariable = { assert(isIndexed); new QVariable(basename, valueTyp, NoIndex) }

//  override def isQuantum: Boolean = true
  override def isClassical: Boolean = false

//  override def rename(name: String): Variable = copy(name=name)

  override def classicalQuantumWord: String = "quantum"

  override def substitute(renaming: List[(Variable, Variable)]): QVariable =
    super.substitute(renaming).asInstanceOf[QVariable]

  override def equals(obj: Any): Boolean = obj match {
    case q : QVariable => basename == q.basename && valueTyp == q.valueTyp && theIndex == q.theIndex
    case _ => false
  }
}

object QVariable {
  def fromName(name: String, typ: Typ, index: Variable.Index = NoIndex): QVariable = {
    assert(name.nonEmpty)
    new QVariable(name, typ, index)
  }

  def fromIndexedName(name: String, typ: Typ): QVariable = {
    assert(name.nonEmpty)
    if (name.last == '1') new QVariable(name.dropRight(1), typ, Index1)
    else if (name.last == '2') new QVariable(name.dropRight(1), typ, Index2)
    else new QVariable(name, typ, NoIndex)
  }

  implicit object ordering extends Ordering[QVariable] {
    override def compare(x: QVariable, y: QVariable): Int =
      Variable.ordering.compareSame(x,y)
  }

/*  def fromTerm_var(context: IsabelleX.ContextX, x: Term): QVariable = x match {
    case Free(name,typ) =>
      QVar
      iable(name, GIsabelle.dest_variableT(typ))
    case _ => throw new java.lang.RuntimeException(f"Cannot transform $x into QVariable")
  }

  def fromQVarList(context: IsabelleX.ContextX, qvs: Term): List[QVariable] = qvs match {
    case Const(GIsabelle.variable_unit.name, _) => Nil
    case App(Const(IsabelleConsts.variable_singleton,_), v) => List(fromTerm_var(context, v))
    case App(App(Const(IsabelleConsts.variable_concat,_), v), vs) =>
      val v2 = fromQVarList(context, v)
      assert(v2.length==1)
      val vs2 = fromQVarList(context, vs)
      v2.head :: vs2
    case _ => throw new RuntimeException("Illformed variable list")
  }*/




}

final class CVariable private (override val basename:String, override val valueTyp: Typ, override val theIndex: Variable.Index) extends Variable {
  def getter(memory: Typ => Term): Term = {
    val memT = if (isIndexed) cl2T else clT
    GIsabelle.getter(valueTyp, indexed=isIndexed) $ variableTermLong $ memory(memT)
  }
  def getter(memory: Term): Term = getter({_ => memory})
  def getter: Term = getter(Bound(0))

  override val hash: Hash[CVariable.this.type] =
    HashTag()(RawHash.hashString(name), Hashable.hash(valueTyp))

  override def index1: CVariable = { assert(theIndex==NoIndex); new CVariable(basename, valueTyp, Index1) }
  override def index2: CVariable = { assert(theIndex==NoIndex); new CVariable(basename, valueTyp, Index2) }

  override def toString: String = s"classical var $name : ${IsabelleX.pretty(valueTyp)}"
  override def unindex: CVariable = { assert(isIndexed); new CVariable(basename, valueTyp, NoIndex) }

//  def valueTerm(implicit isa: de.unruh.isabelle.control.Isabelle, ec: ExecutionContext): Term = Free(name, valueTyp)

//  override def isQuantum: Boolean = false
  override def isClassical: Boolean = true

//  override def rename(name: String): Variable = copy(name=name)

  override def classicalQuantumWord: String = "classical"

  override def substitute(renaming: List[(Variable, Variable)]): CVariable =
    super.substitute(renaming).asInstanceOf[CVariable]

  override def equals(obj: Any): Boolean = obj match {
    case c : CVariable => basename == c.basename && valueTyp == c.valueTyp && theIndex == c.theIndex
    case _ => false
  }
}

object CVariable {
  def fromName(name: String, typ: Typ, index: Variable.Index = NoIndex): CVariable = {
    assert(name.nonEmpty)
//    val last = name.last
//    assert(last != '1')
//    assert(last != '2')
    new CVariable(name, typ, index)
  }

  def fromIndexedName(name: String, typ: Typ): CVariable = {
    assert(name.nonEmpty)
    if (name.last == '1') new CVariable(name.dropRight(1), typ, Index1)
    else if (name.last == '2') new CVariable(name.dropRight(1), typ, Index2)
    else new CVariable(name, typ, NoIndex)
  }

  implicit object ordering extends Ordering[CVariable] {
    override def compare(x: CVariable, y: CVariable): Int =
      Variable.ordering.compareSame(x,y)
  }

/*  def fromTerm_var(context: IsabelleX.ContextX, x: Term): CVariable = x match {
    case Free(name,typ) =>
      assert(name.startsWith("var_"))
      CVariable(name.stripPrefix("var_"), GIsabelle.dest_variableT(typ))
    case _ => throw new RuntimeException("Illformed variable term")
  }

  def fromCVarList(context: IsabelleX.ContextX, cvs: Term): List[CVariable] = cvs match {
    case Const(GIsabelle.variable_unit.name, _) => Nil
    case App(Const(IsabelleConsts.variable_singleton,_), v) => List(fromTerm_var(context, v))
    case App(App(Const(IsabelleConsts.variable_concat,_), v), vs) =>
      val v2 = fromCVarList(context, v)
      assert(v2.length==1)
      val vs2 = fromCVarList(context, vs)
      v2.head :: vs2
    case _ => throw new RuntimeException("Illformed variable list")
  }*/
}


