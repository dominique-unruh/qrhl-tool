package qrhl.logic

import qrhl.isabellex.{IsabelleConsts, IsabelleX}
import IsabelleX.{globalIsabelle => GIsabelle}
import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.MLValue.Converter
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.{Bound, Const, Free, Term, Typ}
import hashedcomputation.{Hash, HashTag, Hashable, HashedValue, RawHash}
import qrhl.logic.Variable.{Index1, Index12, Index2, NoIndex}
import qrhl.AllSet
import GIsabelle.Ops.qrhl_ops
import GIsabelle.Ops
import de.unruh.isabelle.control.Isabelle.DInt
import qrhl.isabellex.IsabelleX.globalIsabelle.{cl2T, clT, qu2T, quT, RegisterChain}

import scala.collection.immutable.ListSet
import scala.concurrent.{ExecutionContext, Future}

// Implicits
import hashedcomputation.Implicits._
import qrhl.isabellex.Implicits._
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._
import qrhl.isabellex.MLValueConverters.Implicits._
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl

trait Indexed
trait Nonindexed

// Variables
sealed trait Variable extends HashedValue {
  def castNonindexed: Variable with Nonindexed
  def castIndexed: Variable with Indexed
  /** Typesafe cast */
  def castNonindexedSafe(implicit ev: this.type <:< Nonindexed): Variable with Nonindexed
  /** Typesafe cast */
  def castIndexedSafe(implicit ev: this.type <:< Indexed): Variable with Indexed

  def unindex: Variable with Nonindexed

  def memTyp: Typ

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
  def index1: Variable with Indexed
  def index2: Variable with Indexed
  val theIndex: Variable.Index
  def index(side:Index12): Variable with Indexed = {
    assert(!isIndexed)
    side match {
      case Variable.Index1 => index1
      case Variable.Index2 => index2
    }
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
  def quantumNI(vars: ListSet[Variable with Nonindexed]): ListSet[QVariableNI] = vars collect { case v : QVariable => v.castNonindexedSafe }
  def quantumI(vars: ListSet[Variable with Indexed]): ListSet[QVariableI] = vars collect { case v : QVariable => v.castIndexedSafe }
  def quantum(vars: Iterable[Variable]): Iterable[QVariable] = vars collect { case v : QVariable => v }
  def quantumNI(vars: Iterable[Variable with Nonindexed]): Iterable[QVariableNI] = vars collect { case v : QVariable => v.castNonindexedSafe }
  def quantumNI(vars: List[Variable with Nonindexed]): List[QVariableNI] = vars collect { case v : QVariable => v.castNonindexedSafe }
  def quantum(vars: Set[Variable]): Set[QVariable] = vars collect { case v : QVariable => v }
  def classical(vars: ListSet[Variable]): ListSet[CVariable] = vars collect { case v : CVariable => v }
  def classicalNI(vars: ListSet[Variable with Nonindexed]): ListSet[CVariableNI] = vars collect { case v : CVariable => v.castNonindexedSafe }
  def classicalI(vars: ListSet[Variable with Indexed]): ListSet[CVariableI] = vars collect { case v : CVariable => v.castIndexedSafe }
  def classical(vars: Iterable[Variable]): Iterable[CVariable] = vars collect { case v : CVariable => v }
  def classicalNI(vars: Iterable[Variable with Nonindexed]): Iterable[CVariableNI] = vars collect { case v : CVariable => v.castNonindexedSafe }
  def classicalNI(vars: List[Variable with Nonindexed]): Iterable[CVariableNI] = vars collect { case v : CVariable => v.castNonindexedSafe }
  def classical(vars: Set[Variable]): Set[CVariable] = vars collect { case v : CVariable => v }

  def vartermToString[A](toStr:A=>String, vars: VarTerm[A]): String = vars match {
    case VTUnit => "()"
    case VTSingle(x) => toStr(x)
    case VTCons(VTSingle(x),xs) => toStr(x) + "," + vartermToString(toStr,xs)
    case VTCons(VTUnit,xs) => "()," + vartermToString(toStr,xs)
    case VTCons(a,b) => s"(${vartermToString(toStr,a)}),${vartermToString(toStr,b)}"
  }

  def vartermToString(vars: VarTerm[Variable]): String = vartermToString[Variable](_.name, vars)

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
    /*def unapply(name: String): Option[(String, Index12)] = {
      if (name.isEmpty) return None
      def basename = name.substring(0, name.length-1)

      name.last match {
        case '1' => Some((basename, Index1))
        case '2' => Some((basename, Index2))
        case _ => None
      }
    }*/
    def unapply(variable: Variable): Option[(Variable, Index12)] = {
      if (variable.isIndexed) Some(variable.unindex, variable.theIndex.asInstanceOf[Index12])
      else None
    }
    def unapply(term: Term): Option[(Term, Index12)] = term match {
      case RegisterChain(fstSnd, v) =>
        fstSnd match {
          case Const(IsabelleConsts.qFst, _) => Some((v,Index1))
          case Const(IsabelleConsts.cFst, _) => Some((v,Index1))
          case Const(IsabelleConsts.qSnd, _) => Some((v,Index2))
          case Const(IsabelleConsts.cSnd, _) => Some((v,Index2))
          case _ => None
        }
      case _ => None
    }
  }

  object IndexedC {
    def unapply(v: CVariable): Option[(CVariable, Index12)] = {
      if (v.isIndexed) Some((v.unindex, v.theIndex.asInstanceOf[Index12]))
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

  sealed trait Index extends HashedValue
  sealed trait Index12 extends Index {
    def choose[A](left: A, right: A): A
    val leftright: String
  }

  sealed trait QC
  case object Classical extends QC
  case object Quantum extends QC

  implicit object CQConverter extends Converter[QC] {
    private val isabelleControl: Null = null // Hide global implicit

    override def mlType(implicit isabelle: Isabelle): String = s"$qrhl_ops.qc"

    override def retrieve(value: MLValue[QC])(implicit isabelle: Isabelle): Future[QC] = {
      implicit val ec: ExecutionContext = isabelle.executionContext
      GIsabelle.Ops.retrieveQC(value).map {
        case DInt(0) => Classical
        case DInt(1) => Quantum
      }
    }

    override def store(value: QC)(implicit isabelle: Isabelle): MLValue[QC] = {
      implicit val ec: ExecutionContext = isabelle.executionContext
      val int = value match {
        case Classical => 0
        case Quantum => 1
      }
      GIsabelle.Ops.storeQC(DInt(int))
    }

    override def exnToValue(implicit isabelle: Isabelle): String = s"fn $qrhl_ops.E_QC qc => qc"

    override def valueToExn(implicit isabelle: Isabelle): String = s"$qrhl_ops.E_QC"
  }

  final case object NoIndex extends Index {
    override val hash: Hash[NoIndex.this.type] = HashTag()()
  }
  final case object Index1 extends Index12 {
    override val hash: Hash[Index1.this.type] = HashTag()()
    override val leftright: String = "left"
    override def choose[A](left: A, right: A): A = left
  }
  final case object Index2 extends Index12 {
    override def hash: Hash[Index2.this.type] = HashTag()()
    override val leftright: String = "right"
    override def choose[A](left: A, right: A): A = right
  }

  implicit object IndexConverter extends Converter[Index] {
    private val isabelleControl: Null = null // Hide global implicit
    override def mlType(implicit isabelle: Isabelle): String = s"$qrhl_ops.index"

    override def retrieve(value: MLValue[Index])(implicit isabelle: Isabelle): Future[Index] = {
      implicit val ec: ExecutionContext = isabelle.executionContext
      val isabelleControl: Null = null // hide conflicting implicit
      GIsabelle.Ops.retrieveIndex(value).map {
        case DInt(0) => NoIndex
        case DInt(1) => Index1
        case DInt(2) => Index2
      }
    }

    override def store(value: Index)(implicit isabelle: Isabelle): MLValue[Index] = {
      implicit val ec: ExecutionContext = isabelle.executionContext
      val isabelleControl: Null = null // hide conflicting implicit
      val int = value match {
        case NoIndex => 0
        case Index1 => 1
        case Index2 => 2
      }
      GIsabelle.Ops.storeIndex(DInt(int))
    }

    override def exnToValue(implicit isabelle: Isabelle): String = s"fn $qrhl_ops.E_Index idx => idx"

    override def valueToExn(implicit isabelle: Isabelle): String = s"$qrhl_ops.E_Index"
  }
}

sealed class QVariable protected (override val basename:String, override val valueTyp: Typ, val theIndex: Variable.Index) extends Variable {
  override val hash: Hash[QVariable.this.type] =
    HashTag()(RawHash.hashString(name), Hashable.hash(valueTyp))

  override def memTyp: Typ = if (isIndexed) qu2T else quT

  def castNonindexed: QVariableNI = {
    assert(theIndex == NoIndex)
    QVariableNI.fromName(name, valueTyp)
  }

  def castIndexed: QVariableI = {
    assert(theIndex != NoIndex)
    QVariableI.fromName(name, valueTyp, theIndex.asInstanceOf[Index12])
  }

  @inline
  override def castNonindexedSafe(implicit ev: this.type <:< Nonindexed): QVariableNI = asInstanceOf[QVariableNI]
  @inline
  override def castIndexedSafe(implicit ev: this.type <:< Indexed): QVariableI = asInstanceOf[QVariableI]

  override def index1: QVariableI = { assert(theIndex==NoIndex); QVariableI.fromName(basename, valueTyp, Index1) }
  override def index2: QVariableI = { assert(theIndex==NoIndex); QVariableI.fromName(basename, valueTyp, Index2) }
  override def toString: String = s"quantum var $name : ${IsabelleX.pretty(valueTyp)}"
  override def unindex: QVariableNI = { assert(isIndexed); QVariableNI.fromName(basename, valueTyp) }

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
  def fromName(name: String, typ: Typ): QVariableNI = {
    QVariableNI.fromName(name, typ)
  }

  def fromName(name: String, typ: Typ, index: Index12): QVariableI = {
    QVariableI.fromName(name, typ, index)
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

sealed class CVariable protected (override val basename:String, override val valueTyp: Typ, override val theIndex: Variable.Index) extends Variable {
  def getter(memory: Typ => Term): Term = {
    val memT = if (isIndexed) cl2T else clT
    GIsabelle.getter(valueTyp, indexed=isIndexed) $ variableTermLong $ memory(memT)
  }
  def getter(memory: Term): Term = getter({_ => memory})
  def getter: Term = getter(Bound(0))
  def setter(value: Term, mem: Term): Term =
    GIsabelle.setter(valueTyp, indexed=isIndexed) $ variableTermLong $ value $ mem

  override def memTyp: Typ = if (isIndexed) cl2T else clT

  override val hash: Hash[CVariable.this.type] =
    HashTag()(RawHash.hashString(name), Hashable.hash(valueTyp))

  override def index1: CVariableI = { assert(theIndex==NoIndex); CVariableI.fromName(basename, valueTyp, Index1) }
  override def index2: CVariableI = { assert(theIndex==NoIndex); CVariableI.fromName(basename, valueTyp, Index2) }
  override def index(side: Index12): CVariableI = {
    side match {
      case Variable.Index1 => index1
      case Variable.Index2 => index2
    }
  }

  override def toString: String = s"classical var $name : ${IsabelleX.pretty(valueTyp)}"
  override def unindex: CVariableNI = { assert(isIndexed); CVariableNI.fromName(basename, valueTyp) }

//  def valueTerm(implicit isa: de.unruh.isabelle.control.Isabelle, ec: ExecutionContext): Term = Free(name, valueTyp)

//  override def isQuantum: Boolean = false
  override def isClassical: Boolean = true

//  override def rename(name: String): Variable = copy(name=name)

  override def classicalQuantumWord: String = "classical"

  override def substitute(renaming: List[(Variable, Variable)]): CVariable =
    super.substitute(renaming).asInstanceOf[CVariable]

  /** Checked at runtime */
  override def castNonindexed: CVariableNI = {
    assert(theIndex == NoIndex)
    CVariableNI.fromName(name, valueTyp)
  }

  /** Checked at runtime */
  override def castIndexed: CVariableI = {
    assert(theIndex != NoIndex)
    CVariableI.fromName(name, valueTyp, theIndex.asInstanceOf[Index12])
  }

  @inline
  /** Typesafe cast */
  override def castNonindexedSafe(implicit ev: this.type <:< Nonindexed): CVariableNI = asInstanceOf[CVariableNI]
  /** Typesafe cast */
  @inline
  override def castIndexedSafe(implicit ev: this.type <:< Indexed): CVariableI = asInstanceOf[CVariableI]

  override def equals(obj: Any): Boolean = obj match {
    case c : CVariable => basename == c.basename && valueTyp == c.valueTyp && theIndex == c.theIndex
    case _ => false
  }
}


object CVariable {
  def fromName(name: String, typ: Typ): CVariableNI = {
    CVariableNI.fromName(name, typ)
  }

  def fromName(name: String, typ: Typ, index: Variable.Index12): CVariableI = {
    CVariableI.fromName(name, typ, index)
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


final class CVariableNI private (basename:String, valueTyp: Typ) extends CVariable(basename, valueTyp, NoIndex) with Nonindexed {
  override val hash: Hash[this.type] = HashTag()(Hashable.hash(basename), Hashable.hash(valueTyp))
  override def castNonindexed: this.type = this
}
object CVariableNI {
  def fromName(name: String, typ: Typ): CVariableNI = {
    assert(name.nonEmpty)
    new CVariableNI(name, typ)
  }
}
final class CVariableI private (basename:String, valueTyp: Typ, theIndex: Variable.Index12) extends CVariable(basename, valueTyp, theIndex) with Indexed {
  override val hash: Hash[this.type] = HashTag()(Hashable.hash(basename), Hashable.hash(valueTyp))
}
object CVariableI {
  def fromName(name: String, typ: Typ, index: Index12): CVariableI = {
    assert(name.nonEmpty)
    new CVariableI(name, typ, index)
  }
}
final class QVariableNI private (basename:String, valueTyp: Typ) extends QVariable(basename, valueTyp, NoIndex) with Nonindexed {
  override val hash: Hash[this.type] = HashTag()(Hashable.hash(basename), Hashable.hash(valueTyp))
}
object QVariableNI {
  def fromName(name: String, typ: Typ): QVariableNI = {
    assert(name.nonEmpty)
    new QVariableNI(name, typ)
  }
}
final class QVariableI private (basename:String, valueTyp: Typ, theIndex: Variable.Index12) extends QVariable(basename, valueTyp, theIndex) with Indexed {
  override val hash: Hash[this.type] = HashTag()(Hashable.hash(basename), Hashable.hash(valueTyp))
}
object QVariableI {
  def fromName(name: String, typ: Typ, index: Index12): QVariableI = {
    assert(name.nonEmpty)
    new QVariableI(name, typ, index)
  }
}

