package qrhl.logic

import info.hupel.isabelle.api.XML
import info.hupel.isabelle.{Codec, XMLResult, pure}
import info.hupel.isabelle.pure.{App, Const, Free, Term}
import qrhl.isabelle.RichTerm.typ_tight_codec
import qrhl.isabelle.{Isabelle, IsabelleConsts}

import scala.collection.generic.CanBuildFrom
import scala.collection.immutable.ListSet
import scala.collection.mutable

// Variables
sealed trait Variable {
  def rename(name: String): Variable

  def isClassical: Boolean
  def isQuantum: Boolean

  val name:String
  /** Name of the variable on Isabelle side (prefixed with var_ for classical variables) */
  val variableName: String
  def index1: Variable
  def index2: Variable
  def index(left:Boolean): Variable = if (left) index1 else index2
  def variableTyp: pure.Typ = Isabelle.variableT(valueTyp)
  def valueTyp : pure.Typ
//  @deprecated("use valueType / variableTyp","") def typ : Typ
  def variableTerm: Term = Free(variableName,variableTyp)
}

object Variable {
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
    def unapply(variable: Variable): Option[(Variable, Boolean)] = variable.name match {
      case Indexed(name, left) => Some(variable.rename(name), left)
      case _ => None
    }
  }

  object IndexedC {
    def unapply(v: CVariable): Option[(CVariable, Boolean)] = {
      if (v.name.isEmpty) return None
      def basename = v.name.substring(0, v.name.length-1)

      v.name.last match {
        case '1' => Some((CVariable(basename, v.valueTyp), true))
        case '2' => Some((CVariable(basename, v.valueTyp), false))
        case _ => None
      }
    }
  }

  def varsToString(vars: Traversable[Variable]): String =
    if (vars.isEmpty) "∅" else
      vars.map(_.name).mkString(", ")
}

final case class QVariable(name:String, override val valueTyp: pure.Typ) extends Variable {

  override def index1: QVariable = QVariable(Variable.index1(name),valueTyp)
  override def index2: QVariable = QVariable(Variable.index2(name),valueTyp)
  override def index(left:Boolean): QVariable = if (left) index1 else index2
  override val variableName: String = name
  override def toString: String = s"quantum var $name : ${Isabelle.pretty(valueTyp)}"

  override def isQuantum: Boolean = true
  override def isClassical: Boolean = false

  override def rename(name: String): Variable = copy(name=name)
}

object QVariable {
  def fromTerm_var(context: Isabelle.Context, x: Term): QVariable = x match {
    case Free(name,typ) =>
      QVariable(name, Isabelle.dest_variableT(typ))
    case _ => throw new java.lang.RuntimeException(f"Cannot transform $x into QVariable")
  }

  def fromQVarList(context: Isabelle.Context, qvs: Term): List[QVariable] = qvs match {
    case Const(Isabelle.variable_unit.name, _) => Nil
    case App(Const(IsabelleConsts.variable_singleton,_), v) => List(fromTerm_var(context, v))
    case App(App(Const(IsabelleConsts.variable_concat,_), v), vs) =>
      val v2 = fromQVarList(context, v)
      assert(v2.length==1)
      val vs2 = fromQVarList(context, vs)
      v2.head :: vs2
    case _ => throw new RuntimeException("Illformed variable list")
  }

  object codec extends Codec[QVariable] {
    override val mlType: String = "(string * typ)"
    override def encode(v: QVariable): XML.Tree = XML.Elem(("V",List(("name",v.name))), List(typ_tight_codec.encode(v.valueTyp)))
    override def decode(tree: XML.Tree): XMLResult[QVariable] = tree match {
      case XML.Elem(("V",List(("name",name))), List(typXml)) =>
        for (typ <- typ_tight_codec.decode(typXml))
          yield QVariable(name,typ)
    }
  }



}

final case class CVariable(name:String, override val valueTyp: pure.Typ) extends Variable {
  override def index1: CVariable = CVariable(Variable.index1(name),valueTyp)
  override def index2: CVariable = CVariable(Variable.index2(name),valueTyp)
  override def index(left:Boolean): CVariable = if (left) index1 else index2
//  override def valueTyp: pure.Typ = typ.isabelleTyp
  override val variableName : String= "var_"+name
  def valueTerm: Term = Free(name,valueTyp)

  override def toString: String = s"classical var $name : ${Isabelle.pretty(valueTyp)}"

  override def isQuantum: Boolean = false
  override def isClassical: Boolean = true

  override def rename(name: String): Variable = copy(name=name)
}

object CVariable {
  def fromTerm_var(context: Isabelle.Context, x: Term): CVariable = x match {
    case Free(name,typ) =>
      assert(name.startsWith("var_"))
      CVariable(name.stripPrefix("var_"), Isabelle.dest_variableT(typ))
    case _ => throw new RuntimeException("Illformed variable term")
  }

  def fromCVarList(context: Isabelle.Context, cvs: Term): List[CVariable] = cvs match {
    case Const(Isabelle.variable_unit.name, _) => Nil
    case App(Const(IsabelleConsts.variable_singleton,_), v) => List(fromTerm_var(context, v))
    case App(App(Const(IsabelleConsts.variable_concat,_), v), vs) =>
      val v2 = fromCVarList(context, v)
      assert(v2.length==1)
      val vs2 = fromCVarList(context, vs)
      v2.head :: vs2
    case _ => throw new RuntimeException("Illformed variable list")
  }

  object codec extends Codec[CVariable] {
    override val mlType: String = "(string * typ)"
    override def encode(v: CVariable): XML.Tree = XML.Elem(("V",List(("name",v.name))), List(typ_tight_codec.encode(v.valueTyp)))
    override def decode(tree: XML.Tree): XMLResult[CVariable] = tree match {
      case XML.Elem(("V",List(("name",name))), List(typXml)) =>
        for (typ <- typ_tight_codec.decode(typXml))
          yield CVariable(name,typ)
    }
  }

}
