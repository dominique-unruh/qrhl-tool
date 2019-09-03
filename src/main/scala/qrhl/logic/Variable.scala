package qrhl.logic

import info.hupel.isabelle.pure
import info.hupel.isabelle.pure.{App, Const, Free, Term}
import qrhl.isabelle.{Isabelle, IsabelleConsts}

// Variables
sealed trait Variable {
  val name:String
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
}

final case class QVariable(name:String, override val valueTyp: pure.Typ) extends Variable {

  override def index1: QVariable = QVariable(Variable.index1(name),valueTyp)
  override def index2: QVariable = QVariable(Variable.index2(name),valueTyp)
  override def index(left:Boolean): QVariable = if (left) index1 else index2
  override val variableName: String = name
  override def toString: String = s"quantum var $name : ${Isabelle.pretty(valueTyp)}"
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
}

final case class CVariable(name:String, override val valueTyp: pure.Typ) extends Variable {
  override def index1: CVariable = CVariable(Variable.index1(name),valueTyp)
  override def index2: CVariable = CVariable(Variable.index2(name),valueTyp)
  override def index(left:Boolean): CVariable = if (left) index1 else index2
//  override def valueTyp: pure.Typ = typ.isabelleTyp
  override val variableName : String= "var_"+name
  def valueTerm: Term = Free(name,valueTyp)

  override def toString: String = s"classical var $name : ${Isabelle.pretty(valueTyp)}"
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
}
