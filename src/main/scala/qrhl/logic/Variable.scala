package qrhl.logic

import info.hupel.isabelle.pure
import info.hupel.isabelle.pure.{App, Const, Free, Term}
import qrhl.isabelle.Isabelle

// Variables
sealed trait Variable {
  val name:String
  def index1: Variable
  def index2: Variable
  def index(left:Boolean): Variable = if (left) index1 else index2
  def variableTyp: pure.Typ = Isabelle.qvariableT(valueTyp)
  def valueTyp : pure.Typ
  @deprecated("use valueType / variableTyp","") def typ : Typ
  def variableTerm: Term
}

object Variable {
  def index1(name:String) : String = name+"1"
  def index2(name:String) : String = name+"2"
  def index(left:Boolean, name:String) : String =
    if (left) index1(name) else index2(name)
}

final case class QVariable(name:String, typ: Typ) extends Variable {

  override def index1: QVariable = QVariable(Variable.index1(name),typ)
  override def index2: QVariable = QVariable(Variable.index2(name),typ)
  override def index(left:Boolean): QVariable = if (left) index1 else index2

  override def valueTyp: pure.Typ = typ.isabelleTyp
  override def variableTerm: Term = Free(name,variableTyp)
}

object QVariable {
  def fromTerm_var(context: Isabelle.Context, x: Term): QVariable = x match {
    case Free(name,typ) =>
//      assert(name.endsWith("_var"))
      QVariable(name, Typ(context, Isabelle.dest_qvariableT(typ)))
  }

  def fromQVarList(context: Isabelle.Context, qvs: Term): List[QVariable] = qvs match {
    case Const(Isabelle.qvariable_unit.name, _) => Nil
    case App(Const(Isabelle.qvariable_singletonName,_), v) => List(fromTerm_var(context, v))
    case App(App(Const(Isabelle.qvariable_concatName,_), v), vs) =>
      val v2 = fromQVarList(context, v)
      assert(v2.length==1)
      val vs2 = fromQVarList(context, vs)
      v2.head :: vs2
  }
}

final case class CVariable(name:String, typ: Typ) extends Variable {
  override def index1: CVariable = CVariable(Variable.index1(name),typ)
  override def index2: CVariable = CVariable(Variable.index2(name),typ)
  override def index(left:Boolean): CVariable = if (left) index1 else index2
  override def valueTyp: pure.Typ = typ.isabelleTyp
  override def variableTerm: Term = Free(name+"_var",variableTyp)
  def valueTerm: Term = Free(name,valueTyp)
}

object CVariable {
  def fromTerm_var(context: Isabelle.Context, x: Term): CVariable = x match {
    case Free(name,typ) =>
      assert(name.endsWith("_var"))
      CVariable(name.stripSuffix("_var"), Typ(context, Isabelle.dest_qvariableT(typ)))
  }
}
