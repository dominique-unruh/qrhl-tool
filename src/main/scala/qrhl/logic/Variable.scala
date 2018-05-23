package qrhl.logic

import info.hupel.isabelle.pure
import info.hupel.isabelle.pure.{Free, Term}

// Variables
sealed trait Variable {
  val name:String
  def index1: Variable
  def index2: Variable
  def index(left:Boolean): Variable = if (left) index1 else index2
  def isabelleTyp : pure.Typ
  def isabelleTerm: Term = Free(name,isabelleTyp)
  def isabelleTerm_var: Term = Free(name+"_var",isabelleTyp)
}
object Variable {
  def index1(name:String) : String = name+"1"
  def index2(name:String) : String = name+"2"
  def index(left:Boolean, name:String) : String =
    if (left) index1(name) else index2(name)
}
case class QVariable(name:String, typ: Typ) extends Variable {

  override def index1: QVariable = QVariable(Variable.index1(name),typ)
  override def index2: QVariable = QVariable(Variable.index2(name),typ)
  override def index(left:Boolean): QVariable = if (left) index1 else index2

  override def isabelleTyp: pure.Typ = pure.Type("QRHL_Core.qvariable",List(typ.isabelleTyp))
}
case class CVariable(name:String, typ: Typ) extends Variable {
  override def index1: CVariable = CVariable(Variable.index1(name),typ)
  override def index2: CVariable = CVariable(Variable.index2(name),typ)
  override def index(left:Boolean): CVariable = if (left) index1 else index2
  override def isabelleTyp: pure.Typ = typ.isabelleTyp


}
