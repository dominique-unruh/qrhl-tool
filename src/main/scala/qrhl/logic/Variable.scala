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
  def isabelleTyp : pure.Typ
  def typ : Typ
  def isabelleTerm: Term = Free(name,isabelleTyp)
  def isabelleTerm_var: Term = Free(name+"_var",Isabelle.qvariableT(typ.isabelleTyp))
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

object QVariable {
  def fromTerm_var(context: Isabelle.Context, x: Term): QVariable = x match {
    case Free(name,typ) =>
      assert(name.endsWith("_var"))
      QVariable(name.stripSuffix("_var"), Typ(context, Isabelle.dest_qvariableT(typ)))
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

case class CVariable(name:String, typ: Typ) extends Variable {
  override def index1: CVariable = CVariable(Variable.index1(name),typ)
  override def index2: CVariable = CVariable(Variable.index2(name),typ)
  override def index(left:Boolean): CVariable = if (left) index1 else index2
  override def isabelleTyp: pure.Typ = typ.isabelleTyp


}

object CVariable {
  def fromTerm_var(context: Isabelle.Context, x: Term): CVariable = x match {
    case Free(name,typ) =>
      assert(name.endsWith("_var"))
      CVariable(name.stripSuffix("_var"), Typ(context, Isabelle.dest_qvariableT(typ)))
  }
}
