package qrhl.logic

// Variables
sealed trait Variable {
  val name:String
  def index1: Variable
  def index2: Variable
  def index(left:Boolean): Variable = if (left) index1 else index2
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
}
case class CVariable(name:String, typ: Typ) extends Variable {
  override def index1: CVariable = CVariable(Variable.index1(name),typ)
  override def index2: CVariable = CVariable(Variable.index2(name),typ)
  override def index(left:Boolean): CVariable = if (left) index1 else index2
}
