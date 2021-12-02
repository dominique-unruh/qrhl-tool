package qrhl.logic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.isabellex.IsabelleX.globalIsabelle
import qrhl.isabellex.IsabelleX.globalIsabelle.{intT, natT}

class VariableTest extends AnyFunSuite {
  test("vartermToString, nested tuples") {
    val vt = VTCons(VTCons(VTSingle("a"),VTSingle("b")),VTCons(VTSingle("c"),VTSingle("d")))
    val str = Variable.vartermToString[String](identity, vt)
    assert(str == "(a,b),c,d")
  }

  test("equality tests") {
    assert(CVariable.fromName("x", intT) == CVariable.fromName("x", intT))
    assert(CVariable.fromName("y", intT) != CVariable.fromName("x", intT))
    assert(CVariable.fromName("x", intT) != CVariable.fromName("x", natT))
    assert(QVariable.fromName("x", intT) != CVariable.fromName("x", intT))
    assert(CVariable.fromName("x", intT) != QVariable.fromName("x", intT))
  }
}
