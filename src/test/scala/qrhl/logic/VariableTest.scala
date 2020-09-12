package qrhl.logic

import org.scalatest.funsuite.AnyFunSuite

class VariableTest extends AnyFunSuite {
  test("vartermToString, nested tuples") {
    val vt = VTCons(VTCons(VTSingle("a"),VTSingle("b")),VTCons(VTSingle("c"),VTSingle("d")))
    val str = Variable.vartermToString[String](identity, vt)
    assert(str == "(a,b),c,d")
  }
}
