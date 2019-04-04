package qrhl.logic

import org.scalatest.FunSuite

class VariableTest extends FunSuite {
  test("vartermToString, nested tuples") {
    val vt = VTCons(VTCons(VTSingle("a"),VTSingle("b")),VTCons(VTSingle("c"),VTSingle("d")))
    val str = Variable.vartermToString[String](identity, vt)
    assert(str == "(a,b),c,d")
  }
}
