package qrhl.toplevel

import info.hupel.isabelle.Operation.ProverException
import info.hupel.isabelle.hol.HOLogic
import org.scalatest.FunSuite
import qrhl.UserException
import qrhl.logic.Call

class ParserTest extends FunSuite {
  implicit lazy val parserContext: ParserContext = {
    val tl = Toplevel.makeToplevel()
    // If this fails for parsing reasons, just directly compose commands instead
    tl.execCmd("classical var x : int")
    tl.execCmd("classical var y : int")
    tl.execCmd("adversary A0 vars x")
    tl.execCmd("adversary B0 vars x")
    tl.execCmd("adversary A1 vars x calls ?")
    tl.execCmd("adversary A2 vars x calls ?, ?")
    tl.state.parserContext
  }

  test("parse while loop") {
    val whileLoop = Parser.parseAll(Parser.whileLoop, "while (True) { skip; };")
  }

  test("parse undeclared variable") {
    assertThrows[UserException] {
      Parser.parseAll(Parser.expression(HOLogic.boolT), "hello")
    }
  }

  test("fail to parse while loop") {
    assertThrows[ProverException] {
      val whileLoop = Parser.parseAll(Parser.whileLoop, "while (1) { skip; };")
    }
  }

  test("adversary") {
    val decl = Parser.parseAll(Parser.declareAdversary, "adversary A vars x, y").get
    assert(decl.name=="A")
    assert(decl.cvars.map(_.name)==List("x","y"))
    assert(decl.qvars.isEmpty)
    assert(decl.numOracles==0)
  }

  test("adversary calls") {
    val decl = Parser.parseAll(Parser.declareAdversary, "adversary A vars x, y calls ?, ?").get
    assert(decl.name=="A")
    assert(decl.cvars.map(_.name)==List("x","y"))
    assert(decl.qvars.isEmpty)
    assert(decl.numOracles==2)
  }

  test("call") {
    val call = Parser.parseAll(Parser.call, "call A0;").get
    assert(call==Call("A0"))
  }

  test("call 1 arg") {
    val call = Parser.parseAll(Parser.call, "call A1(A0);").get
    assert(call==Call("A1",Call("A0")))
  }

  test("call 2 arg") {
    val call = Parser.parseAll(Parser.call, "call A2(A0,B0);").get
    assert(call==Call("A2",Call("A0"),Call("B0")))
  }

  test("call 2 nested") {
    val call = Parser.parseAll(Parser.call, "call A2(A1(B0),A0);").get
    assert(call==Call("A2",Call("A1",Call("B0")),Call("A0")))
  }

  test("call wrong num args") {
    assertThrows[UserException] {
      val call = Parser.parseAll(Parser.call, "call A1").get
      print(call)
    }
  }
}
