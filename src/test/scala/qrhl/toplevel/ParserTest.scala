package qrhl.toplevel

import info.hupel.isabelle.Operation.ProverException
import info.hupel.isabelle.hol.HOLogic
import org.scalatest.FunSuite
import qrhl.UserException

class ParserTest extends FunSuite {
  implicit lazy val parserContext: ParserContext = {
    val tl = ToplevelTest.makeToplevel()
    tl.execCmd("classical var x : int")
    tl.execCmd("classical var y : int")
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
    assert(decl.calls.isEmpty)
  }

  test("adversary calls") {
    val decl = Parser.parseAll(Parser.declareAdversary, "adversary A vars x, y calls f, g").get
    assert(decl.name=="A")
    assert(decl.cvars.map(_.name)==List("x","y"))
    assert(decl.qvars.isEmpty)
    assert(decl.calls==List("f","g"))
  }
}
