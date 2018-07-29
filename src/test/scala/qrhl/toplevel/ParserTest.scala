package qrhl.toplevel

import info.hupel.isabelle.Operation.ProverException
import info.hupel.isabelle.hol.HOLogic
import org.scalatest.FunSuite
import qrhl.UserException

class ParserTest extends FunSuite {
  implicit lazy val parserContext: ParserContext = ToplevelTest.makeToplevel().state.parserContext

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
}
