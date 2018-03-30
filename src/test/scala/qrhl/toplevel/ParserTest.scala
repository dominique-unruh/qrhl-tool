package qrhl.toplevel

import info.hupel.isabelle.Operation.ProverException
import org.scalatest.FunSuite

class ParserTest extends FunSuite {
  implicit val parserContext: ParserContext = ToplevelTest.makeToplevel().state.parserContext

  test("parse while loop") {
    val whileLoop = Parser.parseAll(Parser.whileLoop, "while (true) { skip; };")
  }
  test("fail to parse while loop") {
    assertThrows[ProverException] {
      val whileLoop = Parser.parseAll(Parser.whileLoop, "while (1) { skip; };")
    }
  }
}
