package qrhl.logic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.toplevel.ToplevelTest

class StatementTest extends AnyFunSuite {
  test("equality") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.run(
      """quantum var Q : int.
        |classical var x : int.
        |""".stripMargin)
    val block1 = tl.state.parseBlock("x <- measure Q with computational_basis;")
    val block2 = tl.state.parseBlock("x <- measure Q with computational_basis;")
    assert(block1 == block2)
  }
}
