package qrhl.logic

import org.scalatest.funsuite.AnyFunSuite

class BlockTest extends AnyFunSuite {
  test("inline") {
    val program = Block(Call("a"), Call("b"))
    val a = Call("c")
    val inlined = program.inline("a",Nil,a)
    assert(inlined == Block(Call("c"), Call("b")))
  }

  test("inline with oracles") {
    val program = Block(Call("a",Call("d")), Call("b"))
    val a = Call("c",Call("@a"))
    val inlined = program.inline("a",List("a"),a)
    assert(inlined == Block(Call("c",Call("d")), Call("b")))
  }
}
