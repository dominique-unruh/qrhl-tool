package qrhl.toplevel

import org.scalatest.funsuite.AnyFunSuite
import qrhl.State
import qrhl.logic.{Block, Call, ConcreteProgramDecl}

class DeclareProgramCommandTest extends AnyFunSuite {

  test("oracles") {
    val cmd0 = DeclareProgramCommand("b", Nil, Block.empty)
    val cmd = DeclareProgramCommand("test",List("a"), Block(Call("a"), Call("b")))
    println(cmd)
    val state = State.empty(false).loadIsabelle(Nil)
    val state2 = cmd0.actPrint(state)
    val state3 = cmd.actPrint(state2)
    println(state3.environment.programs)
    val decl = state3.environment.programs("test")
    assert(decl.name == "test")
    assert(decl.numOracles == 1)
    val decl2 = decl.asInstanceOf[ConcreteProgramDecl]
    assert(decl2.oracles == List("a"))
    assert(decl2.program == Block(Call("@a"), Call("b")))
  }
}
