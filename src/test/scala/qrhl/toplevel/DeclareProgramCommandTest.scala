package qrhl.toplevel

import org.scalatest.FunSuite
import qrhl.State
import qrhl.logic.{Block, Call, ConcreteProgramDecl}

class DeclareProgramCommandTest extends FunSuite {

  test("oracles") {
    val cmd = DeclareProgramCommand("test",List("a"),Block(Call("a"),Call("b")))
    println(cmd)
    val state = State.empty(false).loadIsabelle(Nil)
    val state2 = cmd.act(state)
    println(state2.environment.programs)
    val decl = state2.environment.programs("test")
    assert(decl.name == "test")
    assert(decl.numOracles == 1)
    val decl2 = decl.asInstanceOf[ConcreteProgramDecl]
    assert(decl2.oracles == List("a"))
    assert(decl2.program == Block(Call("@a"),Call("b")))
  }
}
