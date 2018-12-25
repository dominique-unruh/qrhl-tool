package qrhl.tactic

import org.scalatest.{FlatSpec, FunSpec, FunSuite}
import qrhl.toplevel.{TacticCommand, ToplevelTest}

class WpTacTest extends FunSuite {
  test("WpTac well-typed (qinit)") {
    val toplevel = ToplevelTest.makeToplevel()
    toplevel.run(
      """
        |quantum var q : bit.
        |qrhl {top} q <q ket 0; ~ q <q ket 0; {top}.
        |wp left.
        |wp right.
      """.stripMargin)
    val goals = toplevel.state.goal
    assert(goals.length==1)
    goals.head.checkWelltyped(toplevel.state.isabelle)
  }

  test("WpTac well-typed (assign)") {
    val toplevel = ToplevelTest.makeToplevel()
    toplevel.run(
      """
        |classical var q : bit.
        |qrhl {top} q <- 0; ~ q <- 0; {top}.
      """.stripMargin)
    toplevel.execCmd(TacticCommand(WpTac(left=true)))
    toplevel.execCmd(TacticCommand(WpTac(left=false)))
    val goals = toplevel.state.goal
    assert(goals.length==1)
    goals.head.checkWelltyped(toplevel.state.isabelle)
  }

  test("WpTac well-typed (sample)") {
    val toplevel = ToplevelTest.makeToplevel()
    toplevel.run(
      """
        |classical var q : bit.
        |qrhl {top} q <$ uniform UNIV; ~ q <$ uniform UNIV; {top}.
        |wp left.
        |wp right.
      """.stripMargin)
    val goals = toplevel.state.goal
    assert(goals.length==1)
    goals.head.checkWelltyped(toplevel.state.isabelle)
  }
}
