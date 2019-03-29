package qrhl.tactic

import org.scalatest.{FlatSpec, FunSpec, FunSuite}
import qrhl.toplevel.{TacticCommand, Toplevel, ToplevelTest}

class WpTacTest extends FunSuite {
  test("WpTac well-typed (qinit)") {
    val toplevel = Toplevel.makeToplevelWithTheory()
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

  test("WpTac well-typed (qinit, two in one)") {
    val toplevel = Toplevel.makeToplevelWithTheory()
    toplevel.run(
      """
        |quantum var q : bit.
        |qrhl {top} q <q ket 0; ~ q <q ket 0; {top}.
        |wp 1 1.
      """.stripMargin)
    val goals = toplevel.state.goal
    assert(goals.length==1)
    goals.head.checkWelltyped(toplevel.state.isabelle)
  }

  test("WpTac well-typed (assign)") {
    val toplevel = Toplevel.makeToplevelWithTheory()
    toplevel.run(
      """
        |classical var q : bit.
        |qrhl {top} q <- 0; ~ q <- 0; {top}.
      """.stripMargin)
    toplevel.execCmd(TacticCommand(WpTac(left=1,right=0)), "<test>")
    toplevel.execCmd(TacticCommand(WpTac(left=0,right=1)), "<test>")
    val goals = toplevel.state.goal
    assert(goals.length==1)
    goals.head.checkWelltyped(toplevel.state.isabelle)
  }

  test("WpTac well-typed (sample)") {
    val toplevel = Toplevel.makeToplevelWithTheory()
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
