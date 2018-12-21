package qrhl.tactic

import org.scalatest.FlatSpec
import qrhl.toplevel.{TacticCommand, Toplevel, ToplevelTest}

class WpTacTest extends FlatSpec {
  "WpTac" should "returns a well-typed subgoal (qinit)" in {
    val toplevel = Toplevel.makeToplevel()
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

  "WpTac" should "returns a well-typed subgoal (assign)" in {
    val toplevel = Toplevel.makeToplevel()
    toplevel.run(
      """
        |classical var q : bit.
        |qrhl {top} q <- 0; ~ q <- 0; {top}.
        |wp left.
        |wp right.
      """.stripMargin)
    val goals = toplevel.state.goal
    assert(goals.length==1)
    goals.head.checkWelltyped(toplevel.state.isabelle)
  }

  "WpTac" should "returns a well-typed subgoal (sample)" in {
    val toplevel = Toplevel.makeToplevel()
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
