package qrhl.tactic

import org.scalatest.FunSuite
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.toplevel.{Toplevel, ToplevelTest}

class O2HTacTest extends FunSuite {
  test("o2h tac") {
    val tl = Toplevel.makeToplevelWithTheory()
    tl.run(
      """
        | ambient var q : nat.
        | ambient var rho : program_state.
        | classical var b : bit.
        | classical var Find : bool.
        | program p := {}.
        |
        | lemma abs ( Pr[b=1:p(rho)] - Pr[b=1:p(rho)] ) <= 2 * sqrt( (1+real q) * Pr[Find:p(rho)] ).
      """.stripMargin)

    val state2 = tl.state.applyTactic(O2HTac)
    println(state2)

    ???
  }
}
