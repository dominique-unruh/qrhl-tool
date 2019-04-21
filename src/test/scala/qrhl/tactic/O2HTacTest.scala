package qrhl.tactic

import info.hupel.isabelle.ProverResult
import org.scalatest.FunSuite
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.toplevel.{Toplevel, ToplevelTest}

class O2HTacTest extends FunSuite {
  test("o2h tac") {
    val tl = Toplevel.makeToplevelWithTheory(List("Empty"))
    tl.run(
      """
        | ambient var q : nat.
        | ambient var rho : program_state.
        | classical var b : bit.
        | classical var Find : bool.
        | classical var count : nat.
        | ambient var o2h_distr : (string set * (string=>bit) * (string=>bit) * unit) distr.
        | classical var G : string => bit.
        | classical var H : string => bit.
        | classical var z : unit.
        | classical var S : string set.
        | quantum var X : string.
        | quantum var Y : bit.
        | classical var hit : bit.
        |
        | program Count(O) := { call O; count <- count + 1; }.
        | adversary Adv_O2H vars z, b, H, X, Y calls ?.
        |
        |
        | program queryG := { on X,Y apply (Uoracle G); }.
        | program queryGS := {
        |   hit <- measure X with binary_measurement (projS S);
        |   if (hit=1) then Find <- True; else skip;
        |   call queryG;
        | }.
        | program queryH := { on X,Y apply (Uoracle H); }.
        |
        | program left := {
        |  count <- 0;
        |  (S,G,H,z) <$ o2h_distr;
        |  call Adv_O2H(Count(queryG));
        | }.
        |
        | program find := {
        |  count <- 0;
        |  (S,G,H,z) <$ o2h_distr;
        |  Find <- False;
        |  call Adv_O2H(Count(queryGS));
        | }.
        |
        | program right := {
        |  count <- 0;
        |  (S,G,H,z) <$ o2h_distr;
        |  call Adv_O2H(Count(queryH));
        | }.
        |
        | debug:isabelle.
        |
        | lemma abs ( Pr[b=1:left(rho)] - Pr[b=1:right(rho)] ) <= 2 * sqrt( (1+real q) * Pr[Find:find(rho)] ).
      """.stripMargin)

    val state2 = try {
      tl.state.applyTactic(O2HTac)
    } catch {
      case e : ProverResult.Failure =>
        println(e.fullMessage)
        throw e
    }

    println(state2)

    ???
  }
}
