package qrhl.tactic

import org.scalatest.FunSuite
import qrhl.toplevel.Toplevel

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
        | adversary Adv_O2H free z, b, X, Y calls ?.
        |
        | program queryG := { on X,Y apply (Uoracle G); }.
        | program queryGS := {
        |   hit <- measure X with binary_measurement (proj_classical_set S);
        |   if (hit=1) then Find <- True; else skip;
        |   call queryG;
        | }.
        | program queryH := { on X,Y apply (Uoracle H); }.
        |
        | program left := {
        |  count <- 0;
        |  (S,G,H,z) <$ o2h_distr;
        |  { local X,Y; call Adv_O2H(Count(queryG)); }
        | }.
        |
        | program find := {
        |  count <- 0;
        |  (S,G,H,z) <$ o2h_distr;
        |  Find <- False;
        |  { local X,Y; call Adv_O2H(Count(queryGS)); }
        | }.
        |
        | program right := {
        |  count <- 0;
        |  (S,G,H,z) <$ o2h_distr;
        |  { local X,Y; call Adv_O2H(Count(queryH)); }
        | }.
        |
        | lemma abs ( Pr[b=1:left(rho)] - Pr[b=1:right(rho)] ) <= 2 * sqrt( (1+real q) * Pr[Find:find(rho)] ).
      """.stripMargin)

    val state2 = tl.state.value.applyTactic(O2HTac)

    println(state2)

    assert(state2.goal.length==4)
    //noinspection ZeroIndexToHead
    assert(state2.goal(0).toString == "probability (expression 〚var_count〛 (λcount. count ≤ q)) left rho = 1")
    assert(state2.goal(1).toString == "probability (expression 〚var_count〛 (λcount. count ≤ q)) right rho = 1")
    assert(state2.goal(2).toString == "probability (expression 〚var_count〛 (λcount. count ≤ q)) find rho = 1")
    assert(state2.goal(3).toString == "∀S G H z x. (S, G, H, z) ∈ supp o2h_distr ⟶ x ∉ S ⟶ G x = H x")
  }
}
