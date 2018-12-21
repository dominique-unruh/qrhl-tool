package qrhl.tactic

import org.scalatest.FunSuite
import qrhl.QRHLSubgoal
import qrhl.isabelle.Isabelle
import qrhl.toplevel.{Toplevel, ToplevelTest}

class RndTacTest extends FunSuite {
  def toplevel(): Toplevel = {
    val tl = Toplevel.makeToplevel()
    tl.run(
      """classical var x : bool.
      """.stripMargin)
    tl
  }

  test("rnd") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} x <$ uniform UNIV; ~ x <$ uniform UNIV; {top}")
    val st = tl.state.applyTactic(RndTac())
    assert(st.goal.length==1)
    val post = st.goal.head.asInstanceOf[QRHLSubgoal].post
    assert(post.toString == "ℭ𝔩𝔞[uniform UNIV = uniform UNIV] ⊓ (⨅z∈supp (uniform UNIV). ⊤)")
    post.checkWelltyped(tl.state.isabelle, Isabelle.predicateT)
  }
}
