package qrhl.tactic

import org.scalatest.funsuite.AnyFunSuite
import qrhl.QRHLSubgoal
import qrhl.isabellex.IsabelleX
import qrhl.toplevel.{Toplevel, ToplevelTest}
import IsabelleX.{globalIsabelle => GIsabelle}
import qrhl.toplevel.ToplevelTest.output

class RndTacTest extends AnyFunSuite {
  def toplevel(): Toplevel = {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.run(
      """classical var x : bool.
      """.stripMargin)
    tl
  }

  test("rnd") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} x <$ uniform UNIV; ~ x <$ uniform UNIV; {top}")
    val st = tl.state.applyTactic(RndEqualTac)

    val context = tl.state.isabelle

    assert(st.goal.length==1)
    val post = st.goal.head.asInstanceOf[QRHLSubgoal].post
    print(s"Post: $post")
    assert(post.decodeFromExpression(context).toString == "ℭ𝔩𝔞[uniform UNIV = uniform UNIV] ⊓ (⨅z∈supp (uniform UNIV). ⊤)")
    post.checkWelltyped(tl.state.isabelle, GIsabelle.predicateT)
  }

  test("rnd witness") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} x <$ uniform UNIV; ~ x <$ uniform UNIV; {top}")
    tl.execCmd("rnd x,x <- map_distr (%x. (x,x)) (uniform UNIV)")
    val st = tl.state

    assert(st.goal.length==1)
    val post = st.goal.head.asInstanceOf[QRHLSubgoal].post
//    assert(post.toString == "???")
    post.checkWelltyped(tl.state.isabelle, GIsabelle.predicateT)
  }
}
