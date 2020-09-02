package qrhl.tactic

import info.hupel.isabelle.ProverResult
import org.scalatest.FunSuite
import qrhl.QRHLSubgoal
import qrhl.isabellex.IsabelleX
import qrhl.logic.CVariable
import qrhl.toplevel.{Toplevel, ToplevelTest}
import IsabelleX.{globalIsabelle => GIsabelle}

class RndTacTest extends FunSuite {
  def toplevel(): Toplevel = {
    val tl = Toplevel.makeToplevelWithTheory()
    tl.run(
      """classical var x : bool.
      """.stripMargin)
    tl
  }

  test("rnd") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} x <$ uniform UNIV; ~ x <$ uniform UNIV; {top}")
    val st =
      try
        tl.state.value.applyTactic(RndEqualTac)
      catch {
        case e : ProverResult.Failure => println(e.fullMessage); throw e }

    assert(st.goal.length==1)
    val post = st.goal.head.asInstanceOf[QRHLSubgoal].post
    assert(post.toString == "ℭ𝔩𝔞[uniform UNIV = uniform UNIV] ⊓ (⨅z∈supp (uniform UNIV). ⊤)")
    post.checkWelltyped(tl.state.value.isabelle, GIsabelle.predicateT)
  }

  test("rnd witness") {
    val tl = toplevel()
    tl.execCmd("qrhl {top} x <$ uniform UNIV; ~ x <$ uniform UNIV; {top}")
    tl.execCmd("rnd x,x <- map_distr (%x. (x,x)) (uniform UNIV)")
    val st = tl.state

    assert(st.value.goal.length==1)
    val post = st.value.goal.head.asInstanceOf[QRHLSubgoal].post
//    assert(post.toString == "???")
    post.checkWelltyped(tl.state.value.isabelle, GIsabelle.predicateT)
  }
}
