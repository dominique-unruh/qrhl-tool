package qrhl.tactic

import org.scalatest.FlatSpec
import qrhl.UserException
import qrhl.toplevel.{Toplevel, ToplevelTest}

class CallTacTest extends FlatSpec {
  def toplevel(): Toplevel = {
    val tl = ToplevelTest.makeToplevel()
    tl.run(
      """classical var x : bit.
        |quantum var q : bit.
        |program p := { x <- undefined; on q apply undefined; }.
      """.stripMargin)
    tl
  }

//  "call tactic" should "complain about classical program variables in post condition" in {
//    val tl = toplevel()
//    tl.execCmd("qrhl {top} call p; ~ call p; {Cla[x1=0]}")
//
//    val ex = intercept[UserException] {
//      tl.state.applyTactic(CallTac)
//    }
//    println(ex)
//
//    assert(ex.msg.startsWith("Postcondition must not contain variable"))
//  }

  "call tactic" should "complain about quantum program variables in post condition" in {
    val tl = toplevel()
    tl.execCmd("qrhl {top} call p; ~ call p; {lift undefined ⟦q1⟧}")

    val ex = intercept[UserException] {
      tl.state.applyTactic(CallTac)
    }

    assert(ex.msg.startsWith("Postcondition must not contain variable"))
  }

  "call tactic" should "permit postcondition to contain the quantum variable equality" in {
    val tl = toplevel()
    tl.execCmd("qrhl {top} call p; ~ call p; {Qeq[q1=q2]}")
    tl.state.applyTactic(CallTac)
  }
}
