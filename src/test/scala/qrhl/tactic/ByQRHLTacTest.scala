package qrhl.tactic

import org.scalatest.{FlatSpec, FunSpec, FunSuite}
import qrhl.toplevel.{GoalCommand, ToplevelTest}

class ByQRHLTacTest extends FunSuite {
  test("works with Pr") {
    val tl = ToplevelTest.makeToplevel()
    tl.execCmd("classical var x : bit")
    tl.execCmd("ambient var rho : program_state")
    tl.execCmd("program p := { skip; }")
    tl.execCmd("lemma xxx: Pr[x:p(rho)] <= Pr[x:p(rho)]")
    tl.execCmd("byqrhl")
    assert(tl.state.goal.length == 1)
    tl.state.goal.head.checkWelltyped(tl.state.isabelle.get)
  }

  test("works with Pr2") {
    val tl = ToplevelTest.makeToplevel()
    tl.execCmd("classical var x : bit")
    tl.execCmd("ambient var rho : program_state")
    tl.execCmd("program p := { skip; }")
    tl.execCmd("lemma xxx: Pr2[x=1:p(rho)] <= Pr2[x=1:p(rho)]")
    println(1)
    tl.execCmd("byqrhl")
    println(2)
    assert(tl.state.goal.length == 1)
    println(3)
    print(tl.state.goal.head)
    println(4)
    tl.state.goal.head.checkWelltyped(tl.state.isabelle.get)
  }
}
