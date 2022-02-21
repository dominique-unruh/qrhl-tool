package qrhl.toplevel

import org.scalatest.funsuite.AnyFunSuite
import qrhl.State

import qrhl.toplevel.ToplevelTest.rootsDirectory

class IsabelleToplevelCommandTest extends AnyFunSuite {
  test("test") {
    val state = ToplevelTest.emptyState.loadIsabelle(Nil, session = None)
    val state2 = state.applyIsabelleToplevelCommand("typedef something = \"UNIV :: nat set\" sorry")
//    val state2 = state.applyIsabelleToplevelCommand("thm refl")
    state2.isabelle.context.force
  }
}
