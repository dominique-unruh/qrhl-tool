package qrhl.toplevel

import org.scalatest.funsuite.AnyFunSuite
import qrhl.State

import qrhl.toplevel.ToplevelTest.rootsDirectory

class IsabelleToplevelCommandTest extends AnyFunSuite {
  test("test") {
    val state = ToplevelTest.emptyState.loadIsabelle(Nil, session = None)
    val state2 = state.applyIsabelleToplevelCommand("typedef something = \"UNIV :: nat set\" sorry")
    state2.isabelle.context.force
  }

  test("test unicode") {
    val state = ToplevelTest.emptyState.loadIsabelle(Nil, session = None)
    val state2 = state.applyIsabelleToplevelCommand("typedef Δ = \"UNIV :: nat set\" sorry")
    state2.isabelle.context.force
  }
}
