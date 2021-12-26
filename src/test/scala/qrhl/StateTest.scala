package qrhl

import org.scalatest.funsuite.AnyFunSuite
import qrhl.isabellex.IsabelleX.globalIsabelle
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl
import qrhl.isabellex.RichTerm
import qrhl.toplevel.ToplevelTest

import scala.concurrent.ExecutionContext.Implicits.global

class StateTest extends AnyFunSuite {
  test("test that distinctness of variables can be shown (classical)") {
    val state = ToplevelTest.makeToplevelWithTheory().state
      .declareVariable("x", globalIsabelle.intT, quantum = false)
      .declareVariable("y", globalIsabelle.intT, quantum = false)
      .declareVariable("z", globalIsabelle.intT, quantum = false)
    val goal = state.isabelle.readTerm("cregister (cregister_pair x (cregister_pair z y))", globalIsabelle.boolT)
    val (result,_) = state.isabelle.simplify(goal, Nil)
    assert(result.isabelleTerm.concreteRecursive == globalIsabelle.True_const)
  }

  test("test that distinctness of variables can be shown (quantum)") {
    val state = ToplevelTest.makeToplevelWithTheory().state
      .declareVariable("q", globalIsabelle.intT, quantum = true)
      .declareVariable("r", globalIsabelle.intT, quantum = true)
      .declareVariable("s", globalIsabelle.intT, quantum = true)
    val goal = state.isabelle.readTerm("qregister (qregister_pair r (qregister_pair q s))", globalIsabelle.boolT)
    val (result,_) = state.isabelle.simplify(goal, Nil)
    assert(result.isabelleTerm.concreteRecursive == globalIsabelle.True_const)
  }
}
