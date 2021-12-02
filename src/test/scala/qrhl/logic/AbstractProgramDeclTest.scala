package qrhl.logic

import de.unruh.isabelle.pure.Term
import org.scalatest.funsuite.AnyFunSuite
import qrhl.State
import qrhl.isabellex.IsabelleX
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl
import qrhl.toplevel.{Toplevel, ToplevelTest}

import scala.concurrent.ExecutionContext.Implicits.global

class AbstractProgramDeclTest extends AnyFunSuite {
  test("declareInIsabelle does not ruin variable types") {
    val state = ToplevelTest.makeToplevelWithTheory(Nil).state
      .declareVariable("x", IsabelleX.globalIsabelle.intT, quantum=false)
    val x = state.environment.getCVariable("x")
    val t1 = Term(state.isabelle.context, "x").fastType.concreteRecursive
    val adv = AbstractProgramDecl("A", List(x), List(x), List(x), List(x), List(x), 0)
    // At some point, the following accidentally changed the type of the fixed variable x
    val isa2 = adv.declareInIsabelle(state.isabelle)
    val t2 = Term(isa2.context, "x").fastType.concreteRecursive
    println(t1.pretty(isa2.context))
    println(t2.pretty(isa2.context))
    assert(t2==t1)
  }
}
