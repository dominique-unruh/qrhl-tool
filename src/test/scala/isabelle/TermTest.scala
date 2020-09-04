package isabelle

import isabelle.control.{Isabelle, IsabelleTest}
import org.scalatest.FunSuite

import scala.concurrent.ExecutionContext.Implicits.global
import isabelle.control.IsabelleTest.isabelle

class TermTest extends FunSuite {
  lazy val ctxt: Context = Context("Main")

  test("equals: Const/Const") {
    val const1 = Const("true", Type("bool"))
    val const1b = Const("true", Type("bool"))
    val const2 = Const("false", Type("bool"))
    val const3 = Const("true", Type("xxx"))

    assert(const1==const1)
    assert(const1==const1b)
    assert(const1!=const2)
    assert(const1!=const3)
    assert(const2!=const1)
    assert(const2==const2)
    assert(const2!=const3)
    assert(const3!=const1)
    assert(const3!=const2)
    assert(const3==const3)
  }

  test("parse: True") {
    val str = "True"
    val term = Term(ctxt, str)
    println(term.getClass, term)

    term match {
      case Const("HOL.True", Type("HOL.bool", Nil)) =>
    }
  }
}
