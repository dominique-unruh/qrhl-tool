package isabelle

import isabelle.control.{Isabelle, IsabelleTest}
import org.scalatest.FunSuite

import scala.concurrent.ExecutionContext.Implicits.global

class TermTest extends FunSuite {
  lazy val ctxt: Context = Context("Main")

  test("parse: True") {
    implicit val isa: Isabelle = IsabelleTest.isabelle

    val str = "True"
    val term = Term(ctxt, str)
    println(term.getClass, term)

    term match {
      case Const("HOL.True", Type("HOL.bool", Nil)) =>
    }
  }
}
