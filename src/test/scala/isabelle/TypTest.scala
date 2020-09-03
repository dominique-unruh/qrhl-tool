package isabelle

import isabelle.control.{Isabelle, IsabelleTest}
import org.scalatest.FunSuite

import scala.concurrent.ExecutionContext.Implicits.global

class TypTest extends FunSuite {
  lazy val ctxt: Context = Context("Main")

  test("parse: nat") {
    implicit val isa: Isabelle = IsabelleTest.isabelle

    val str = "nat"
    val typ = Typ(ctxt, str)
    println(typ.getClass, typ)
    typ match {
      case Type("Nat.nat", List()) => ()
      case _ => fail()
    }
  }
}
