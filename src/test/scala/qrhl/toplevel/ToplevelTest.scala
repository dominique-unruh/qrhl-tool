package qrhl.toplevel

import org.scalatest.{FlatSpec, FunSuite}
import qrhl.UserException
import qrhl.isabelle.Isabelle

class ToplevelTest extends FlatSpec {
  def makeToplevel(): Toplevel = Toplevel.makeToplevel(ToplevelTest.isabelle)

  "toplevel" should "assign statement should throw UserException on undefined variable" in {
    val toplevel = makeToplevel()
    assertThrows[UserException] {
      toplevel.execCmd("program prog := { x <- (); }")
    }
  }
}

object ToplevelTest {
  val isabellePath = "/opt/Isabelle2016-1"
  lazy val isabelle = new Isabelle(isabellePath)
}