package qrhl.toplevel

import org.scalatest.{FlatSpec, FunSuite}
import qrhl.UserException
import qrhl.isabelle.Isabelle

class ToplevelTest extends FlatSpec {
  "toplevel" should "assign statement should throw UserException on undefined variable" in {
    val toplevel = ToplevelTest.makeToplevel()
    assertThrows[UserException] {
      toplevel.execCmd("program prog := { x <- (); }")
    }
  }
}

object ToplevelTest {
  val isabellePath = "auto"
  lazy val isabelle = new Isabelle(isabellePath)
  def makeToplevel(): Toplevel = Toplevel.makeToplevel(ToplevelTest.isabelle)
}