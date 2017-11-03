package qrhl.toplevel

import java.nio.file.{Path, Paths}

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

  "prg-enc-indcpa.qrhl" should "execute successfully" in {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("prg-enc-indcpa.qrhl"))
  }

  "prg-enc-rorcpa.qrhl" should "execute successfully" in {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("prg-enc-rorcpa.qrhl"))
  }

  "equality.qrhl" should "execute successfully" in {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("equality.qrhl"))
  }

}

object ToplevelTest {
  val isabellePath = "auto"
  lazy val isabelle = new Isabelle(isabellePath)
  def makeToplevel(): Toplevel = Toplevel.makeToplevel(ToplevelTest.isabelle)
}