package qrhl.isabelle

import org.scalatest.FlatSpec
import qrhl.UserException
import qrhl.toplevel.{Toplevel, ToplevelTest}


class IsabelleTest extends FlatSpec {
  "Isabelle" should "fail with UserException when given wrong path" in {
    assertThrows[UserException] {
      new Isabelle("/tmp/xxx")
    }
  }

  "Isabelle" should "initialize successfully with path=auto" in {
    new Isabelle("auto")
  }

  "Isabelle" should "load an empty theory" in {
    ToplevelTest.isabelle.getContextFile("Empty")
  }
}
