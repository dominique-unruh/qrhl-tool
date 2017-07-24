package qrhl.isabelle

import org.scalatest.FlatSpec
import qrhl.UserException


class IsabelleTest extends FlatSpec {
  "Isabelle" should "fail with UserException when given wrong path" in {
    assertThrows[UserException] {
      new Isabelle("/tmp/xxx")
    }
  }
}
