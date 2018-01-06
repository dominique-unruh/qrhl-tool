package qrhl.isabelle

import org.scalatest.{FlatSpec, FunSpec, FunSuite}
import qrhl.UserException
import qrhl.toplevel.{Toplevel, ToplevelTest}


class IsabelleTest extends FunSuite {
  test("wrong path") {
    assertThrows[UserException] {
      new Isabelle("/tmp/xxx")
    }
  }

  test("initialize with path=auto") {
    new Isabelle("auto")
  }

  test("load an empty theory") {
    ToplevelTest.isabelle.getQRHLContextWithFiles("Empty")
  }
}
