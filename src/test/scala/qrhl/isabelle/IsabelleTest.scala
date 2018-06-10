package qrhl.isabelle

import java.nio.file.Paths

import org.scalatest.FunSuite
import org.scalatest.tags.Slow
import qrhl.UserException
import qrhl.toplevel.ToplevelTest

@Slow
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
    ToplevelTest.isabelle.getQRHLContextWithFiles(Paths.get("Empty.thy"))
  }

}
