package qrhl.isabelle

import java.nio.file.Paths

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.{Const, Term, Type}
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

  test("dest_char") {
    val term = Const ("String.char.Char", Isabelle.unitT) $ // using unitT here since dest_char doesn't look at the type anyway
      HOLogic.False $ HOLogic.False $ HOLogic.False $ HOLogic.True $ HOLogic.True $ HOLogic.True $ HOLogic.True $ HOLogic.False
    val c = Isabelle.dest_char(term)
    assert(c=='x')
  }
}
