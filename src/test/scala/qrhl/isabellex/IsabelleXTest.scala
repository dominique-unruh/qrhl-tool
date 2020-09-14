package qrhl.isabellex

import java.nio.file.Paths

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.tags.Slow
import qrhl.UserException
import qrhl.toplevel.ToplevelTest
import IsabelleX.{globalIsabelle => GIsabelle}
import de.unruh.isabelle.pure.Const

// Implicits
import GIsabelle.isabelleControl
import scala.concurrent.ExecutionContext.Implicits.global

@Slow
class IsabelleXTest extends AnyFunSuite {

  test("initialize") {
    IsabelleX.globalIsabelle
//    Isabelle.globalIsabelle.new Isabelle("auto")
  }

  test("load an empty theory") {
    IsabelleX.globalIsabelle.getQRHLContextWithFiles(Paths.get("Empty.thy"))
  }

  test("dest_char") {
    val term = Const ("String.char.Char", GIsabelle.unitT) $ // using unitT here since dest_char doesn't look at the type anyway
      GIsabelle.False_const $ GIsabelle.False_const $ GIsabelle.False_const $ GIsabelle.True_const $ GIsabelle.True_const $ GIsabelle.True_const $ GIsabelle.True_const $ GIsabelle.False_const
    val c = GIsabelle.dest_char(term)
    assert(c=='x')
  }
}
