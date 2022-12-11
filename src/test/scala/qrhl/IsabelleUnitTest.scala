package qrhl

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.pure.Theory
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.tags.Slow
import qrhl.isabellex.{IsabelleX, IsabelleXTest}
import qrhl.toplevel.{Toplevel, ToplevelTest}

import java.nio.file.{Files, Paths}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.reflect.io.Path

@Slow
class IsabelleUnitTest extends AnyFunSuite {
  /** Runs the unit tests in src/test/isabelle (simply by loading the theory `All_Unit_Tests.thy`). */
  test("Isabelle unit tests") {
    IsabelleXTest.ensureLoaded()
    implicit val isabelle: Isabelle = IsabelleX.globalIsabelle.isabelleControl
    val thyPath = Paths.get("src/test/isabelle/All_Unit_Tests.thy")
    assert(Files.exists(thyPath))
    val thy = Theory(thyPath)
    thy.force
  }
}
