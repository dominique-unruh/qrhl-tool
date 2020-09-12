package isabelle

import org.scalatest.funsuite.AnyFunSuite
import isabelle.control.IsabelleException

import isabelle.control.IsabelleTest.isabelle
import scala.concurrent.ExecutionContext.Implicits.global

class TheoryTest extends AnyFunSuite {
  test("import structure") {
    assertThrows[IsabelleException] {
      isabelle.executeMLCodeNow("HOLogic.boolT") }
    val thy = Theory("Main")
    thy.importMLStructure("HOLogic", "MyHOLogic")
    isabelle.executeMLCodeNow("MyHOLogic.boolT")
  }
}
