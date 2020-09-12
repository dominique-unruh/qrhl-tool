package isabelle

import org.scalatest.funsuite.AnyFunSuite
import isabelle.control.IsabelleException
import isabelle.control.IsabelleTest.{isabelle => isa}
import isabelle.pure.Theory

import scala.concurrent.ExecutionContext.Implicits.global

class TheoryTest extends AnyFunSuite {
  test("import structure") {
    assertThrows[IsabelleException] {
      isa.executeMLCodeNow("HOLogic.boolT") }
    val thy = Theory("Main")
    thy.importMLStructure("HOLogic", "MyHOLogic")
    isa.executeMLCodeNow("MyHOLogic.boolT")
  }
}
