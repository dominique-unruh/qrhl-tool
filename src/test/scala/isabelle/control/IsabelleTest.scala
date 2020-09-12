package isabelle.control

import java.nio.file.Paths

import isabelle.control.Isabelle.Setup
import isabelle.control.IsabelleTest.{isabelle => isa}
import org.scalatest.funsuite.AnyFunSuite

class IsabelleTest extends AnyFunSuite {
  test("handle compilation error") {
    assertThrows[IsabelleException] {
      isa.executeMLCodeNow("1+true")
    }
  }
}

object IsabelleTest {
  val setup: Setup = Setup(
    workingDirectory = Paths.get("/home/unruh/svn/qrhl-tool"),
    isabelleHome = Paths.get("/opt/Isabelle2020"),
    sessionRoots = Nil,
    userDir = None
  )

  implicit lazy val isabelle: Isabelle = {
    println("Starting Isabelle")
    val isa = new Isabelle(setup)
    println("Started. Initializing Term/Typ/Context")
    println("Initialized.")
    isa
  }
}
