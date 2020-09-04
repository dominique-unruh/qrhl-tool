package isabelle.control

import java.nio.file.Paths

import isabelle.{Context, Term, Typ}
import isabelle.control.Isabelle.Setup
import isabelle.control.IsabelleTest.isabelle
import org.scalatest.FunSuite

import scala.concurrent.ExecutionContext.Implicits.global

class IsabelleTest extends FunSuite {
  test("handle compilation error") {
    assertThrows[IsabelleException] {
      isabelle.executeMLCodeNow("1+true")
    }
  }
}

object IsabelleTest {
  val setup: Setup = Setup(
    workingDirectory = Paths.get("/home/unruh/svn/qrhl-tool"),
    isabelleHome = Paths.get("Isabelle2019-RC4"),
    sessionRoots = Nil,
    userDir = Some(Paths.get("isabelle-temp/user/Isabelle2019-RC4/.isabelle"))
  )

  implicit lazy val isabelle: Isabelle = {
    println("Starting Isabelle")
    val isa = new Isabelle(setup)
    println("Started. Initializing Term/Typ/Context")
    Term.init(isa)
    Typ.init(isa)
    Context.init(isa)
    println("Initialized.")
    isa
  }
}