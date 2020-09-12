package isabelle.control

import java.nio.file.Paths

import isabelle.control.Isabelle.Setup
import isabelle.control.IsabelleTest.{isabelle => isa}
import org.scalatest.funsuite.AnyFunSuite

import scala.concurrent.{Await, Awaitable}
import scala.concurrent.duration.Duration

class IsabelleTest extends AnyFunSuite {
  private def await[A](f: Awaitable[A]) : A = Await.result(f, Duration.Inf)

  test("handle compilation error") {
    assertThrows[IsabelleException] {
      isa.executeMLCodeNow("1+true")
    }
  }

  test("initialize Isabelle") {
    isa
  }

  test("executeMLCode") {
    println("Sending code")
    val exec = isa.executeMLCode("val _ = tracing \"Hello\"")
    println("Waiting for completion")
    await(exec)
  }




  test("storeValue / retrieveString") {
    val id = await(isa.storeValue("E_Int 123"))
    val int = await(isa.retrieveLong(id))
    assert(int == 123)
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
