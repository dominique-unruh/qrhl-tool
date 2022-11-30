package qrhl.toplevel

import java.io.PrintWriter
import java.nio.file.{Path, Paths}
import hashedcomputation.filesystem.{DirectorySnapshot, FingerprintedDirectorySnapshot, RootsDirectory}
import org.scalatest.funsuite.AnyFunSuite
import qrhl.{State, UserException}
import qrhl.isabellex.IsabelleX
import qrhl.toplevel.Toplevel.{ReadLine, stripComment}

import scala.util.Random

class ToplevelTest extends AnyFunSuite {
  test("assign statement should throw UserException on undefined variable") {
    val toplevel = ToplevelTest.makeToplevelWithTheory()
    assertThrows[UserException] {
      toplevel.execCmd("program prog := { x <- (); }")
    }
  }

  test("name collision between program and variable should have proper error message") {
    val toplevel = ToplevelTest.makeToplevelWithTheory()
    toplevel.execCmd("classical var x : int")
    val exn = intercept[UserException] {
      toplevel.execCmd("program x := { skip; }") }
    assert(exn.getMessage.startsWith("Name x already used for a variable or program"))
  }


  test("stripComment") {
    assert(stripComment("# Test") == "")
    assert(stripComment(" # Test") == "")
    assert(stripComment("  start of line # Test") == "  start of line")
    assert(stripComment("  start of line# Test") == "  start of line# Test")
    assert(stripComment("  start of line # Test1 # Test2") == "  start of line")
  }

}

object ToplevelTest {
  // We create the state relative to the examples directory because otherwise some tests will try to initialize Isabelle
  // relative to session dir `<project>/examples/`, and others relative to `<project>/`.
  // This would be rejected by IsabelleX.globalIsabelleWith
  lazy val emptyState: State = State.empty(cheating = false).changeDirectory(Paths.get("examples").toAbsolutePath)

  /** Toplevel with a theory preloaded. Also suppresses errors at EOF. */
  def makeToplevelWithTheory(theory:Seq[String]=Nil) : Toplevel = {
    val tl = Toplevel.makeToplevelFromState(emptyState, errorWhenUnfinished = false)
    tl.execCmd(IsabelleCommand(theory))
    tl
  }

  implicit val output: PrintWriter = new PrintWriter(System.out, false)

//  def randomCommandString : String = "<fake> "+Random.nextLong()
  //  val isabellePath = "auto"
  //  lazy val isabelle = new Isabelle(isabellePath)
  //  def makeToplevel(): Toplevel = Toplevel.makeToplevel()
//  object dummyReadLine extends ReadLine {
//    override def readline(prompt: String): String = ???
//    override def position: String = "<test case>"
//  }

  implicit val rootsDirectory: FingerprintedDirectorySnapshot = {
    val root = RootsDirectory()
    root.registerInterest(Paths.get("ROOT").toAbsolutePath)
    root.registerInterest(Paths.get("ROOTS").toAbsolutePath)
    root.registerInterest(Paths.get("examples/ROOT").toAbsolutePath)
    root.registerInterest(Paths.get("examples/ROOTS").toAbsolutePath)
    FingerprintedDirectorySnapshot(root)
  }
}
