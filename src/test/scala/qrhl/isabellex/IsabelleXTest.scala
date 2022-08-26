package qrhl.isabellex

import java.nio.file.{Files, Paths}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.tags.Slow
import qrhl.{State, UserException}
import qrhl.toplevel.ToplevelTest
import IsabelleX.{ContextX, globalIsabelle => GIsabelle}
import de.unruh.isabelle.pure.{Const, Context, Thm}

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

  /** Creates theories A importing B. Checks whether [[IsabelleX.globalIsabelle.getQRHLContextWithFiles]] reloads the theory content if the files have changed between calls. */
  test("reloading changed theories") {
    val tempdir = Files.createTempDirectory("qrhl-tool-test")
    println(s"DIR: $tempdir")
    val aThy = tempdir.resolve("A.thy")
    val bThy = tempdir.resolve("B.thy")
    def writeA(i : Int) =
      Files.writeString(aThy, s"""theory A imports B begin definition "(a::int) = $i" end""")
    def writeB(i : Int) =
      Files.writeString(bThy, s"""theory B imports Main begin definition "(b::int) = $i" end""")
    def getA(ctxt: Context) : String =
      Thm(ctxt, "a_def").pretty(ctxt).stripPrefix("a = ")
    def getB(ctxt: Context) : String =
      Thm(ctxt, "b_def").pretty(ctxt).stripPrefix("b = ")
    def getAB(ctxt: Context) : (String,String) =
      (getA(ctxt), getB(ctxt))
    //noinspection AccessorLikeMethodIsEmptyParen
    def getCtxt() : Context = IsabelleX.globalIsabelle.getQRHLContextWithFiles(aThy)._1.context

    {
      writeA(1)
      writeB(2)
      val ctxt = getCtxt()
      assert(getAB(ctxt) == ("1", "2"))
    }

    {
      writeA(3)
      val ctxt = getCtxt()
      assert(getAB(ctxt) == ("3", "2"))
    }

    {
      writeB(4)
      val ctxt = getCtxt()
      assert(getAB(ctxt) == ("3", "4"))
    }
  }
}

object IsabelleXTest {
  /** Makes sure that [[IsabelleX.globalIsabelle]] is initialized. */
  def ensureLoaded(): Unit = ToplevelTest.emptyState.loadIsabelle(Nil, session = None)(qrhl.toplevel.ToplevelTest.rootsDirectory)
}