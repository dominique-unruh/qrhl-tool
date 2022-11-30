package qrhl.isabellex

import org.scalatest.funsuite.AnyFunSuite
import qrhl.logic.{Call, Statement}

import scala.concurrent.ExecutionContext.Implicits.global
import MLValueConverters.Implicits._
import IsabelleX.globalIsabelle.isabelleControl
import de.unruh.isabelle.mlvalue.MLValue
import org.scalatest.BeforeAndAfterAll
import qrhl.toplevel.ToplevelTest

class MLValueConvertersTest extends AnyFunSuite with BeforeAndAfterAll {
  override def beforeAll(): Unit = IsabelleXTest.ensureLoaded()

  test("Call roundtrip") {
    val prog = Call("a")
    val mlProg = MLValue[Call](prog)
    print(mlProg)
    val prog2 = mlProg.retrieveNow
    print(prog2)
    assert(prog==prog2)
  }

  test("Call as statement roundtrip") {
    val prog = Call("a")
    println(prog)
    val mlProg = MLValue[Statement](prog)
    print(mlProg)
    val prog2 = mlProg.retrieveNow
    print(prog2)
    assert(prog==prog2)
  }

}
