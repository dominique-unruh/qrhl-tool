package isabelle.control

import java.nio.file.Paths

import isabelle.pure.{Context, Theory, Thm}
import isabelle.control.Isabelle.Setup
import isabelle.mlvalue.MLValue
import org.scalatest.funsuite.AnyFunSuite

import scala.concurrent.{Await, Awaitable, ExecutionContext, ExecutionContextExecutor}
import isabelle.mlvalue.MLValue.Implicits._
import isabelle.pure.Context.Implicits._

import scala.concurrent.duration.Duration
import scala.concurrent.ExecutionContext.Implicits.global
import isabelle.control.IsabelleTest.isabelle

class MLValueTest extends AnyFunSuite {
  test ("two instances of Isabelle") {
    val isabelle1 = IsabelleTest.isabelle
    val isabelle2 = new Isabelle(IsabelleTest.setup)
    val ctxt1 = Context("Pure")(isabelle1, implicitly)
    val ctxt2 = Context("Main")(isabelle2, implicitly)
    val thm1 = Thm(ctxt1, "Pure.reflexive")(isabelle1, implicitly)
    val thm2 = Thm(ctxt2, "HOL.refl")(isabelle2, implicitly)
    val str1 = thm1.pretty(ctxt1)
    val str2 = thm2.pretty(ctxt2)
    assert(str1 == "?x \\<equiv> ?x")
    assert(str2 == "?t = ?t")
  }

  test ("store/retrieve int") {
    val i = 43458
    val mlVal = MLValue(i)
    val i2 = mlVal.retrieveNow
    assert(i==i2)
  }

  def await[A](x: Awaitable[A]): A = Await.result(x, Duration.Inf)
}