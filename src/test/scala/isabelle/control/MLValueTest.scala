package isabelle.control

import java.nio.file.Paths

import isabelle.{Context, Thm}
import isabelle.control.Isabelle.Setup
import org.scalatest.FunSuite

import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}

import MLValue.Implicits._
import Context.Implicits._
import IsabelleTest.isabelle

object MLValueTest {
  def main(args: Array[String]): Unit = {

    implicit val ec: ExecutionContextExecutor = ExecutionContext.global
    Thm.init(isabelle)
    val ctxt = Context("Main")
//    ctxt.mlValue.retrieve
    val thm = Thm(ctxt, "refl")
    println(thm)
    println(thm.pretty(ctxt))
    val cprop = thm.cterm
    println(cprop)
    println(cprop.pretty(ctxt))
    val term = cprop.concrete
    println(term)
  }
}