package isabelle.control

import java.nio.file.Paths

import isabelle.{Context, Theory, Thm}
import isabelle.control.Isabelle.Setup
import org.scalatest.FunSuite

import scala.concurrent.{Await, Awaitable, ExecutionContext, ExecutionContextExecutor}
import MLValue.Implicits._
import Context.Implicits._

import scala.concurrent.duration.Duration

object MLValueTest {
  def await[A](x: Awaitable[A]): A = Await.result(x, Duration.Inf)

  def main(args: Array[String]): Unit = {
    implicit val ec: ExecutionContextExecutor = ExecutionContext.global
    implicit val isabelle: Isabelle = IsabelleTest.isabelle
    Thm.init(isabelle)
    val thy = Theory("Main")
//    await(Theory.importMLStructure.id)
    thy.importMLStructure("HOLogic", "Hello")
    isabelle.executeMLCodeNow("Hello.Trueprop")
  }
}