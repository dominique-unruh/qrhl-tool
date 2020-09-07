package isabelle.control

import java.nio.file.Paths

import isabelle.{Context, Term, Typ}
import isabelle.control.Isabelle.Setup
import isabelle.control.IsabelleTest.isabelle
import org.scalatest.FunSuite

import scala.concurrent.ExecutionContext.Implicits.global
import MLValue.Implicits._

import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future}

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
    println("Initialized.")
    isa
  }

  def main(args: Array[String]): Unit = {
    case class Tree(children: List[Tree]) {
      def size: Int = children.map(_.size).sum + 1
    }
    implicit object TreeConverter extends MLValue.Converter[Tree] {
      override def retrieve(value: MLValue[Tree])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Tree] = {
        val global = null
        value.asInstanceOf[MLValue[List[Tree]]].retrieve.map(Tree)
      }

      override def store(value: Tree)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Tree] = {
        val global = null
        MLValue(value.children).asInstanceOf[MLValue[Tree]]
      }

      override lazy val exnToValue: String = ???
      override lazy val valueToExn: String = ???
    }
    val emptyTree = Tree(Nil)

    val inc = MLValue.compileFunction[Int, Int]("fn i => i+1")
    def time(text: String, n: Int)(fun : => Unit): Unit = {
//      println("One iteration before")
//      fun
      println(s"Start timing... ($text)")
      val t1 = System.nanoTime
      for (i <- 1 to n)
        fun
      val t2 = System.nanoTime()
      val timePerIter = (t2-t1) / 1000000.0 / n
      println(f"$timePerIter%2fms per iteration")
    }

    var nums : List[MLValue[Int]] = null
    time ("MLValue", 1) {
      nums = (1 to 10000).map(MLValue.apply[Int]).toList
    }

    var futures : List[Future[Int]] = null
    time ("futures", 1) {
      futures = nums.map(_.retrieve)
    }

    time ("results", 1) {
      futures.map(future => Await.result(future, Duration.Inf))
    }

    def double(x: Tree) = Tree(List(x,x))

//    val tree = double(double(double(double(double(double(double(double(double(double(
//      double(double(double(double(double(double(double(double(double(double(emptyTree))))))))))))))))))))
//
//    println(s"size: ${tree.size}")
//
//    time ("tree", 1) {
//      MLValue(tree).retrieveNow
//    }
//
//    val list = (1 to 1000).toList
//    time ("list", 1) {
//      MLValue(list).retrieveNow
//    }
  }
}
