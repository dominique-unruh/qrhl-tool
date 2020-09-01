package isabelle.tmp

import isabelle.{Context, Thm}
import isabelle.control.Isabelle

import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}

object Test {
  def main(args: Array[String]): Unit = {
    implicit val ec: ExecutionContextExecutor = ExecutionContext.global
    val isabelle = new Isabelle()
    Thm.init(isabelle)
    val ctxt = Context("Main")
    val thm = Thm(ctxt, "refl")
    println(thm)
    println(thm.pretty(ctxt))
  }
}
