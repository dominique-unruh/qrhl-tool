package isabelle.control

import java.nio.file.Paths

import isabelle.{Context, Thm}
import isabelle.control.Isabelle.Setup
import org.scalatest.FunSuite

import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}

object MLValueTest {
  def main(args: Array[String]): Unit = {
    val setup: Setup = Setup(
      workingDirectory = Paths.get("/home/unruh/svn/qrhl-tool"),
      isabelleHome = Paths.get("Isabelle2019-RC4"),
      sessionRoots = Nil,
      userDir = Some(Paths.get("isabelle-temp/user/Isabelle2019-RC4/.isabelle"))
    )

    implicit val ec: ExecutionContextExecutor = ExecutionContext.global
    val isabelle = new Isabelle(setup)
    Thm.init(isabelle)
    val ctxt = Context("Main")
    val thm = Thm(ctxt, "refl")
    println(thm)
    println(thm.pretty(ctxt))
  }
}