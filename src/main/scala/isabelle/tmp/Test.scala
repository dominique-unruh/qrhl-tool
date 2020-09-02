package isabelle.tmp

import java.nio.file.{Path, Paths}

import isabelle.{Context, Thm}
import isabelle.control.Isabelle
import isabelle.control.Isabelle.Setup
import qrhl.isabelle.DistributionDirectory

import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}

object Test {
  val setup = Setup(
    workingDirectory = DistributionDirectory.distributionDirectory,
    isabelleHome = Paths.get("Isabelle2019-RC4"),
    sessionRoots = Nil,
    userDir = Some(Paths.get("isabelle-temp/user/Isabelle2019-RC4/.isabelle"))
  )

  def main(args: Array[String]): Unit = {
    implicit val ec: ExecutionContextExecutor = ExecutionContext.global
    val isabelle = new Isabelle(setup)
    Thm.init(isabelle)
    val ctxt = Context("Main")
    val thm = Thm(ctxt, "refl")
    println(thm)
    println(thm.pretty(ctxt))
  }
}
