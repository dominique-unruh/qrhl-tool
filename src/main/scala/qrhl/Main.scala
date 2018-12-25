package qrhl

import java.nio.file.{Path, Paths}

import org.rogach.scallop.{ScallopConf, ScallopOption, Subcommand}
import qrhl.isabelle.Isabelle
import qrhl.toplevel.Toplevel
import qrhl.toplevel.Toplevel.runFromTerminal

object Main {
  class CLIConf(args: Seq[String]) extends ScallopConf(args) {
    val isabelle: ScallopOption[String] = opt[String]()
    val rebuild : ScallopOption[Boolean] = toggle()
    val emacs : ScallopOption[Boolean] = toggle() // Ignored but ProofGeneral needs to give some option to support spaces in paths
    val file: ScallopOption[String] = trailArg[String](required=false)
  }

  def main(args: Array[String]): Unit = {
    val conf = new CLIConf(args)
    conf.verify()
    if (conf.rebuild.getOrElse(false)) {
      val isabelle = new Isabelle("auto", build=true)
      isabelle.dispose()
    } else if (conf.isabelle.supplied) {
      val isabelle = new Isabelle(conf.isabelle.toOption.get, build=true)
      isabelle.runJEdit(if (conf.file.supplied) List(conf.file.toOption.get) else Nil)
      isabelle.dispose()
    } else if (conf.file.isDefined) {
      val tl = new Toplevel()
      tl.run(Paths.get(conf.file.toOption.get))
//      tl.dispose()
    } else
      Toplevel.main()
  }
}
