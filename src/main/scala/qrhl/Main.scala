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
    // if cheating is false, cheating cannot be activated
    val cheating : ScallopOption[Boolean] = toggle() // Default: interactive mode: true, from file: false
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
      val tl = Toplevel.makeToplevel(cheating=conf.cheating.getOrElse(false))
      try
        tl.run(Paths.get(conf.file.toOption.get))
      catch {
        case e : Throwable =>
          e.printStackTrace()
          sys.exit(1)
      }
      sys.exit()
//      tl.dispose()
    } else
      Toplevel.main(cheating = conf.cheating.getOrElse(true))
  }
}
