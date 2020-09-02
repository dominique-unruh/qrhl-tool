package qrhl

import java.nio.file.{Path, Paths}

import org.rogach.scallop.{ScallopConf, ScallopOption, Subcommand}
import qrhl.isabellex.IsabelleX
import qrhl.toplevel.Toplevel
import qrhl.toplevel.Toplevel.runFromTerminal

object Main {
  class CLIConf(args: Seq[String]) extends ScallopConf(args) {
    val rebuild : ScallopOption[Boolean] = toggle()
    // if cheating is false, cheating cannot be activated
    val cheating : ScallopOption[Boolean] = toggle() // Default: interactive mode: true, from file: false
    val emacs : ScallopOption[Boolean] = toggle() // Ignored but ProofGeneral needs to give some option to support spaces in paths
    val file: ScallopOption[String] = trailArg[String](required=false)
  }

  def checkJavaVersion() : Unit = {
    val version = System.getProperty("java.version")
//    println(version)
    val major = version.split("\\.")(0).toInt
//    println(major)
    if (major < 9) {
      System.err.println(s"Requiring at least Java version 9, got $version")
      System.exit(1)
    }
  }

  def main(args: Array[String]): Unit = {
    checkJavaVersion()

    val conf = new CLIConf(args)
    conf.verify()
    if (conf.rebuild.getOrElse(false)) {
      val isabelle = new IsabelleX(build=true)
      isabelle.dispose()
    } else if (conf.file.isDefined) {
      val tl = Toplevel.makeToplevel(cheating=conf.cheating.getOrElse(false))
      try
        if (!tl.runWithErrorHandler(Paths.get(conf.file.toOption.get), abortOnError = true))
          sys.exit(1)
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
