package qrhl

import java.nio.file.{Files, Path, Paths}
import de.unruh.isabelle.control.Isabelle
import org.rogach.scallop.{ScallopConf, ScallopOption, Subcommand}
import qrhl.isabellex.IsabelleX
import qrhl.toplevel.Toplevel
import qrhl.toplevel.Toplevel.runFromTerminal

import java.io.PrintStream

object Main {
  // On Windows, the output charset may not be UTF-8 even with VM option -Dfile.encoding=UTF-8. So we force it here.
  // We set it here (i.e., upon object initialization) to make sure that it is executed before scala.Console is
  // initialized because scala.Console uses a copy the System.out and we cannot change that copy globally later.
  System.setOut(new PrintStream(System.out, true, "UTF-8"))

  class CLIConf(args: Seq[String]) extends ScallopConf(args) {
    val build : ScallopOption[Boolean] = toggle()
    // if cheating is false, cheating cannot be activated
    val cheating : ScallopOption[Boolean] = toggle() // Default: interactive mode: true, from file: false
    val emacs : ScallopOption[Boolean] = toggle() // Ignored but ProofGeneral needs to give some option to support spaces in paths
    val isabelle : ScallopOption[Boolean] = toggle()
    val session : ScallopOption[String] = opt[String]()
    val file: ScallopOption[String] = trailArg[String](required=false)
    verify()
  }

  def checkJavaVersion() : Unit = {
    val version = System.getProperty("java.version")
//    println(version)
    val major = version.split("\\.")(0).toInt
//    println(major)
    if (major < 11) {
      System.err.println(s"\n\nRequiring at least Java version 11, got $version")
      System.exit(1)
    }
  }

  def main(args: Array[String]): Unit = {
    checkJavaVersion()

    val conf = new CLIConf(args)

    if (conf.session.isSupplied && !conf.isabelle.isSupplied) {
      System.err.println("Option --session only supported in combination with --isabelle")
      sys.exit(1)
    }

    IsabelleX.checkIsabelleHome()

    if (conf.build.getOrElse(false)) {
      val isabelle = new IsabelleX(IsabelleX.defaultSetup)
      isabelle.dispose()
    } else if (conf.isabelle.getOrElse(false)) {
      var setup = IsabelleX.defaultSetup
      val files = conf.file.toOption.toList.map(Path.of(_:String))
      val dir = files.headOption.map(_.getParent).getOrElse(Paths.get("")).toAbsolutePath
      if (Files.exists(dir.resolve("ROOT")) || Files.exists(dir.resolve("ROOTS")))
        setup = setup.copy(sessionRoots = setup.sessionRoots.appended(dir))
      if (conf.session.isSupplied)
        setup = setup.copy(logic = conf.session())
      Isabelle.jedit(setup, files)
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
      Toplevel.main(cheating = conf.cheating.getOrElse(true), allowMultilineCommands = !conf.emacs.getOrElse(false))
  }
}
