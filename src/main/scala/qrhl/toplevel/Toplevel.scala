package qrhl.toplevel

import java.io._
import java.nio.charset.StandardCharsets
import java.nio.file.Path

import info.hupel.isabelle.ProverResult
import org.jline.reader.LineReaderBuilder
import org.jline.terminal.TerminalBuilder
import org.jline.terminal.impl.DumbTerminal
import org.log4s
import qrhl.isabelle.Isabelle
import qrhl.toplevel.Toplevel.{ReadLine, logger}
import qrhl.{State, UserException}

import scala.io.StdIn
import scala.util.matching.Regex

/** Not thread safe */
class Toplevel private(initialState : State) {
//  def dispose(): Unit = {
//    if (state.hasIsabelle) state.isabelle.isabelle.dispose()
//    states = null
//  }

  def isabelle: Isabelle = state.isabelle.isabelle

  /** Reads one command from the input. The last line of the command must end with ".".
    * Comment lines (starting with whitespace + #) are skipped.
    * @param readLine command for reading lines from the input, invoked with the prompt to show
    * @return the command (without the "."), null on EOF
    * */
  private def readCommand(readLine : ReadLine): String = {
    val str = new StringBuilder()
    var first = true
    while (true) {
      //      val line = StdIn.readLine("qrhl> ")
      val line =
        try {
          readLine.readline(if (first) "\nqrhl> " else "\n...> ")
        } catch {
          case _: org.jline.reader.EndOfFileException =>
            null;
          case _: org.jline.reader.UserInterruptException =>
            println("Aborted.")
            sys.exit(1)
        }

      line match {
        case Toplevel.commentRegex(_*) =>
        case _ =>

          if (line == null) {
            val str2 = str.toString()
            if (str2.trim == "") return null
            return str2
          }

          str.append(line).append('\n')

          if (Toplevel.commandEnd.findFirstIn(line).isDefined)
            return Toplevel.commandEnd.replaceAllIn(str.toString, "")
          first = false
      }
    }

    "" // unreachable
  }


  private var states : List[State] = List(initialState)

  /** Executes a single command. */
  def execCmd(cmd:Command, position: => String) : Unit = {
    state.filesChanged match {
      case Nil =>
      case files =>
        println(s"***** [WARNING] Some files changed (${files.mkString(", ")}).\n***** Please retract the current proof script. (C-c C-r or Proof-General->Retract Buffer)\n\n")
    }

    try {
      cmd match {
        case UndoCommand(n) =>
          assert(n < states.length)
          val isabelleLoaded = state.hasIsabelle
          states = states.drop(n)
          // If state after undo has no Isabelle, run GC to give the system the chance to finalize a possibly loaded Isabelle
          if (!state.hasIsabelle && isabelleLoaded)
            System.gc()
        case _ =>
          val newState = cmd.act(state)
          states = newState :: states
      }
    } catch {
      case e:UserException => e.setPosition(position); throw e
      case e: ProverResult.Failure => throw UserException(e,position)
    }

    println(state)
  }

  /** Returns the current state of the toplevel */
  def state: State = states.head

  /** Executes a single command. The command must be given without a final ".". */
  def execCmd(cmd:String, position: => String = "<string>") : Unit = {
    val cmd2 = try {
      state.parseCommand(cmd)
    } catch {
      case e:UserException => e.setPosition(position); throw e
      case e:ProverResult.Failure => throw UserException(e,position)
    }
    execCmd(cmd2, position)
  }

  def run(script: String): Unit = {
    run(new ReadLine.Str(script))
  }

  def run(script: Path): Unit = {
    //    val reader = new InputStreamReader(new FileInputStream(script.toFile), StandardCharsets.UTF_8)
    //    println("Toplevel.run",script,script.toAbsolutePath.normalize.getParent)
    val readLine = new Toplevel.ReadLine.File(script)
    execCmd(ChangeDirectoryCommand(script.toAbsolutePath.normalize.getParent), readLine.position)
    run(readLine)
  }

  def runWithErrorHandler(script: Path, abortOnError:Boolean): Boolean = {
    val readLine = new Toplevel.ReadLine.File(script)
    execCmd(ChangeDirectoryCommand(script.toAbsolutePath.normalize.getParent), readLine.position)
    runWithErrorHandler(readLine, abortOnError=abortOnError)
  }

  /** Runs a sequence of commands. Each command must be delimited by "." at the end of a line.
    * A line starting with # (and possibly whitespace before that) is ignored (comment).
    * @param readLine command for reading lines from the input, invoked with the prompt to show
    */
  def run(readLine : ReadLine): Unit = {
    while (true) {
        val cmdStr = readCommand(readLine)
        if (cmdStr==null) { println("EOF"); return; }
        execCmd(cmdStr, readLine.position)
    }
  }

  /** Runs a sequence of commands. Each command must be delimited by "." at the end of a line.
    * Errors (such as UserException's and asserts) are caught and printed as error messages,
    * and the commands producing the errors are ignored.
    * @param readLine command for reading lines from the input, invoked with the prompt to show
    */
  def runWithErrorHandler(readLine : ReadLine, abortOnError:Boolean=false): Boolean = {
    while (true) {
      try {
        val cmdStr = readCommand(readLine)
        if (cmdStr==null) { println("EOF"); return true; }
        execCmd(cmdStr, readLine.position)
      } catch {
        case e:UserException =>
          println(s"[ERROR] ${e.positionMessage}")
          if (abortOnError) return false
        case e : Throwable =>
          println("[ERROR] [INTERNAL ERROR!!!]")
          e.printStackTrace(System.out)
          if (abortOnError) return false
      }
    }
    assert(false) // unreachable
    false
  }
}

object Toplevel {
  private val commandEnd: Regex = """\.\s*$""".r
  private val commentRegex = """^\s*\#.*$""".r

  private val logger = log4s.getLogger

  /** Runs the interactive toplevel from the terminal (with interactive readline). */
  def runFromTerminal(cheating:Boolean) : Toplevel = {
    val toplevel = Toplevel.makeToplevel(cheating=cheating)
    toplevel.runWithErrorHandler(new ReadLine.Terminal)
    toplevel
  }

  def makeToplevelWithTheory(theory:Seq[String]=Nil) : Toplevel = {
    val state = State.empty(cheating = false).loadIsabelle(theory)
    new Toplevel(state)
  }

  def makeToplevelFromState(state:State) : Toplevel =
    new Toplevel(state)

  def makeToplevel(cheating:Boolean) : Toplevel = {
    val state = State.empty(cheating = cheating)
    new Toplevel(state)
  }

  abstract class ReadLine {
    def readline(prompt:String) : String
//    def printPosition() : Unit
    def position : String
  }
  object ReadLine {
    class File(path: Path) extends ReadLine {
      private val reader = new LineNumberReader(new InputStreamReader(new FileInputStream(path.toFile), StandardCharsets.UTF_8))
      override def readline(prompt: String): String = reader.readLine()
//      override def printPosition(): Unit = println(s"At $position:")
      override def position: String = s"$path:${reader.getLineNumber}"
    }
    class Str(string: String) extends ReadLine {
      private val reader = new BufferedReader(new StringReader(string))
      override def readline(prompt: String): String = reader.readLine()
//      override def printPosition(): Unit = Toplevel.logger.debug(s"Skipping printPosition (uninteresting): $position")
      override def position: String = "<string>"
    }
    class Terminal extends ReadLine {
      private val terminal = TerminalBuilder.terminal()
      private val readlineFunction: String => String = {
        if (terminal.isInstanceOf[DumbTerminal]) {
          println("Using dumb readline instead of JLine.");
          { p: String => StdIn.readLine(p) } // JLine's DumbTerminal echoes lines, so we don't use JLine in this case
        } else {
          val lineReader = LineReaderBuilder.builder().terminal(terminal).build()
          lineReader.readLine
        }
      }
      override def readline(prompt: String): String = readlineFunction(prompt)
      override def position: String = "<terminal>"
//      override def printPosition(): Unit = Toplevel.logger.debug(s"Skipping printPosition (uninteresting): $position")
    }
  }

  def main(cheating:Boolean): Unit = {
    try
      runFromTerminal(cheating)
    catch {
      case e:Throwable => // we need to catch and print, otherwise the sys.exit below gobbles up the exception
        e.printStackTrace()
        sys.exit(1)
    } finally
      sys.exit(0) // otherwise the Isabelle process blocks termination
  }
}
