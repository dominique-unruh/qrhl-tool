package qrhl.toplevel

import java.io.{BufferedReader, FileReader, Reader, StringReader}
import java.nio.file.Path

import info.hupel.isabelle.Operation.ProverException
import org.jline.reader.LineReaderBuilder
import org.jline.terminal.TerminalBuilder
import org.jline.terminal.impl.DumbTerminal
import qrhl.isabelle.Isabelle
import qrhl.{State, UserException}

import scala.io.StdIn
import scala.util.matching.Regex

/** Not thread safe */
class Toplevel(initialState : State = State.empty) {
  def dispose(): Unit = {
    if (state.hasIsabelle) state.isabelle.isabelle.dispose()
    states = null
  }

  def isabelle: Isabelle = state.isabelle.isabelle

  /** Reads one command from the input. The last line of the command must end with ".".
    * Comment lines (starting with whitespace + #) are skipped.
    * @param readLine command for reading lines from the input, invoked with the prompt to show
    * @return the command (without the "."), null on EOF
    * */
  private def readCommand(readLine : String => String): String = {
    val str = new StringBuilder()
    var first = true
    while (true) {
      //      val line = StdIn.readLine("qrhl> ")
      val line =
        try {
//          lineReader.readLine(if (first) "\nqrhl> " else "\n...> ")
          readLine(if (first) "\nqrhl> " else "\n...> ")
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
  def execCmd(cmd:Command) : Unit = {
    state.filesChanged match {
      case Nil =>
      case files => println(s"***** [WARNING] Some files changed (${files.mkString(", ")}). Best restart the prover. *****\n\n")
    }

    cmd match {
      case UndoCommand(n) =>
        assert(n < states.length)
        val isabelleLoaded = state.hasIsabelle
        states = states.drop(n)
        // If state after undo has no Isabelle, run GC to give the system the chance to finalize a possibly loaded Isabelle
        if (!state.hasIsabelle && isabelleLoaded)
          System.gc()
      case _ =>
        val newState = cmd.act(states.head)
        states = newState :: states
    }
    println(states.head)
  }

  /** Returns the current state of the toplevel */
  def state: State = states.head

  /** Executes a single command. The command must be given without a final ".". */
  def execCmd(cmd:String) : Unit = {
    val cmd2 = state.parseCommand(cmd)
    execCmd(cmd2)
  }

  /** Runs a sequence of commands. Each command must be delimited by "." at the end of a line. */
  def run(script: String): Unit = {
    val reader = new StringReader(script)
    run(reader)
  }

  def run(script: Path): Unit = {
    val reader = new FileReader(script.toFile)
//    println("Toplevel.run",script,script.toAbsolutePath.normalize.getParent)
    execCmd(ChangeDirectoryCommand(script.toAbsolutePath.normalize.getParent))
    run(reader)
  }

  def run(script: Reader) : Unit = {
    val reader = new BufferedReader(script)
    def readLine(prompt:String) = {
      val line = reader.readLine()
      println("> "+line)
      line
    }
    run(readLine _)
  }
  
  /** Runs a sequence of commands. Each command must be delimited by "." at the end of a line.
    * A line starting with # (and possibly whitespace before that) is ignored (comment).
    * @param readLine command for reading lines from the input, invoked with the prompt to show
    */
  def run(readLine : String => String): Unit = {
    while (true) {
        val cmdStr = readCommand(readLine)
        if (cmdStr==null) { println("EOF"); return; }
        execCmd(cmdStr)
    }
  }

  /** Runs a sequence of commands. Each command must be delimited by "." at the end of a line.
    * Errors (such as UserException's and asserts) are caught and printed as error messages,
    * and the commands producing the errors are ignored.
    * @param readLine command for reading lines from the input, invoked with the prompt to show
    */
  def runWithErrorHandler(readLine : String => String): Unit = {
    while (true) {
      try {
        val cmdStr = readCommand(readLine)
        if (cmdStr==null) { println("EOF"); return; }
        execCmd(cmdStr)
      } catch {
        case UserException(msg) =>
          println("[ERROR] "+msg)
        case e: ProverException =>
          val msg = Isabelle.symbolsToUnicode(e.fullMessage)
          println("[ERROR] (in Isabelle) "+msg)
        case e : Throwable =>
          println("[ERROR] [INTERNAL ERROR!!!]")
          e.printStackTrace(System.out)
      }
    }
  }
}

object Toplevel {
  private val commandEnd: Regex = """\.\s*$""".r
  private val commentRegex = """^\s*\#.*$""".r

  /** Runs the interactive toplevel from the terminal (with interactive readline). */
  def runFromTerminal() : Toplevel = {
    val terminal = TerminalBuilder.terminal()
    val readLine : String => String = {
      if (terminal.isInstanceOf[DumbTerminal]) {
        println("Using dumb readline instead of JLine.");
        { (p: String) => StdIn.readLine(p) } // JLine's DumbTerminal echoes lines, so we don't use JLine in this case
      } else {
        val lineReader = LineReaderBuilder.builder().terminal(terminal).build()
        lineReader.readLine
      }
    }
    val toplevel = new Toplevel()
    toplevel.runWithErrorHandler(readLine)
    toplevel
  }

  def makeToplevel(isabelle:Isabelle, theory:Option[String]=None) : Toplevel = {
    val state = State.empty.loadIsabelle(isabelle,theory)
    new Toplevel(state)
  }

  def main(): Unit = {
    try
      runFromTerminal()
    catch {
      case e:Throwable => // we need to catch and print, otherwise the sys.exit below gobbles up the exception
        e.printStackTrace()
        sys.exit(1)
    } finally
      sys.exit(0) // otherwise the Isabelle process blocks termination
  }
}
