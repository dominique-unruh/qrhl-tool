package qrhl.toplevel

import java.io._
import java.nio.charset.StandardCharsets
import java.nio.file.Path

import hashedcomputation.filesystem
import de.unruh.isabelle.control.IsabelleException
import hashedcomputation.filesystem.{Directory, DirectorySnapshot, FileSnapshot, OutdatedSnapshotException}
import qrhl.CurrentFS
import qrhl.toplevel.Toplevel.CommandOrString
import sourcecode.Text.generate

import scala.collection.mutable
//import org.eclipse.jgit.diff.HashedSequenceComparator
import org.jline.reader.LineReaderBuilder
import org.jline.terminal.TerminalBuilder
import org.jline.terminal.impl.DumbTerminal
import org.log4s
import qrhl.isabellex.IsabelleX
import qrhl.toplevel.Toplevel.{ReadLine, logger}
import qrhl.{State, UserException, Utils}

import scala.io.StdIn
import scala.util.matching.Regex
import org.apache.commons.codec.binary.Hex

/** Not thread safe */
class Toplevel private(initialState : State, fsSnapshot: CurrentFS = null) {
  def state = currentState

  //  val initialState: default.Hashed[State] = Hashed(_initialState, default.hash(getClass.descriptorString))
//  def dispose(): Unit = {
//    if (state.hasIsabelle) state.isabelle.isabelle.dispose()
//    states = null
//  }

  private val rootDirectory : Directory = if (fsSnapshot!=null) null else {
    val rootPath = Path.of("").toAbsolutePath.getRoot
    Directory(rootPath, partial = true)
  }

//  implicit var currentFS : CurrentFS =
//    if (fsSnapshot!=null) fsSnapshot else {
//      val snapshot = rootDirectory.snapshot()
//      new CurrentFS(snapshot, rootDirectory.path)
//    }

//  def isabelle: IsabelleX = state.isabelle.isabelle

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

          str.append(line).append(' ') // linebreaks are translated into ' ', that way lines read from the file are the same as lines send by ProofGeneral

          if (Toplevel.commandEnd.findFirstIn(line).isDefined)
            return Toplevel.commandEnd.replaceAllIn(str.toString, "")
          first = false
      }
    }

    "" // unreachable
  }

  /** List of (cmdString, position) */
  private val commands = mutable.ArrayDeque[CommandOrString]()

  private var previousFS = null : DirectorySnapshot

  def computeState() : State = {
    while (true) {
      implicit val currentFS: CurrentFS =
        if (fsSnapshot != null) fsSnapshot else CurrentFS(rootDirectory)

      if (previousFS != null && previousFS != currentFS.directory) {
        println("Some files changed. Replaying all affected commands.")
        previousFS = currentFS.directory
      }

      try {
        var state = initialState
        for (command <- commands)
          try {
            val cmd = command.parse(state)
            state = commandAct(cmd, state)
          } catch {
            case e: UserException => e.setPosition(command.position); throw e
            case e: IsabelleException => throw UserException(e, command.position)
          }
        println(state.lastOutput)
        return state
      } catch {
        case _: OutdatedSnapshotException if rootDirectory != null =>
      }
    }
    throw new AssertionError("Unreachable code")
  }

  private def commandAct(command: Command, state: State)(implicit currentFS: CurrentFS) : State =
    command match {
      case includeCommand : IncludeCommand =>
        val stringWriter = new StringWriter()
        implicit val writer: PrintWriter = new PrintWriter(stringWriter)
        val newState = state.include(includeCommand.file)
        writer.close()
        newState.setLastOutput(stringWriter.toString)
      case cmd : IsabelleCommand =>
        val newState = state.loadIsabelle(cmd.thy)
        newState.setLastOutput("Isabelle loaded.")
      case _ =>
        val newState = command.actString(state)
//        println(newState.lastOutput)
        newState
    }

/*  private def commandActRetry(commandString: String, position: String, command: Command, state: State): State = {
    assert(rootDirectory!=null)
    try {
      commandAct(command, state)
    } catch {
      case _ : OutdatedSnapshotException =>
        var success = false
        println("Files changed. Replaying all affected commands.")
        while (!success)
          try {
            currentFS = CurrentFS(rootDirectory)
            var newStates = Nil : List[(String,String,State)]
            var state = null : State
            for ((str, pos, oldState) <- states.reverse) {
              if (str == null) { // initial state
                state = oldState
                newStates = (null, null, state) :: newStates
              } else {
                val cmd = parseCommand(state, str, pos)
                state = commandAct(cmd, state)
                newStates = (str, pos, state) :: newStates
              }
            }
            val cmd = parseCommand(state, commandString, position)
            state = commandAct(cmd, state)
            states = (commandString, position, state) :: newStates
            success = true
          } catch {
            case _ : OutdatedSnapshotException =>
          }

    }
  }*/

/*  /** Executes a single command. */
  private def execCmd(cmdString:String, cmd:Command, position: => String) : Unit = {
//    warnIfFilesChanged()
    try {
      cmd match {
        case UndoCommand(n) =>
          if (n >= states.length)
            throw UserException(s"Cannot undo $n steps (only ${states.length-1} steps performed so far)")
//          assert(n < states.length)
          val isabelleLoaded = state.value.hasIsabelle
          states = states.drop(n)
          println("Undo...")
        case _ =>
          val newState =
            if (fsSnapshot!=null)
              commandAct(cmd, state)
            else
              commandActRetry(cmdString, position, cmd, state)
          states = (cmdString, position, newState) :: states
      }
    } catch {
      case e: UserException => e.setPosition(position); throw e
      case e: IsabelleException => throw UserException(e,position)
    }

    //    logger.debug(s"State hash: ${state.hash}")
    println(state.value)
  }

  /** Returns the current state of the toplevel */
  def state: State = states.head*/

/*  private def parseCommand(state: State, cmdStr: String, position: String) = {
    try {
      state.value.parseCommand(cmdStr)
    } catch {
      case e: UserException => e.setPosition(position); throw e
      case e: IsabelleException => throw UserException(e,position)
    }
  }*/

  private var currentState : State = initialState


  def execCmd(string: String): Unit =
    execCmd(CommandOrString.Str(string, "<no position>"))
  def execCmd(command: Command): Unit =
    execCmd(CommandOrString.Cmd(command, "<no position>"))

  /** Executes a single command. The command must be given without a final ".". */
  def execCmd(cmd:CommandOrString) : Unit = {
    cmd.undo match {
      case Some(undo) =>
        if (undo > commands.length)
          throw UserException(s"Cannot undo $undo steps (only ${commands.length} steps performed so far)")
        println("Undo...\n")
        commands.trimEnd(undo)
        currentState = computeState()
      case _ => // Not an undo command
        commands.append(cmd)
        currentState = computeState()
    }
  }

  def run(script: String): Unit = {
    run(new ReadLine.Str(script))
  }

  def run(script: Path): Unit = {
    //    val reader = new InputStreamReader(new FileInputStream(script.toFile), StandardCharsets.UTF_8)
    //    println("Toplevel.run",script,script.toAbsolutePath.normalize.getParent)
    val readLine = new Toplevel.ReadLine.File(script)
    val directory = script.toAbsolutePath.normalize.getParent
    execCmd(CommandOrString.Cmd(ChangeDirectoryCommand(directory), readLine.position))
    run(readLine)
  }

  def run(script: FileSnapshot, path: Path): Unit = {
    val readLine = new Toplevel.ReadLine.FileSnapshot(script, path)
    val directory = path.toAbsolutePath.normalize.getParent
    execCmd(CommandOrString.Cmd(ChangeDirectoryCommand(directory), readLine.position))
    run(readLine)
  }


  def runWithErrorHandler(script: Path, abortOnError:Boolean): Boolean = {
    val readLine = new Toplevel.ReadLine.File(script)
    val directory = script.toAbsolutePath.normalize.getParent
    execCmd(CommandOrString.Cmd(ChangeDirectoryCommand(directory), readLine.position))
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
        execCmd(CommandOrString.Str(cmdStr, readLine.position))
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
        execCmd(CommandOrString.Str(cmdStr, readLine.position))
      } catch {
        case e:UserException =>
          println(s"[ERROR] ${e.positionMessage}")
          if (abortOnError) return false
        case e : Throwable =>
          println("[ERROR] [INTERNAL ERROR!!!]")
          val stringWriter = new StringWriter()
          val printWriter = new PrintWriter(stringWriter)
          e.printStackTrace(printWriter)
          printWriter.flush()
          // Making sure there are no *** in the string as this confuses ProofGeneral (*** is the marker for out of band messages)
          val msg = stringWriter.toString.replaceAll("""\*\*+""", "**")
          print(msg)
          if (abortOnError) return false
      }
    }
    assert(false) // unreachable
    false
  }
}

object Toplevel {

  // hashing still works if nothing changed inside the included file but comments?
//  private val commandActComputation : default.Function[(Command,State), State] = default.createFunction {
//    case Hashed.Value((command, state)) => command.actString(state)
//  }

  private val commandEnd: Regex = """\.\s*$""".r
  private val commentRegex = """^\s*#.*$""".r

  private val logger = log4s.getLogger

  /** Runs the interactive toplevel from the terminal (with interactive readline). */
  def runFromTerminal(cheating:Boolean) : Toplevel = {
    val toplevel = Toplevel.makeToplevel(cheating=cheating)
    toplevel.runWithErrorHandler(new ReadLine.Terminal)
    toplevel
  }

  def makeToplevelFromState(state: State, currentFS: CurrentFS) : Toplevel =
    new Toplevel(state, currentFS)

  def makeToplevel(cheating: Boolean) : Toplevel = {
    val state = State.empty(cheating = cheating)
    new Toplevel(state)
  }

  abstract class ReadLine {
    def readline(prompt:String) : String
//    def printPosition() : Unit
    def position : String
  }
  object ReadLine {
    class FileSnapshot(file: filesystem.FileSnapshot, path: Path) extends ReadLine {
      private val reader =
        new LineNumberReader(new InputStreamReader(file.inputStream(), StandardCharsets.UTF_8))
      override def readline(prompt: String): String = reader.readLine()
      //      override def printPosition(): Unit = println(s"At $position:")
      override def position: String = s"$path:${reader.getLineNumber}"
    }
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

  sealed trait CommandOrString {
    def parse(state: State): Command
    val position: String
    def undo: Option[Int]
  }
  object CommandOrString {
    final case class Cmd(command: Command, position: String) extends CommandOrString {
      override def parse(state: State): Command = command
      override def undo: Option[Int] = None
    }
    final case class Str(string: String, position: String) extends CommandOrString {
      override def parse(state: State): Command =
        state.parseCommand(string)
      override def undo: Option[Int] =
        Parser.parseAll(Parser.undo, string) match {
          case Parser.Success(n, _) => Some(n)
          case _ => None
        }
    }
  }
}
