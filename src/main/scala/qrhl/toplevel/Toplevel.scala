package qrhl.toplevel

import java.io._
import java.nio.charset.StandardCharsets
import java.nio.file.Path
import hashedcomputation.{Element, Fingerprint, Hash, Hashable, HashedFunction, HashedPromise, NestedElement, Tuple3Element1, Tuple3Element2, Tuple3Element3, filesystem}
import de.unruh.isabelle.control.IsabelleException
import hashedcomputation.filesystem.{Directory, DirectorySnapshot, FileSnapshot, FingerprintedDirectorySnapshot, OutdatedSnapshotException}
import qrhl.CurrentFS
import qrhl.toplevel.Toplevel.CommandOrString
import sourcecode.Text.generate

import scala.collection.mutable
import scala.concurrent.Future
import scala.util.control.Breaks.{break, breakable}
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

// TODO: remove all the "XXX" methods

/** Not thread safe */
class Toplevel private(initialState : State) {
  private var currentState : State = initialState
  /** List of (cmdString, position) */
  private val commands = mutable.ArrayDeque[CommandOrString]()
  private var previousFS = null : DirectorySnapshot
  private val rootDirectory : Directory = {
    val rootPath = Path.of("").toAbsolutePath.getRoot
    Directory(rootPath, partial = true)
  }
  private var filesChanged = false

  def state: State = currentState

  //  val initialState: default.Hashed[State] = Hashed(_initialState, default.hash(getClass.descriptorString))
//  def dispose(): Unit = {
//    if (state.hasIsabelle) state.isabelle.isabelle.dispose()
//    states = null
//  }


//  implicit var currentFS : CurrentFS =
//    if (fsSnapshot!=null) fsSnapshot else {
//      val snapshot = rootDirectory.snapshot()
//      new CurrentFS(snapshot, rootDirectory.path)
//    }

//  def isabelle: IsabelleX = state.isabelle.isabelle

  def computeState() : State = {
    val currentFS: CurrentFS = CurrentFS(rootDirectory.path, FingerprintedDirectorySnapshot(rootDirectory))

    if (filesChanged) {
      println("Some files changed. Replaying all affected commands.")
      filesChanged = false
    }

    try {
      val state = Toplevel.computeStateFromCommands(initialState, commands.toSeq, currentFS)
      println(state.lastOutput)
      state
    } catch {
      case _: OutdatedSnapshotException if rootDirectory != null =>
        filesChanged = true
        computeState()
    }
  }

/*  private val commandActFunction: HashedFunction[(Command, State, CurrentFS), State] = {
    type T = (Command,State,CurrentFS)
    new HashedFunction[T, State] {
    override def compute(input: (Command, State, CurrentFS)):
    Future[(State, Fingerprint[(Command, State, CurrentFS)])] = Future {

      val (cmd, state, currentFS) = input
      val currentFSfp = currentFS.fingerprinted
      val fingerprinter = currentFSfp.directory.newFingerprinter

      val newState = commandAct(cmd, state)(currentFSfp)

      val entry1 = Fingerprint.Entry[T, Command](new Tuple3Element1, input)
      val entry2 = Fingerprint.Entry[T, State](new Tuple3Element2, input)
      val entry3a = Fingerprint.Entry[T, Path](NestedElement[T,CurrentFS,Path](new Tuple3Element3, CurrentFSElementRoot), input)
      val entry3b = Fingerprint.Entry[T, DirectorySnapshot](
        NestedElement(new Tuple3Element3, CurrentFSElementDir), fingerprinter.fingerprint())
      val fingerprint = Fingerprint(Hashable.hash(input), Some(List(entry1, entry2, entry3a, entry3b)))

    }
    override def hash: Hash[this.type] = Hash.randomHash()
  }
  }*/

/*  private def commandAct(command: Command, state: State)(implicit currentFS: CurrentFS) : State = {
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
        newState
    }
  }*/


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
    val readLine = new Toplevel.ReadLine.File(script)
    val directory = script.toAbsolutePath.normalize.getParent
    execCmd(CommandOrString.Cmd(ChangeDirectoryCommand(directory), readLine.position))
    run(readLine)
  }

  def XXXrun(script: FileSnapshot, path: Path): Unit = {
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
        val cmdStr = Toplevel.readCommand(readLine)
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
        val cmdStr = Toplevel.readCommand(readLine)
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
  private val commandEnd: Regex = """\.\s*$""".r
  private val commentRegex = """^\s*#.*$""".r

  private val logger = log4s.getLogger

  /** Runs the interactive toplevel from the terminal (with interactive readline). */
  def runFromTerminal(cheating:Boolean) : Toplevel = {
    val toplevel = Toplevel.makeToplevel(cheating=cheating)
    toplevel.runWithErrorHandler(new ReadLine.Terminal)
    toplevel
  }

  def makeToplevelFromState(state: State) : Toplevel =
    new Toplevel(state)

  def makeToplevel(cheating: Boolean) : Toplevel = {
    val state = State.empty(cheating = cheating)
    new Toplevel(state)
  }

  abstract class ReadLine {
    def readline(prompt:String) : String
    def position : String
  }
  object ReadLine {
    class FileSnapshot(file: filesystem.FileSnapshot, path: Path) extends ReadLine {
      private val reader =
        new LineNumberReader(new InputStreamReader(file.inputStream(), StandardCharsets.UTF_8))
      override def readline(prompt: String): String = reader.readLine()
      override def position: String = s"$path:${reader.getLineNumber}"
    }
    class File(path: Path) extends ReadLine {
      private val reader = new LineNumberReader(new InputStreamReader(new FileInputStream(path.toFile), StandardCharsets.UTF_8))
      override def readline(prompt: String): String = reader.readLine()
      override def position: String = s"$path:${reader.getLineNumber}"
    }
    class Str(string: String) extends ReadLine {
      private val reader = new BufferedReader(new StringReader(string))
      override def readline(prompt: String): String = reader.readLine()
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

  def computeStateFromReadline(initialState: State, readLine: ReadLine, currentFS: CurrentFS): State = {
    val commands = mutable.ArrayDeque[CommandOrString]()
    breakable {
      while (true) {
        val cmdStr = readCommand(readLine)
        if (cmdStr == null) break()
        commands.append(CommandOrString.Str(cmdStr, readLine.position))
      }
    }
    computeStateFromCommands(initialState, commands.toSeq, currentFS)
  }

  def computeStateFromFileContent(initialState: State, path: Path, fileContent: FileSnapshot, currentFS: CurrentFS): State =
    computeStateFromReadline(initialState: State, new ReadLine.FileSnapshot(fileContent, path), currentFS)

  def computeStateFromCommands(initialState: State, commands: Seq[CommandOrString], currentFS: CurrentFS): State = {
    var state = initialState
    implicit val _currentFS: CurrentFS = currentFS
    for (command <- commands)
      try {
        val cmd = command.parse(state)
        state = cmd match {
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
            val newState = cmd.actString(state)
            newState
        }
      } catch {
        case e: UserException => e.setPosition(command.position); throw e
        case e: IsabelleException => throw UserException(e, command.position)
      }
    state
  }

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

}
