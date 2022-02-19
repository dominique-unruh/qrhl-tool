package qrhl.toplevel

import java.io._
import java.nio.charset.StandardCharsets
import java.nio.file.Path
import hashedcomputation.{Element, Fingerprint, Hash, HashTag, Hashable, HashedFunction, HashedPromise, HashedValue, NestedElement, Tuple3Element1, Tuple3Element2, Tuple3Element3, filesystem}
import de.unruh.isabelle.control.IsabelleException
import hashedcomputation.Fingerprint.Entry
import hashedcomputation.filesystem.{Directory, DirectorySnapshot, FileSnapshot, FingerprintedDirectorySnapshot, OutdatedSnapshotException, RootsDirectory}
import qrhl.toplevel.Toplevel.CommandOrString
import scalaz.Scalaz.ToIdOps
import sourcecode.Text.generate

import scala.collection.mutable
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Future}
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
import hashedcomputation.Implicits._

/** Not thread safe */
class Toplevel private(initialState : State) {
  private var currentState : State = initialState
  /** Reversed list of commands */
  private var commands : List[CommandOrString] = Nil
  private var previousFS = null : DirectorySnapshot
  private val rootDirectory : RootsDirectory = RootsDirectory()
//  private var filesChanged = false

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

  def computeState(commands: Seq[CommandOrString]) : State = {
    val fs: FingerprintedDirectorySnapshot = FingerprintedDirectorySnapshot(rootDirectory)

//    if (filesChanged) {
//      println("Some files changed. Replaying all affected commands.")
//      filesChanged = false
//    }

    try {
      val state = Toplevel.computeStateFromCommands(initialState, commands.toSeq, fs)
      println(state.lastOutput)
      state
    } catch {
      case _: OutdatedSnapshotException if rootDirectory != null =>
        computeState(commands)
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
        // Don't store the new command list unless the "computeState()" below succeeds
        // Otherwise ProofGeneral would get out of sync
        val newCommands = commands.drop(undo)
        currentState = computeState(newCommands.reverse)
        commands = newCommands
        println(currentState)
      case _ => // Not an undo command
        // Don't store the new command list unless the "computeState()" below succeeds
        // Otherwise ProofGeneral would get out of sync
        val newCommands = cmd :: commands
        currentState = computeState(newCommands.reverse)
        commands = newCommands
        println(currentState)
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

/*  def run(script: FileSnapshot, path: Path): Unit = {
    val readLine = new Toplevel.ReadLine.FileSnapshot(script, path)
    val directory = path.toAbsolutePath.normalize.getParent
    execCmd(CommandOrString.Cmd(ChangeDirectoryCommand(directory), readLine.position))
    run(readLine)
  }*/

  def runWithErrorHandler(script: Path, abortOnError:Boolean): Boolean = {
    val readLine = new Toplevel.ReadLine.File(script)
    val directory = script.toAbsolutePath.normalize.getParent
    execCmd(CommandOrString.Cmd(ChangeDirectoryCommand(directory), readLine.position))
    runWithErrorHandler(readLine, abortOnError=abortOnError)
  }

  /** Checks that there is no pending proof.
   * If there is none, a success message is printed.
   * @throws UserException if there is a pending proof */
  private def checkFinished() : Unit = {
    if (state.currentLemma.isDefined) {
      if (state.goal.isProved)
        throw UserException("Unfinished proof at end of file. (You forgot the qed command.)")
      else
        throw UserException("Unfinished proof at end of file. (Pending subgoals.)")
    }
    println("\n\nAll proofs processed successfully.")
  }

  /** Runs a sequence of commands. Each command must be delimited by "." at the end of a line.
    * A line starting with # (and possibly whitespace before that) is ignored (comment).
    * @param readLine command for reading lines from the input, invoked with the prompt to show
    */
  def run(readLine : ReadLine): Unit = {
    while (true) {
        val cmdStr = Toplevel.readCommand(readLine)
        if (cmdStr==null) { checkFinished(); return }
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
        if (cmdStr==null) { checkFinished(); return true }
        execCmd(CommandOrString.Str(cmdStr, readLine.position))
      } catch {
        case e : UserException =>
          println(s"[ERROR] ${e.positionMessage}")
          if (e.log != null && !e.log.isBlank) {
            println("\nThe full output of the command follows:\n")
            println(e.log)
          }
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
  private val commandEnd: Regex = """\.(\s*$|\s+)""".r
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
    def readline(prompt: String) : String
    def position : String
    val unprocessed: StringBuilder = new StringBuilder()
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
      private val terminal = TerminalBuilder.builder().dumb(true).build()
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

  sealed trait CommandOrString extends HashedValue {
    def parse(state: State): Command
    val position: String
    def undo: Option[Int]
  }

  object CommandOrString {
    final case class Cmd(command: Command, position: String) extends CommandOrString {
      override def parse(state: State): Command = command
      override def undo: Option[Int] = None
      override def hash: Hash[Cmd.this.type] = HashTag()(command.hash, Hashable.hash(position))
    }

    private val cachedParseCommand = HashedFunction.apply[(State,String),Command] {
      case (state, string) => state.parseCommand(string)
    }

    final case class Str(string: String, position: String) extends CommandOrString {
      override def parse(state: State): Command =
        Await.result(HashedPromise(cachedParseCommand, (state, string)).getOutput,
          Duration.Inf)

      override def undo: Option[Int] =
        Parser.parseAll(Parser.undo, string) match {
          case Parser.Success(n, _) => Some(n)
          case _ => None
        }

      override def hash: Hash[Str.this.type] = HashTag()(Hashable.hash(string), Hashable.hash(position))
    }
  }

  def computeStateFromReadline(initialState: State, readLine: ReadLine, fs: FingerprintedDirectorySnapshot): State = {
    val commands = mutable.ArrayDeque[CommandOrString]()
    breakable {
      while (true) {
        val cmdStr = readCommand(readLine)
        if (cmdStr == null) break()
        commands.append(CommandOrString.Str(cmdStr, readLine.position))
      }
    }
    computeStateFromCommands(initialState, commands.toSeq, fs)
  }

  /** path must be absolute */
  def computeStateFromFileContent(initialState: State, path: Path, fileContent: FileSnapshot, fs: FingerprintedDirectorySnapshot): State =
    computeStateFromReadline(initialState.changeDirectory(path.getParent),
      new ReadLine.FileSnapshot(fileContent, path), fs)

  private val cachedApplyCommandToState = HashedFunction.fingerprintedComputation[(Command, State, DirectorySnapshot), State] {
    case (command, state, directory) =>
      logger.debug(s"Evaluating $command")
      type T = (Command, State, DirectorySnapshot)
      implicit val fs: FingerprintedDirectorySnapshot = FingerprintedDirectorySnapshot(directory)
      val newState = command match {
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

      val fsFingerprint = fs.fingerprintBuilder.fingerprint
      val fingerprint = Fingerprint(Hashable.hash((command, state, directory)), Some(Seq(
        Entry[T,Command](Tuple3Element1(), Fingerprint(command.hash)),
        Entry[T,State](Tuple3Element2(), Fingerprint(state.hash)),
        Entry[T,DirectorySnapshot](Tuple3Element3(), fsFingerprint)
      )))

//      logger.debug("Fingerprint: " + fingerprint)

      (newState, fingerprint)
  }

  def applyCommandToState(command: CommandOrString, state: State, fs: FingerprintedDirectorySnapshot): State = {
    val cmd = command.parse(state)

    val unsafeFS = fs.fingerprintBuilder.unsafeUnderlyingValue
    val future = HashedPromise(cachedApplyCommandToState, (cmd, state, unsafeFS)).get
//      cachedApplyCommandToState.compute((cmd, state, unsafeFS))
    val (result, fingerprint) = Await.result(future, Duration.Inf)
    def projectEntry[C](entry: Entry[(Command, State, DirectorySnapshot), C]):
          Option[Seq[Entry[DirectorySnapshot, _]]] = entry.element match {
      case _ : Tuple3Element1[_,_,_] => Some(Nil)
      case _ : Tuple3Element2[_,_,_] => Some(Nil)
      case _ : Tuple3Element3[_,_,DirectorySnapshot] =>
        // DirectorySnapshot =:= C
        val fps: Option[Seq[Entry[C, _]]] = entry.fingerprint.fingerprints
        fps.asInstanceOf[Option[Seq[Entry[DirectorySnapshot,_]]]]
      case NestedElement(_: Tuple3Element1[_,_,_], _) => Some(Nil)
      case NestedElement(_: Tuple3Element2[_,_,_], _) => Some(Nil)
      case NestedElement(_: Tuple3Element3[_,_,DirectorySnapshot],
                         inner : Element[DirectorySnapshot, C]) =>
        Some(Seq(Entry(inner, entry.fingerprint)))
      case _ => None
    }

    val fsFingerprint = fingerprint.project(unsafeFS.hash, projectEntry(_))
    fs.fingerprintBuilder.access(fsFingerprint)
    result
  }

  def computeStateFromCommands(initialState: State, commands: Seq[CommandOrString], fs: FingerprintedDirectorySnapshot): State = {
    var state = initialState
    for (command <- commands)
      try {
        state = applyCommandToState(command, state, fs)
      } catch {
        case e: UserException => e.setPosition(command.position); throw e
        case e: IsabelleException => throw UserException(e, command.position)
      }
    state
  }

  private def stripComment(line: String): String = line match {
    case Toplevel.commentRegex(_*) => ""
    case _ => line
  }

  private def clearBuilderIfWhite(str: StringBuilder): Unit = {
    if (str.forall(_.isWhitespace)) str.clear()
  }

  private def scanCommand(string: String): Option[(String, Int)] = {
    Parser.parse(Parser.focus, string) match {
      case Parser.Success(_, next) =>
        Some((string.substring(0, next.offset), next.offset))
      case Parser.NoSuccess(_, _) =>
        Parser.parse(Parser.commandSpan, string) match {
          case Parser.Success(endOffset, next) =>
            Some((string.substring(0, endOffset), next.offset))
          case Parser.NoSuccess(_, _) =>
            None
        }
    }
  }

  /** Reads one command from the input. The last line of the command must end with ".".
   * Comment lines (starting with whitespace + #) are skipped.
   *
   * @param readLine command for reading lines from the input, invoked with the prompt to show
   * @return the command (without the "."), null on EOF
   * */
  private def readCommand(readLine : ReadLine): String = {
    val str = readLine.unprocessed
    while (true) {
      clearBuilderIfWhite(str)

      scanCommand(str.toString()) match {
        case Some((command, len)) =>
          logger.debug(s"scanCommand -> ($command, $len)")
          str.delete(0, len)
          return command
        case None =>
      }

      val line =
        try {
          readLine.readline(if (str.isEmpty) "\nqrhl> " else "\n...> ")
        } catch {
          case _: org.jline.reader.EndOfFileException => null
          case _: org.jline.reader.UserInterruptException =>
            println("Aborted.")
            sys.exit(1)
        }

      if (line == null) {
        if (str.isEmpty)
          return null;
        else {
          println("EOF in the middle of a command")
          sys.exit(1)
        }
      }

      str.append(stripComment(line))
    }

    throw new AssertionError("unreachable code")
  }
}
