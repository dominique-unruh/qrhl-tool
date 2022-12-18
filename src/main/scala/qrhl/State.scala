package qrhl

import java.io.PrintWriter
import java.nio.file.attribute.FileTime
import java.nio.file.{Files, NoSuchFileException, Path, Paths}
import java.util
import org.log4s
import isabellex.{IsabelleX, RichTerm}
import qrhl.logic._
import qrhl.toplevel.{Command, Parser, ParserContext, Toplevel}
import de.unruh.isabelle.control
import control.IsabelleMLException
import qrhl.State.logger

import scala.collection.mutable
import hashedcomputation.{Hash, HashTag, Hashable, HashedValue, RawHash}
import org.apache.commons.codec.binary.Hex
import IsabelleX.{ContextX, globalIsabelle => GIsabelle}
import GIsabelle.Ops
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.Typ
import hashedcomputation.filesystem.FingerprintedDirectorySnapshot
import scalaz.Scalaz.ToIdOps

// Implicits
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import qrhl.isabellex.MLValueConverters.Implicits._
import scala.concurrent.ExecutionContext.Implicits._
import GIsabelle.isabelleControl
import hashedcomputation.Implicits._
import qrhl.isabellex.Implicits._


trait Tactic extends HashedValue {
  def apply(state: State, goal : Subgoal)(implicit output: PrintWriter) : List[Subgoal]
}

class UserException private (private val msg:String, private var _position:String=null, private var _log:String=null) extends RuntimeException(msg) {
  /** Sets the position if no position set yet. Does nothing if `position == null`. */
  def setPosition(position:String): Unit =
    if (_position==null)
      _position = position

  /** Sets the log if no log set yet. Does nothing if `log == null`. */
  def setLog(log:String): Unit =
    if (_log==null)
      _log = log

  def position : String = _position
  def log : String = _log
  def positionMessage : String =
    if (position != null && position != "<terminal>")
      s"$position: $msg"
    else
      msg
}
object UserException {
  private val logger = log4s.getLogger

  def apply(msg: String) = new UserException(msg)
  def apply(e: IsabelleMLException, position: String = null, log: String = null): UserException = {
//    logger.debug(s"Failing operation: operation ${e.operation} with input ${e.input}")
    val e2 = UserException("(in Isabelle) "+IsabelleX.symbols.symbolsToUnicode(e.getMessage))
    e2.setPosition(position)
    e2.setLog(log)
    e2
  }
}

/** A path together with a last-modification time and content hash. */
class FileTimeStamp(val file:Path) {
  import FileTimeStamp.logger

  private var time = FileTimeStamp.getLastModifiedTime(file)
  private val hash = Utils.hashFile(file)
  /** Returns whether the file (content) has changed since the FileTimeStamp was created.
   * Uses the last modification time as a shortcut – the assumption is that
   * the content will be unmodified if the time is */
  def changed : Boolean =
    if (time==FileTimeStamp.getLastModifiedTime(file))
      false
    else {
      val newHash = Utils.hashFile(file)
      if (util.Arrays.equals(hash,newHash)) {
        time = FileTimeStamp.getLastModifiedTime(file)
        false
      } else {
        logger.debug(s"File change detected: ${Hex.encodeHexString(hash)} -> ${Hex.encodeHexString(newHash)}")
        true
      }
    }

  override def toString: String = s"$file@$time@${Hex.encodeHexString(hash).substring(0,8)}"
}
object FileTimeStamp {
  private val logger = log4s.getLogger
  def getLastModifiedTime(file:Path): FileTime = try
    Files.getLastModifiedTime(file)
  catch {
    case _ : NoSuchFileException => FileTime.fromMillis(-1)
  }
}

class CheatMode private (
                    private val cheatAtAll : Boolean, // whether any cheating should happen at all
                    private val cheatInProof : Boolean, // cheating till the end of the current proof
                    private val cheatInFile : Boolean, // cheating till the end of current file
                    private val inInclude : Boolean // in included file
                    ) extends HashedValue {
//  assert(includeLevel >= 0)
//  def endInclude = new CheatMode(cheatAtAll=cheatAtAll, cheatInProof=cheatInProof, cheatInFile=false, includeLevel=includeLevel-1)
  def endProof = new CheatMode(cheatAtAll=cheatAtAll, cheatInProof=false, cheatInFile=cheatInFile, inInclude=inInclude)
  def cheating: Boolean = cheatAtAll && (cheatInFile || cheatInProof || inInclude)
  def startCheatInProof = new CheatMode(cheatAtAll=cheatAtAll, cheatInProof=true, cheatInFile=cheatInFile, inInclude=inInclude)
  def startCheatInFile = new CheatMode(cheatAtAll=cheatAtAll, cheatInProof=cheatInProof, cheatInFile=true, inInclude=inInclude)
  def startInclude = new CheatMode(cheatAtAll=cheatAtAll, cheatInProof=cheatInProof, cheatInFile=cheatInFile, inInclude=true)
  def stopCheatInFile(inProof:Boolean) = new CheatMode(cheatAtAll=cheatAtAll,
    cheatInProof=cheatInProof || (inProof && cheatInFile),
    cheatInFile=false, inInclude=inInclude)

  override def hash: Hash[CheatMode.this.type] =
    HashTag()(Hashable.hash(cheatAtAll), Hashable.hash(cheatInFile), Hashable.hash(cheatInProof), Hashable.hash(inInclude))
}

object CheatMode {
  def make(cheatAtAll:Boolean): CheatMode = new CheatMode(cheatAtAll=cheatAtAll,false,false,false)
}


class State private (val environment: Environment,
                     val goal: Goal,
                     val currentLemma: Option[(String,RichTerm)],
                     private val _isabelle: Option[IsabelleX.ContextX],
                     private val _isabelleTheory: List[Path],
//                     val dependencies: List[FileTimeStamp],
                     /** Absolute path */
                     val currentDirectory: Path,
                     val cheatMode : CheatMode,
                     val includedFiles : Set[Path],
                     val lastOutput : String,
                     _hash : Hash[State])
    extends HashedValue {
  def applyIsabelleToplevelCommand(command: String): State = {
    if (currentLemma.isDefined)
      throw UserException(s"""Isabelle commands are only possible outside a proof. Maybe you intended to use "isa ${command}."?""")
    val newContext = Ops.applyToplevelCommand(isabelle.context, IsabelleX.symbols.unicodeToSymbols(command)).retrieveNow
    copy(isabelle = Some(new ContextX(isabelle.isabelle, newContext)),
      hash = HashTag()(hash, Hashable.hash(command)))
  }

  def focusOrUnfocus(selector: Option[SubgoalSelector], focusVariant: String): State = {
    if (cheatMode.cheating)
      copy(goal=Goal.empty, hash=HashTag()(hash))
    else if (currentLemma.isEmpty)
      throw UserException("No pending proof")
    else
      copy(goal = goal.focusOrUnfocus(selector, focusVariant),
        hash = HashTag()(hash, Hashable.hash(focusVariant)))
  }


  val hash: Hash[this.type] = _hash.asInstanceOf[Hash[this.type]]

//  private def HashTag()(hash)(implicit file: sourcecode.File, line: sourcecode.Line) : Hash[State] =
//    RawHash.hashString(s"State: $file:$line:${hash.hex}:empty")

//  private def HashTag()(hash,hashes: Hash[Any]*)(implicit file: sourcecode.File, line: sourcecode.Line): Hash[State] =
//    RawHash.hashString(s"State: $file:$line:${hash.hex}:${hashes.map(_.hex).mkString("")}")

//  private def HashTag()(hash,arguments: HashedValue*)(implicit file: sourcecode.File, line: sourcecode.Line): Hash[State] =
//    HashTag()(hash,arguments.map(_.hash) : _*)(file, line)

  def include(file: Path)(implicit output: PrintWriter, fs: FingerprintedDirectorySnapshot): State = {
    output.println("Including file "+file)
    val fullpath = currentDirectory.resolve(file)
//    val relpath = fs.relativize(fullpath)

    logger.debug(s"Including $fullpath")
    if (includedFiles.contains(fullpath)) {
      println(s"Already included $fullpath. Skipping.")
      this
    } else {
      val fileContent = fs.getFile(fullpath).getOrElse { throw UserException(s"File $file not found (relative to $currentDirectory)") }
      val state1 = this.copy(includedFiles = includedFiles + fullpath, cheatMode=cheatMode.startInclude,
        hash = HashTag()(this.hash, fileContent.hash))
      val state2 = Toplevel.computeStateFromFileContent(state1, fullpath, fileContent, fs, allowMultilineCommands = true)
//      val toplevel = Toplevel.makeToplevelFromState(state1, fs)
//      toplevel.run(fileContent, fullpath)
//      val state2 = toplevel.state
      val state3 = state2.copy(
        cheatMode = cheatMode, // restore original cheatMode
        currentDirectory = currentDirectory,  // restore original currentDirectory
        hash = HashTag()(state2.hash))
      state3
    }
  }

  private def setCheatMode(cheatMode: CheatMode): State = copy(cheatMode = cheatMode, hash = HashTag()(hash, Hashable.hash(cheatMode)))
  def cheatInFile: State = setCheatMode(cheatMode.startCheatInFile)
  def cheatInProof: State = setCheatMode(cheatMode.startCheatInProof)
  def stopCheating: State = setCheatMode(cheatMode.stopCheatInFile(currentLemma.isDefined))

  def isabelle: IsabelleX.ContextX = _isabelle match {
    case Some(isa) => isa
    case None => throw UserException(Parser.noIsabelleError)
  }
  def hasIsabelle: Boolean = _isabelle.isDefined

  def qed: State = {
    assert(currentLemma.isDefined)
    assert(goal.isProved)

    val (name,prop) = currentLemma.get
    val isa = if (name!="") _isabelle.map(_.addAssumption(name,prop.isabelleTerm)) else _isabelle
    // TODO: Base this on the state from the beginning of the proof, then the proof interna definitely won't affect the hash
    copy(isabelle=isa, currentLemma=None, cheatMode=cheatMode.endProof,
      hash = HashTag()(hash)
    )
  }

  private def containsDuplicates[A](seq: Seq[A]): Boolean = {
    val seen = new mutable.HashSet[A]()
    for (e <- seq) {
      if (seen.contains(e)) return true
      seen += e
    }
    false
  }

  def declareProgram(name: String, oracles: List[String], program: Block): State = {
    if (containsDuplicates(oracles))
      throw UserException("Oracles "+oracles.mkString(",")+" must not contain duplicates")

    for (x <- program.variablesDirect)
      if (!environment.variableExistsForProg(x))
        throw UserException(s"Undeclared variable $x in program")

    if (_isabelle.isEmpty) throw UserException("Missing isabelle command.")
    if (this.environment.variableExists(name))
      throw UserException(s"Name $name already used for a variable or program.")

    val decl = ConcreteProgramDecl(isabelle.context, environment, name, oracles, program)
    val env1 = environment.declareProgram(decl)
    val isa = decl.declareInIsabelle(_isabelle.get)

//    val isa1 = _isabelle.get.declareVariable(name, if (oracles.isEmpty) Isabelle.programT else Isabelle.oracle_programT)

//    val isa2 = decl.getSimplifierRules.foldLeft(isa1) { (isa,rule) => isa.addAssumption("", rule.isabelleTerm, simplifier = true) }

    logger.debug(s"Program variables: ${env1.programs(name).variablesRecursive}")

    copy(environment = env1, isabelle=Some(isa),
      hash = HashTag()(hash, decl.hash))
  }

  def declareAdversary(name: String, free: Seq[Variable with Nonindexed], inner: Seq[Variable with Nonindexed], written: Seq[Variable with Nonindexed],
                       covered: Seq[Variable with Nonindexed], overwritten: Seq[Variable with Nonindexed], numOracles : Int): State = {
//    val isa1 = _isabelle.get.declareVariable(name,
//      if (numOracles==0) Isabelle.programT else Isabelle.oracle_programT)
    val decl = AbstractProgramDecl(name, free=free.toList,inner=inner.toList,written=written.toList,covered=covered.toList,overwritten=overwritten.toList, numOracles=numOracles)
    val isa = decl.declareInIsabelle(_isabelle.get)
//    val isa2 = decl.getSimplifierRules.foldLeft(isa1) { (isa,rule) => isa.addAssumption("", rule.isabelleTerm, simplifier = true) }
    val env1 = environment.declareProgram(decl)

    logger.debug(s"Program variables: ${env1.programs(name).variablesRecursive}")

    copy(environment = env1, isabelle=Some(isa),
      hash = HashTag()(hash, decl.hash))
  }


  def applyTactic(tactic:Tactic)(implicit output: PrintWriter) : State =
    if (cheatMode.cheating)
      copy(goal=Goal.empty, hash=HashTag()(hash))
    else if (goal.isProved)
      throw UserException("No pending proof")
    else {
      val newGoal = goal.applyTactic(this, tactic)
      copy(goal = newGoal,
        hash=HashTag()(hash, newGoal.hash))
    }

  private def copy(environment:Environment=environment,
                   goal:Goal=goal,
                   isabelle:Option[IsabelleX.ContextX]=_isabelle.map(_.force),
//                   dependencies:List[FileTimeStamp]=dependencies,
                   currentLemma:Option[(String,RichTerm)]=currentLemma,
                   currentDirectory:Path=currentDirectory,
                   cheatMode:CheatMode=cheatMode,
                   isabelleTheory:List[Path]=_isabelleTheory,
                   includedFiles:Set[Path]=includedFiles,
                   lastOutput:String=lastOutput,
                   hash: Hash[State]) : State =
    new State(environment=environment, goal=goal, _isabelle=isabelle, cheatMode=cheatMode,
      currentLemma=currentLemma, currentDirectory=currentDirectory,
      includedFiles=includedFiles, _isabelleTheory=isabelleTheory, lastOutput = lastOutput,
      _hash = hash)

  def changeDirectory(dir:Path): State = {
    assert(dir!=null)
    assert(dir.isAbsolute)
    if (dir==currentDirectory) return this
    if (!Files.isDirectory(dir)) throw UserException(s"Non-existent directory: $dir")
//    if (hasIsabelle) throw UserException("Cannot change directory after loading Isabelle")
    copy(currentDirectory=dir, hash = HashTag()(hash,Hashable.hash(dir)))
  }

  def setLastOutput(output: String): State =
    copy(lastOutput = output, hash = HashTag()(hash,Hashable.hash(output)))

  def openGoal(name:String, goal:Subgoal) : State = this.currentLemma match {
    case None =>
      goal.checkVariablesDeclared(environment)
      copy(goal=Goal(goal), currentLemma=Some((name,goal.toTerm(_isabelle.get))),
        hash = HashTag()(hash,Hashable.hash(name), goal.hash))
    case _ => throw UserException("There is still a pending proof.")
  }

  override def toString: String = if (cheatMode.cheating)
    "In cheat mode."
  else goal.longDescription

  lazy val parserContext: ParserContext = ParserContext(isabelle=_isabelle, environment=environment)

  def parseCommand(str:String): Command = {
    implicit val parserContext: ParserContext = this.parserContext
    Parser.parseAll(Parser.command,str) match {
      case Parser.Success(cmd2,_) => cmd2
      case res @ Parser.NoSuccess(msg, _) =>
        throw UserException(msg)
    }
  }

  /** Parses an expression in shortform. Returns the parsed expression in shortform. */
  def parseExpression(typ:Typ, str:String, indexed:Boolean): Expression = {
    implicit val parserContext: ParserContext = this.parserContext
    Parser.parseAll(Parser.expression(typ, indexed=indexed),str) match {
      case Parser.Success(cmd2,_) => cmd2
      case res @ Parser.NoSuccess(msg, _) =>
        throw UserException(msg)
    }
  }

  /*
    def parseExpressionLongform(typ: Typ, str: String, indexed:Boolean): RichTerm = {
      val shortform = parseExpression(typ, str, indexed = indexed)
      shortform.encodeAsExpression(isabelle, indexed = indexed)
    }
  */

  def parseBlock(str:String): Block = {
    implicit val parserContext: ParserContext = this.parserContext
    Parser.parseAll(Parser.block,str) match {
      case Parser.Success(cmd2,_) => cmd2
      case res @ Parser.NoSuccess(msg, _) =>
        throw UserException(msg)
    }
  }

  def loadIsabelle(theory:Seq[String], session : Option[String])(implicit fs: FingerprintedDirectorySnapshot) : State = {
    assert(currentDirectory.isAbsolute)
    val theoryPath = theory.toList map { thy => currentDirectory.resolve(thy+".thy") }

    // In order to get snapshot exceptions before running Isabelle (saves time)
    for (t <- theoryPath) fs.getFile(t)

    if (_isabelle.isDefined)
      if (theoryPath != _isabelleTheory)
        throw UserException(s"Isabelle loaded twice with different theories: ${if (_isabelleTheory.isEmpty) "none" else _isabelleTheory.mkString(", ")} vs. ${if (theoryPath.isEmpty) "none" else theoryPath.mkString(", ")}")
      else
        return this

    // If currentDirectory (from where we initialize via "isabelle" command) contains ROOT or ROOTS, use it as additional session directory
    val sessionDirectory =
      currentDirectory.toAbsolutePath.normalize
        .into { d =>
          if (fs.getFile(d.resolve("ROOT")).isDefined || fs.getFile(d.resolve("ROOTS")).isDefined)
            Some(d) else None }

    val isabelle = IsabelleX.globalIsabelleWith(sessionDir = sessionDirectory, session = session)
    logger.debug(s"Paths of theories to load: $theoryPath")
    val (ctxt,deps) = isabelle.getQRHLContextWithFiles(theoryPath : _*)
    logger.debug(s"Dependencies of theory ${theory.mkString(", ")}: ${deps.mkString(", ")}")

    for (f <- deps) assert(f.isAbsolute)

//    val relDeps = deps.map(currentFS.relativize)

    // This ensures that even when one .get fails (and updates the Toplevel.rootDirectory), the others are
    // tried to (so all updates happen in one go).
    for (d <- deps) try { fs.getFile(d) } catch { case _ : Throwable => }

    val deps2 = for (file <- deps) yield {
//      val relfile = currentFS.relativize(file)
      val content = fs.getFile(file)
      logger.debug(s"$file -> $content")
      (file, content)
    }

    val newState = copy(isabelle = Some(ctxt), isabelleTheory=theoryPath,
      hash = HashTag()(hash,Hashable.hash(theory.toList), Hashable.hash(deps2)))
    // We declare a quantum variable aux :: infinite by default (for use in equal-tac, for example)
    newState.declareVariable("aux", GIsabelle.infiniteT, quantum = true)
  }

//  def filesChanged : List[Path] = {
//    dependencies.filter(_.changed).map(_.file)
//  }

  private def declare_quantum_variable(isabelle: IsabelleX.ContextX, name: String, typ: Typ, existingVars: Iterable[(String,Typ)]) : IsabelleX.ContextX = {
    val ctxt = Ops.declare_quantum_variable(name, typ, isabelle.context, existingVars.toList).retrieveNow
    new ContextX(isabelle.isabelle, ctxt)
//    isabelle.map(id => isabelle.isabelle.invoke(State.declare_quantum_variable, (name,typ,id)))
  }

  private def declare_classical_variable(isabelle: IsabelleX.ContextX, name: String, typ: Typ, existingVars: Iterable[(String,Typ)]) : IsabelleX.ContextX = {
    val ctxt = Ops.declare_classical_variable(name, typ, isabelle.context, existingVars.toList).retrieveNow
    new ContextX(isabelle.isabelle, ctxt)
//    isabelle.map(id => isabelle.isabelle.invoke(State.declare_classical_variable, (name,typ,id)))
  }

  def declareVariable(name: String, typ: Typ, quantum: Boolean): State = {
    val existingVars =
      for (c <- if (quantum) environment.qVariables.values else environment.cVariables.values)
        yield (c.basename, c.valueTyp)
    val newEnv = environment.declareVariable(name, typ, quantum = quantum)
//      .declareAmbientVariable("var_"+name, typ)
//      .declareAmbientVariable("var_"+Variable.index1(name), typ)
//      .declareAmbientVariable("var_"+Variable.index2(name), typ)
    if (_isabelle.isEmpty) throw UserException("Missing isabelle command.")
    val isa = _isabelle.get
    val newIsa =
      if (quantum)
        declare_quantum_variable(isa, name, typ, existingVars)
      else
        declare_classical_variable(isa, name, typ, existingVars)

    copy(environment = newEnv, isabelle = Some(newIsa),
      hash = HashTag()(hash, RawHash.hashString(name), Hashable.hash(typ), Hashable.hash(quantum)))
  }

  def declareAmbientVariable(name: String, typ: Typ): State = {
    val newEnv = environment.declareAmbientVariable(name, typ)
    if (_isabelle.isEmpty) throw UserException("Missing isabelle command.")
    val isa = _isabelle.get.declareVariable(name, typ)
    copy(environment = newEnv, isabelle = Some(isa),
      hash = HashTag()(hash, RawHash.hashString(name), Hashable.hash(typ)))
  }
}

object State {
  def empty(cheating:Boolean) = new State(environment=Environment.empty, goal=Goal.empty,
    _isabelle=None, _isabelleTheory=null,
//    dependencies=Nil,
    currentLemma=None, currentDirectory=Paths.get("").toAbsolutePath,
    cheatMode=CheatMode.make(cheating), includedFiles=Set.empty,
    lastOutput = "Ready.",
    _hash = HashTag()(Hashable.hash(cheating)))
//  private[State] val defaultIsabelleTheory = "QRHL"

  private val logger = log4s.getLogger
}
