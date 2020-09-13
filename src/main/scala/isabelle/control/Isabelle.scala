package isabelle.control

import java.io.{BufferedReader, BufferedWriter, DataInputStream, DataOutputStream, EOFException, FileInputStream, FileOutputStream, IOException, InputStream, InputStreamReader, OutputStreamWriter}
import java.lang
import java.lang.ref.Cleaner
import java.nio.charset.StandardCharsets
import java.nio.file.{FileSystemNotFoundException, Files, Path, Paths}
import java.util.concurrent.{ArrayBlockingQueue, BlockingQueue, ConcurrentHashMap, ConcurrentLinkedQueue}

import isabelle.control.Isabelle.Setup
import isabelle.mlvalue.MLValue
import isabelle.pure.Term
import org.apache.commons.io.FileUtils
import org.log4s
import org.log4s.{Debug, LogLevel, Logger, Warn}

import scala.annotation.tailrec
import scala.collection.JavaConverters.collectionAsScalaIterableConverter
import scala.collection.mutable.ListBuffer
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future, Promise}
import scala.io.Source
import scala.sys.process.{Process, ProcessLogger}
import scala.util.{Failure, Success, Try}

/**
  * A running instance of Isabelle.
  *
  * The Isabelle process is initialized with some ML code that allows this class to remote control Isabelle. In more detail:
  *
  * The Isabelle process maintains a map from IDs to values (the "object store").
  * Those values can be of any type (e.g., integers, terms, functions, etc.).
  * (How this works in a strongly typed language such as ML is described below.)
  * The Isabelle class has functions to operate on the values in the object store
  * (e.g., creating new objects, retrieving the value of an object, performing operations on objects).
  *
  * The operations provided by this class are very lowlevel. For more convenient and type-safe operations on
  * values in the object store, see [[MLValue]].
  *
  * Operations on objects are asynchronous and return futures.
  *
  * On the Scala side, the IDs of objects are represented by the class [[isabelle.control.Isabelle.ID]].
  * These IDs ensure garbage collection – if an ID is not referenced any more on the Scala side, it will
  * be removed from the object store in the Isabelle process, too.
  *
  * To be able to store objects of different types in the object store, even though ML does not support subtyping,
  * we make use of the fact that all exceptions share the same ML type `exn`. The object store stores only values of
  * type `exn`. To store, e.g., integers, we define an exception `exception E_Int of int`. Then for an integer `i`,
  * `E_Int i` is an exception that can be stored in the object store. We can convert the exception back to an integer
  * using the function `fn E_Int i => i` that uses pattern matching. (This will raise `Match` if the given exception is
  * does not contain an integer. This way we achieve dynamic typing of our object store.) The following exceptions are
  * predefined in structure `Control_Isabelle`:
  * {{{
  * exception E_Function of exn -> exn
  * exception E_Int of int
  * exception E_String of string
  * exception E_Pair of exn * exn
  * }}}
  * (That structure also exports functions `store` and `handleLines` which are for internal use only
  * and must not be used in the ML code.)
  *
  * Note that some of the exception again refer to the exn type, e.g., `E_Pair`. Thus, to store a pair of integers,
  * we use the term `E_Pair (E_Int 1, E_Int 2)`.
  *
  * New exceptions for storing other types can be defined at runtime using [[executeMLCode]].
  *
  * @param setup Configuration object that specifies the path of the Isabelle binary etc. See [[Setup]]. This also
  *              specifies with Isabelle heap to load.
  * @param build Whether to build the Isabelle heap before running Isabelle. If false, the heap will never be
  *              built. (This means changes in the Isabelle theories will not be reflected. And if the heap was never
  *              built, the Isabelle process fails.) If true, the Isabelle build command will be invoked. That
  *              command automatically checks for changed dependencies but may add a noticable delay even if
  *              the heap was already built.
  */

class Isabelle(val setup: Setup, build: Boolean = false) {
  import Isabelle._

  private val sendQueue : BlockingQueue[(DataOutputStream => Unit, Try[Data] => Unit)] = new ArrayBlockingQueue(1000)
  private val callbacks : ConcurrentHashMap[Long, Try[Data] => Unit] = new ConcurrentHashMap()
  private val cleaner = Cleaner.create()

  // Must be Integer, not Int, because ConcurrentLinkedList uses null to indicate that it is empty
  private val garbageQueue = new ConcurrentLinkedQueue[java.lang.Long]()

  private def garbageCollect(stream: DataOutputStream) : Boolean = {
    //    println("Checking for garbage")
    if (garbageQueue.peek() == null)
      false
    else {
      val buffer = ListBuffer[Data]()

      @tailrec def drain(): Unit = garbageQueue.poll() match {
        case null =>
        case obj =>
          buffer.addOne(DInt(obj))
          drain()
      }

      drain()
      logger.debug(s"Sending GC command to Isabelle, ${buffer.size} freed objects")
      stream.writeByte(8)
      writeData(stream, DTree(buffer.toSeq :_*))
      true
    }
  }

  private def processQueue(inFifo: Path) : Unit = {
    logger.debug("Process queue thread started")
    val stream = new DataOutputStream(new FileOutputStream(inFifo.toFile))
    var count = 0

    def sendLine(line: DataOutputStream => Unit, callback: Try[Data] => Unit): Unit = {
      if (callback != null)
        callbacks.put(count, callback)
      line(stream)
      count += 1
    }

    @tailrec @inline
    def drainQueue() : Unit = {
      val elem = sendQueue.poll()
      if (elem!=null) {
        val (line,callback) = elem
        sendLine(line,callback)
        drainQueue()
      }
    }

    while (true) {
      val (line,callback) = sendQueue.take()
      sendLine(line, callback)
      drainQueue()
      if (garbageCollect(stream))
        count += 1
      stream.flush()
    }
  }

  private def readString(stream: DataInputStream): String = {
    val len = stream.readInt()
    val bytes = stream.readNBytes(len)
    new String(bytes, StandardCharsets.US_ASCII)
  }

  private def writeString(stream: DataOutputStream, str: String): Unit = {
    val bytes = str.getBytes(StandardCharsets.US_ASCII)
    stream.writeInt(bytes.length)
//    logger.debug(s"length: ${bytes.length}, content: ${new String(bytes)}")
    stream.write(bytes)
  }

  private def writeData(stream: DataOutputStream, data: Data): Unit = data match {
    case DInt(i) => stream.writeByte(1); stream.writeLong(i)
    case DString(s) => stream.writeByte(2); writeString(stream, s)
    case DTree(list@_*) =>
      stream.writeByte(3)
      stream.writeLong(list.length)
      for (d <- list)
        writeData(stream, d)
    case DObject(id) =>
      stream.writeByte(4)
      stream.writeLong(id.id)
  }

  private def readData(stream: DataInputStream): Data = {
    stream.readByte() match {
      case 1 => DInt(stream.readLong())
      case 2 => DString(readString(stream))
      case 3 =>
        val len = stream.readLong()
        val list = ListBuffer[Data]()
        for (_ <- 1L to len)
          list.addOne(readData(stream))
        DTree(list.toSeq:_*)
      case 4 =>
        val id = stream.readLong()
        DObject(new ID(id, this))
    }
  }


  /** Message format:
    *
    * int|1b|data - success response for command #int
    * int|2b|string - failure response for command #int
    *
    * 1b,2b,...: byte literals
    *
    * int64: 64 msb-first signed integer
    *
    * data: binary representation of [[Data]]:
    *   1b|int64 - DInt
    *   2b|string - DString (must be ASCII)
    *   3b|int64|data|data|... - DTree (int64 = # of data)
    *   4b|int64 - DObject (responsibility for GC is on Scala side)
    *
    * string: int32|bytes
    *
    * */
  private def parseIsabelle(outFifo: Path) : Unit = {
    val output = new DataInputStream(new FileInputStream(outFifo.toFile))
    try
    while (true) {
      val seq = output.readLong()
      val answerType = output.readByte()
      val callback = callbacks.remove(seq)
//      logger.debug(s"Seq: $seq, type: $answerType, callback: $callback")
      answerType match {
        case 1 =>
          val payload = readData(output)
          callback(Success(payload))
        case 2 =>
          val msg = readString(output)
          callback(Failure(IsabelleException(msg)))
      }
    } catch {
      case _ : EOFException =>
    }
  }

  //noinspection SameParameterValue
  private def filePathFromResource(name: String, tmpDir: Path): Path = {
    val url = getClass.getResource(name)
    assert(url != null, name)
    try
      Path.of(url.toURI)
    catch {
      case _ : FileSystemNotFoundException =>
        val tmpPath = tmpDir.resolve(name.split('/').last)
        val tmpFile = tmpPath.toFile
        tmpFile.deleteOnExit()
        FileUtils.copyURLToFile(url, tmpFile)
        tmpPath
    }
  }

  private def startProcess() : java.lang.Process = {
    def wd = setup.workingDirectory
    /** Path to absolute string, interpreted relative to wd */
    def str(path: Path) = wd.resolve(path).toAbsolutePath.toString

    val tempDir = Files.createTempDirectory("isabellecontrol").toAbsolutePath
    tempDir.toFile.deleteOnExit()
    logger.debug(s"Temp directory: $tempDir")

    val isabelleBinary = setup.isabelleHome.resolve("bin").resolve("isabelle")
    val mlFile = filePathFromResource("control_isabelle.ml", tempDir)

    assert(setup.userDir.forall(_.endsWith(".isabelle")))


    val inputPipe = tempDir.resolve("in-fifo").toAbsolutePath
    inputPipe.toFile.deleteOnExit()
    val outputPipe = tempDir.resolve("out-fifo").toAbsolutePath
    outputPipe.toFile.deleteOnExit()
    if (Process(List("mkfifo", inputPipe.toString)).! != 0)
      throw new IOException(s"Cannot create fifo $inputPipe")
    if (Process(List("mkfifo", outputPipe.toString)).! != 0)
      throw new IOException(s"Cannot create fifo $outputPipe")


    val cmd = ListBuffer[String]()

    cmd += str(isabelleBinary) += "process"
    cmd += "-l" += setup.logic

    // TODO: escape pipe name for ML
    cmd += "-e" += s"""val (inputPipeName,outputPipeName) = ("$inputPipe","$outputPipe")"""

    cmd += "-f" += mlFile.toAbsolutePath.toString

    cmd += "-e" += "Control_Isabelle.handleLines()"

    for (root <- setup.sessionRoots)
      cmd += "-d" += str(root)

    logger.debug(s"Cmd line: ${cmd.mkString(" ")}")

    val processBuilder = new java.lang.ProcessBuilder(cmd.toSeq :_*)
    processBuilder.directory(wd.toAbsolutePath.toFile)
    for (userDir <- setup.userDir)
      processBuilder.environment.put("USER_HOME", str(userDir.getParent))

    val processQueueThread = new Thread("Send to Isabelle") {
      override def run(): Unit = processQueue(inputPipe) }
    processQueueThread.setDaemon(true)
    processQueueThread.start()

    val parseIsabelleThread = new Thread("Read from Isabelle") {
      override def run(): Unit = parseIsabelle(outputPipe) }
    parseIsabelleThread.setDaemon(true)
    parseIsabelleThread.start()

    val process = processBuilder.start()

    logStream(process.getErrorStream, Warn) // stderr
    logStream(process.getInputStream, Debug) // stdout

    process
  }

  if (build) buildSession(setup)
  private val process: lang.Process = startProcess()

  /** Returns whether the Isabelle process has been destroyed (via [[destroy]]) */
  def isDestroyed: Boolean = destroyed

  @volatile private var destroyed = false
  /** Kills the running Isabelle process.
    * After this, no more operations on values in the object store are possible.
    * Futures corresponding to already running computations will throw an [[IsabelleDestroyedException]].
    */
  def destroy(): Unit = {
    destroyed = true
    garbageQueue.clear()
    process.destroy()

    def callCallback(cb: Try[Data] => Unit): Unit =
      cb(Failure(IsabelleDestroyedException("Isabelle process has been destroyed")))

    for ((_,cb) <- sendQueue.asScala)
      callCallback(cb)
    sendQueue.clear()

    for (cb <- callbacks.values.asScala)
      callCallback(cb)
  }

  private def send(str: DataOutputStream => Unit, callback: Try[Data] => Unit) : Unit = {
    if (destroyed)
      throw new IllegalStateException("Isabelle instance has been destroyed")
    sendQueue.put((str,callback))
  }

  private def intStringToID(data: Data) : ID = data match {
    case DInt(int) => new ID(int, this)
  }


  /** Executes the ML code `ml` in the Isabelle process.
    * Definitions made in `ml` affect the global Isabelle name space.
    * This is intended mostly for defining new types.
    * To create values (e.g., if `ml` is the code of a function that should be executed),
    * preferably use [[storeValue]] which creates anonymous values in the object store.
    * The ML code is executed in a context where the structure `Control_Isabelle` is not opened
    * (i.e., you have to write `Control_Isabelle.E_Int` instead of `E_Int`).
    *
    * @return A future that completes when the code was executed.
    *         (Or throws an [[IsabelleControllerException]] if the ML code compilation/execution fails.)
    */
  def executeMLCode(ml : String) : Future[Unit] = {
    val promise : Promise[Unit] = Promise()
    logger.debug(s"Executing ML code: $ml")
    send({ stream => stream.writeByte(1); writeString(stream, ml) }, { result => promise.complete(result.map(_ => ())) })
    promise.future
  }

  /** Like [[executeMLCode]] but waits for the code to be executed before returning. */
  def executeMLCodeNow(ml : String): Unit = Await.result(executeMLCode(ml), Duration.Inf)

  /** Executes the ML expression `ml` in the Isabelle process.
    * The expression must be of ML type `exn`.
    * The result of evaluating the expression is added to the object store.
    * The ML code is executed in a context where the structure `Control_Isabelle` is opened
    * (i.e., you can write `E_Int` instead of `Control_Isabelle.E_Int`).
    *
    * Example: `storeValue("exception E_Term of term")` (this is actually done by [[Term]]).
    *
    * In code that is supposed to support multiple instances of Isabelle, it can be cumbersome to
    * keep track in which instances a given ML code fragment was already executed. See [[OperationCollection]]
    * for a helper class to facilitate that.
    *
    * @return Future that contains an ID referencing the result in the object store.
    *         (Or throws an [[IsabelleControllerException]] if the ML code compilation/execution fails.)
    */
  def storeValue(ml : String): Future[ID] = {
    val promise : Promise[ID] = Promise()
//    logger.debug(s"Compiling ML value: $ml")
    send({ stream => stream.writeByte(4); writeString(stream, ml) },
      { result => promise.complete(result.map(intStringToID)) })
    promise.future
  }

  /** Stores `i` in the object store. (I.e., an object `E_Int i` will be added.)
    * Equivalent to `storeValue(i.toString)` but does not invoke the ML compiler (faster).
    *
    * @return A future containing the ID in the object store.
    */
    @deprecated
  def storeLong(i: Long): Future[ID] = {
    val promise : Promise[ID] = Promise()
    send({ stream => stream.writeByte(3); stream.writeLong(i) },
      { result => promise.complete(result.map(intStringToID)) })
    promise.future
  }

  /** Stores `s` in the object store. (I.e., an object `E_String i` will be added.)
    *
    * Strings are required to be ASCII strings.
    *
    * @return A future containing the ID in the object store.
    */
  def storeString(str: String): Future[ID] = {
    val promise : Promise[ID] = Promise()
    send({ stream => stream.writeByte(2); writeString(stream, str) },
      { result => promise.complete(result.map(intStringToID)) })
    promise.future
  }

/*
  /** Given two objects `a`,`b` in the object store, create a pair `E_Pair (a,b)`.
    *
    * @return A future containing the ID of the pair in the object store.
    */
  @deprecated
  def makePair(a: ID, b: ID) : Future[ID] = {
    val promise : Promise[ID] = Promise()
    send({ stream => stream.writeByte(9); stream.writeLong(a.id); stream.writeLong(b.id) },
      { result => promise.complete(result.map(intStringToID)) })
    promise.future
  }
*/

/*
  /** Given an object `E_Pair (a,b)` in the object store, store
    * `a` and `b` as objects and return their IDs
    *
    * @return A future containing the IDs of `a` and `b`
    */
  @deprecated
  def splitPair(pair: ID) : Future[(ID,ID)] = {
    val promise : Promise[(ID,ID)] = Promise()
    send({ stream => stream.writeByte(10); stream.writeLong(pair.id) },
      { result => promise.complete(result.map {
        case DTree(a,b) => (intStringToID(a), intStringToID(b)) } ) } )
    promise.future
  }
*/

  /** // TODO Not true any more
    *
    * If `f` and `x` refer to objects in the object store,
    * and `f` is of the form `E_Function f'`
    * compute `f' x` and store the result in the object store.
    *
    * @return A future containing the ID of the result (or throwing an exception
    *         if the evaluation `f` is not `E_Function f'` or `f' x` throws an exception in ML)
    */
  def applyFunction(f: ID, x: Data): Future[Data] = {
    val promise: Promise[Data] = Promise()
    send({ stream => stream.writeByte(7); stream.writeLong(f.id); writeData(stream,x) },
      { result => promise.complete(result) })
    promise.future
  }

  def applyFunction(f: Future[ID], x: Data)(implicit ec: ExecutionContext) : Future[Data] =
    for (f2 <- f; fx <- applyFunction(f2, x)) yield fx

  @deprecated
  def applyFunctionOld(f: ID, x: ID)(implicit ec: ExecutionContext): Future[ID] = {
    applyFunction(f, DObject(x)).map { case DObject(id) => id }
  }

  /** Retrieves the integer `i` referenced by `id` in the object store.
    *
    * Does not check whether the ML integer (which can be unbounded) fits into a Long
    *
    * @return Future that contains `i`. (Or throws an [[IsabelleException]]
    *         if `id` does not refer to an `E_Int i` object.)
    */
  @deprecated
  def retrieveLong(id: ID): Future[Long] = {
    val promise: Promise[Long] = Promise()
    send({ stream => stream.writeByte(5); stream.writeLong(id.id) },
      { result => promise.complete(result.map { case DInt(int) => int }) })
    promise.future
  }

  /** Retrieves the string `s` referenced by `id` in the object store.
    *
    * Note: Currently, newlines will be replaced by spaces in the retrieved string.
    * This will change in the future.
    *
    * @return Future that contains `s`. (Or throws an [[IsabelleException]]
    *         if `id` does not refer to an `E_String s` object.)
    */
  @deprecated
  def retrieveString(id: ID): Future[String] = {
    val promise: Promise[String] = Promise()
    send({ stream => stream.writeByte(6); stream.writeLong(id.id) },
      { result => promise.complete(result.map { case DString(str) => str }) })
    promise.future
  }

  def retrieveData(id: ID): Future[Data] = {
    val promise: Promise[Data] = Promise()
    send({ stream => stream.writeByte(11); stream.writeLong(id.id) },
      { result => promise.complete(result) })
    promise.future
  }

  def storeData(data: Data): Future[ID] = {
    val promise : Promise[ID] = Promise()
    send({ stream => stream.writeByte(12); writeData(stream, data) },
      { result => promise.complete(result.map(intStringToID)) })
    promise.future
  }
}

object Isabelle {
  private val logger = log4s.getLogger

  private def logStream(stream: InputStream, level: LogLevel) : Unit = {
    val log = logger(level)
    val thread = new Thread(s"Isabelle output logger, $level") {
      override def run(): Unit = {
        new BufferedReader(new InputStreamReader(stream)).lines().forEach(line => logger.debug(line))
      }
    }
    thread.setDaemon(true)
    thread.start()
  }

  /** An ID referencing an object in the object store (see the description of [[Isabelle]]).
    * If this ID is not referenced any more, the referenced object will be garbage collected
    * in the Isabelle process, too.
    */
  final class ID private[control] (private[control] val id: Long, isabelle: Isabelle) {
    isabelle.cleaner.register(this, new IDCleaner(id, isabelle))

    override def equals(obj: Any): Boolean = obj match {
      case obj: ID => id == obj.id
      case _ => false
    }
  }
  private final class IDCleaner(id: Long, isabelle: Isabelle) extends Runnable {
    def run(): Unit = isabelle.garbageQueue.add(id)
  }

  /** Configuration for initializing an [[Isabelle]] instance.
    *
    * (The fields of this class are documents in the source code. I am not sure why they do not occur in the
    * generated API doc.)
    *
    * @param workingDirectory Working directory in which the Isabelle process should run. (Default:
    *                         working directory of the Scala process.) All other paths described
    *                         below are interpreted relative to `workingDirectory` (unless they are absolute).
    * @param isabelleHome Path to the Isabelle distribution
    * @param logic Heap image to load in Isabelle (e.g., `HOL`, `HOL-Analysis`, etc.)
    * @param sessionRoots Additional session directories in which Isabelle will search for sessions
    *                     (must contain `ROOT` files and optionally `ROOTS` files, see the Isabelle system manual).
    *                     Default: no additional session directories
    * @param userDir User configuration directory for Isabelle. Must end in `/.isabelle` if provided.
    *                None (default) means to let Isabelle chose the default location.
    *                Here Isabelle stores user configuration and heap images (unless
    *                the location of the heap images is configured differently, see the Isabelle system manual)
    */
  case class Setup(workingDirectory : Path = Paths.get(""),
                   isabelleHome : Path,
                   logic : String = "HOL",
                   sessionRoots : Seq[Path] = Nil,
                   userDir : Option[Path] = None)

  /** Runs the Isabelle build process to build the session heap image `setup.logic`
    *
    * This is done automatically by the constructors of [[Isabelle]] unless `build=false`.
    *
    * @param setup Configuration of Isabelle.
    */
  def buildSession(setup: Setup) : Unit = {
    def wd = setup.workingDirectory
    /** Path to absolute string, interpreted relative to wd */
    def str(path: Path) = wd.resolve(path).toAbsolutePath.toString
    val isabelleBinary = setup.isabelleHome.resolve("bin").resolve("isabelle")
    val cmd = ListBuffer[String]()

    cmd += str(isabelleBinary) += "build"
    cmd += "-b" // Build heap image

    for (root <- setup.sessionRoots)
      cmd += "-d" += str(root)

    cmd += setup.logic

    logger.debug(s"Cmd line: ${cmd.mkString(" ")}")

    val extraEnv =
      for (userDir <- setup.userDir.toList)
        yield ("USER_HOME", str(userDir.getParent))

    val processBuilder = scala.sys.process.Process(cmd.toSeq, wd.toAbsolutePath.toFile, extraEnv :_*)
    val errors = ListBuffer[String]()
    if (0 != processBuilder.!(ProcessLogger(line => logger.debug(s"Isabelle build: $line"),
      {line => errors.append(line); logger.warn(s"Isabelle build: $line")})))
      throw IsabelleBuildException(s"Isabelle build for session ${setup.logic} failed", errors.toList)
  }

  /**
    * Starts Isabelle/jEdit (interactive editing of theories) with the given Isabelle configuration.
    *
    * @param setup Isabelle configuration
    * @param files Files to open in jEdit
    */
  def jedit(setup: Setup, files: Seq[Path]) : Unit = {
    def wd = setup.workingDirectory
    /** Path to absolute string, interpreted relative to wd */
    def str(path: Path) = wd.resolve(path).toAbsolutePath.toString
    val isabelleBinary = setup.isabelleHome.resolve("bin").resolve("isabelle")
    val cmd = ListBuffer[String]()

    cmd += str(isabelleBinary) += "jedit"

    for (root <- setup.sessionRoots)
      cmd += "-d" += str(root)

    cmd += "-l" += setup.logic

    cmd += "--"
    cmd ++= files.map { _.toAbsolutePath.toString }

    logger.debug(s"Cmd line: ${cmd.mkString(" ")}")

    val extraEnv =
      for (userDir <- setup.userDir.toList)
        yield ("USER_HOME", str(userDir.getParent))

    val processBuilder = scala.sys.process.Process(cmd.toSeq, wd.toAbsolutePath.toFile, extraEnv :_*)
    val errors = ListBuffer[String]()
    if (0 != processBuilder.!(ProcessLogger(line => logger.debug(s"Isabelle build: $line"),
      {line => errors.append(line); logger.warn(s"Isabelle build: $line")})))
      throw IsabelleBuildException(s"Isabelle build for session ${setup.logic} failed", errors.toList)
  }

  sealed trait Data
  final case class DInt(int: Long) extends Data
  final case class DString(string: String) extends Data
  final case class DTree(list: Data*) extends Data
  final case class DObject(id: ID) extends Data
}

/** Ancestor of all exceptions specific to [[Isabelle]] */
abstract class IsabelleControllerException(message: String) extends IOException(message)

/** Thrown if an operation cannot be executed because [[Isabelle.destroy()]] has already been invoked. */
case class IsabelleDestroyedException(message: String) extends IsabelleControllerException(message)
/** Thrown if the build process of Isabelle fails */
case class IsabelleBuildException(message: String, errors: List[String])
  extends IsabelleControllerException(if (errors.nonEmpty) message + ": " + errors.last else message)
/** Thrown in case of an error in the ML process (ML compilation errors, exceptions thrown by ML code) */
case class IsabelleException(message: String) extends IsabelleControllerException(message)


