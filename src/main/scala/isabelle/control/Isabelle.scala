package isabelle.control

import java.io.{BufferedInputStream, BufferedOutputStream, BufferedReader, BufferedWriter, FileInputStream, FileOutputStream, IOException, InputStream, InputStreamReader, OutputStreamWriter}
import java.lang
import java.lang.ProcessBuilder.Redirect
import java.lang.ref.Cleaner
import java.net.URL
import java.nio.file.{Files, Path, Paths}
import java.util.concurrent.{ArrayBlockingQueue, BlockingQueue, ConcurrentHashMap, ConcurrentLinkedQueue}

import isabelle.control.Isabelle.Setup
import org.log4s
import org.log4s.{Debug, LogLevel, Warn}

import scala.annotation.tailrec
import scala.collection.JavaConverters.{asScalaIteratorConverter, collectionAsScalaIterableConverter, enumerationAsScalaIteratorConverter}
import scala.collection.mutable.ListBuffer
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future, Promise}
import scala.io.Source
import scala.sys.process.Process
import scala.util.{Failure, Success, Try}

class Isabelle(setup: Setup, build: Boolean = false) {
  import Isabelle._

  private val sendQueue : BlockingQueue[(String, Try[String] => Unit)] = new ArrayBlockingQueue(1000)
  private val callbacks : ConcurrentHashMap[Int, Try[String] => Unit] = new ConcurrentHashMap()
  private val cleaner = Cleaner.create()

  // Must be Integer, not Int, because ConcurrentLinkedList uses null to indicate that it is empty
  private val garbageQueue = new ConcurrentLinkedQueue[Integer]()

  private def garbageCollect() : Option[String] = {
//    println("Checking for garbage")
    @tailrec def drain(objs: List[Int]) : List[Int] = garbageQueue.poll() match {
      case null => objs
      case obj =>
        if (objs.length > 1000) // Since Poly/ML has only a 64KB string size limit, we avoid too long lists of IDs in one go
          obj::objs
        else
          drain(obj::objs)
    }
    val objs = drain(Nil)
    if (objs.nonEmpty)
      Some(s"g${objs.mkString(" ")}\n")
    else
      None
  }

  private def processQueue(inFifo: Path) : Unit = {
    logger.debug("Process queue thread started")
    val stream = new FileOutputStream(inFifo.toFile)
    val writer = new BufferedWriter(new OutputStreamWriter(stream, "ascii"))
    var count = 0

    @tailrec @inline
    def drainQueue() : Unit = {
      val elem = sendQueue.poll()
      if (elem!=null) {
        val (line,callback) = elem
        assert(line.endsWith("\n"), line)
//        logger.debug(s"Writing ${line.trim}")
        if (callback != null)
          callbacks.put(count, callback)
        writer.write(line)
        count += 1
        drainQueue()
      }
    }

    while (true) {
      val (line,callback) = sendQueue.take()
      assert(line.endsWith("\n"), line)
//      logger.debug(s"Writing! ${line.trim}")
      if (callback != null)
        callbacks.put(count, callback)
      writer.write(line)
      count += 1
      drainQueue()
      for (cmd <- garbageCollect()) {
        logger.debug("Sending GC command to Isabelle")
        writer.write(cmd)
        count += 1
      }
//      println("Flushing.")
      writer.flush()
      Thread.sleep(100)
    }
  }

  private def parseIsabelle(outFifo: Path) : Unit = {
    val output = new FileInputStream(outFifo.toFile)
    Source.fromInputStream(output, "ascii").getLines.foreach { line =>
//      println(s"Received: [$line]")
      val spaceIdx = line.indexOf(' ')
      val (seq,content) = if (spaceIdx == -1) (line,"") else line.splitAt(spaceIdx+1)
      callbacks.remove(seq.trim.toInt) match {
        case null => println(s"No callback $seq")
        case callback =>
          if (content.nonEmpty && content(0) == '!')
            callback(Failure(IsabelleException(content.substring(1))))
          else
            callback(Success(content))
      }
//      println(s"#callbacks = ${callbacks.size}")
    }
  }

  private def filePathFromResource(name: String): Path = {
    val url = getClass.getResource(name)
    assert(url != null, name)
    // TODO: Copy url to temp folder if not a file
    Path.of(url.toURI)
  }

  private def startProcess() : java.lang.Process = {
    def wd = setup.workingDirectory
    /** Path to absolute string, interpreted relative to wd */
    def str(path: Path) = wd.resolve(path).toAbsolutePath.toString

    val isabelleBinary = setup.isabelleHome.resolve("bin").resolve("isabelle")
    val mlFile = filePathFromResource("control_isabelle.ml")

    assert(setup.userDir.forall(_.endsWith(".isabelle")))

    val tempDir = Files.createTempDirectory("isabellecontrol").toAbsolutePath
    tempDir.toFile.deleteOnExit()
    logger.debug(s"Temp directory: $tempDir")

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

    logger.debug(s"Cmd line: $cmd")

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

  private def buildSession() : Unit = ???

  if (build) buildSession()
  private val process: lang.Process = startProcess()

  @volatile private var destroyed = false
  def destroy(): Unit = {
    destroyed = true
    garbageQueue.clear()
    process.destroy()

    def callCallback(cb: Try[String] => Unit): Unit =
      cb(Failure(IsabelleDestroyedException("Isabelle process has been destroyed")))

    for ((_,cb) <- sendQueue.asScala)
      callCallback(cb)
    sendQueue.clear()

    for (cb <- callbacks.values.asScala)
      callCallback(cb)
  }

  private def send(str: String, callback: Try[String] => Unit) : Unit = {
    if (destroyed)
      throw new IllegalStateException("Isabelle instance has been destroyed")
    sendQueue.put((str,callback))
  }

  /*  def computeInteger(ml: String): Promise[Int] = {
      val promise : Promise[Int] = Promise()
      assert(!ml.contains('\n'))
      send(s"i$ml\n", { result => promise.success(result.toInt) })
      promise
    }*/

  private def intStringToID(str: String) : ID =
    new ID(str.toInt, this)

  def executeMLCode(ml : String) : Future[Unit] = {
    val promise : Promise[Unit] = Promise()
    assert(!ml.contains('\n'))
    logger.debug(s"Executing ML code: $ml")
    send(s"M$ml\n", { result => promise.complete(result.map(_ => ())) })
    promise.future
  }

  def executeMLCodeNow(ml : String): Unit = Await.result(executeMLCode(ml), Duration.Inf)

  private[control] def storeFunction(ml : String): Promise[ID] = {
    val promise : Promise[ID] = Promise()
    assert(!ml.contains('\n'))
    logger.debug(s"Compiling ML function: $ml")
    send(s"f$ml\n", { result => promise.complete(result.map(intStringToID)) })
    promise
  }

  private[control] def storeInteger(i: Int): Promise[ID] = {
    val promise : Promise[ID] = Promise()
    send(s"s$i\n", { result => promise.complete(result.map(intStringToID)) })
    promise
  }

  private[control] def makePair(a: ID, b: ID) : Promise[ID] = {
    val promise : Promise[ID] = Promise()
    send(s"p${a.id} ${b.id}\n", { result => promise.complete(result.map(intStringToID)) })
    promise
  }

  private[control] def splitPair(pair: ID) : Promise[(ID,ID)] = {
    val promise : Promise[(ID,ID)] = Promise()
    send(s"P${pair.id}\n", { result => promise.complete(result.map { resultStr =>
      resultStr.split(' ') match {
      case Array(a,b) => (intStringToID(a), intStringToID(b)) } }) })
    promise
  }

  private[control] def storeString(str: String): Promise[ID] = {
    val promise : Promise[ID] = Promise()
    assert(!str.contains('\n'))
    send(s"S$str\n", { result => promise.complete(result.map(intStringToID)) })
    promise
  }

  private[control] def applyFunction(f: ID, x: ID): Promise[ID] = {
    val promise: Promise[ID] = Promise()
    send(s"a${f.id} ${x.id}\n", { result => promise.complete(result.map(intStringToID)) })
    promise
  }

  private[control] def retrieveInteger(id: ID): Promise[Int] = {
    val promise: Promise[Int] = Promise()
    send(s"r${id.id}\n", { result => promise.complete(result.map(_.toInt)) })
    promise
  }

  private[control] def retrieveString(id: ID): Promise[String] = {
    val promise: Promise[String] = Promise()
    send(s"R${id.id}\n", { result => promise.complete(result) })
    promise
  }

}

object Isabelle {
  private val logger = log4s.getLogger

  def logStream(stream: InputStream, level: LogLevel) : Unit = {
    val log = logger(level)
    val thread = new Thread(s"Isabelle output logger, $level") {
      override def run(): Unit = {
        new BufferedReader(new InputStreamReader(stream)).lines().forEach(line => logger.debug(line))

//        for (line <- Source.fromInputStream(stream).getLines())
//          log(line)
      }
    }
    thread.setDaemon(true)
    thread.start()
  }

  private[control] final class ID(val id: Int, isabelle: Isabelle) {
    isabelle.cleaner.register(this, new IDCleaner(id, isabelle))
  }
  private final class IDCleaner(id: Int, isabelle: Isabelle) extends Runnable {
    def run(): Unit = isabelle.garbageQueue.add(id)
  }

  case class Setup(
                    workingDirectory : Path = Paths.get(""),
                    isabelleHome : Path,
                    logic : String = "HOL",
                    sessionRoots : Seq[Path] = Nil,
                    /** Must end in .isabelle if provided */
                    userDir : Option[Path] = None
                  )

}

abstract class IsabelleControllerException(message: String) extends IOException(message)
case class IsabelleDestroyedException(message: String) extends IsabelleControllerException(message)
case class IsabelleException(message: String) extends IsabelleControllerException(message)






