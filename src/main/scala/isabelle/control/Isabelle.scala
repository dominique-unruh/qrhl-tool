package isabelle.control

import java.io.{BufferedWriter, FileInputStream, FileOutputStream, IOException, OutputStreamWriter}
import java.lang
import java.lang.ProcessBuilder.Redirect
import java.lang.ref.Cleaner
import java.nio.file.{Files, Path}
import java.util.concurrent.{ArrayBlockingQueue, BlockingQueue, ConcurrentHashMap, ConcurrentLinkedQueue}

import qrhl.isabelle.DistributionDirectory

import scala.annotation.tailrec
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future, Promise}
import scala.io.Source
import scala.sys.process.Process


class Isabelle {
  import Isabelle._

  private val distributionDir = DistributionDirectory.distributionDirectory
  private val isabelle = "Isabelle2019-RC4/bin/isabelle"
  private val logic = "QRHL"
  private val roots = List("isabelle-thys","isabelle-afp")
  private val userDir = "isabelle-temp/user/Isabelle2019-RC4/.isabelle"
  private val mlFile = "isabelle-thys/control_isabelle.ml"

  private val sendQueue : BlockingQueue[(String, String => Unit)] = new ArrayBlockingQueue(1000)
  private val callbacks : ConcurrentHashMap[Int, String => Unit] = new ConcurrentHashMap()
//  private [isabelle] val referenceQueue = new ReferenceQueue[ID]()
  private val cleaner = Cleaner.create()

  // Must be Integer, not Int, because ConcurrentLinkedList uses null to indicate that it is empty
  private val garbageQueue = new ConcurrentLinkedQueue[Integer]()

  private def garbageCollect() : Option[String] = {
    println("Checking for garbage")
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
    println("Process queue thread started")
    val stream = new FileOutputStream(inFifo.toFile)
    val writer = new BufferedWriter(new OutputStreamWriter(stream, "ascii"))
    var count = 0

    @tailrec @inline
    def drainQueue() : Unit = {
      val elem = sendQueue.poll()
      if (elem!=null) {
        val (line,callback) = elem
        assert(line.endsWith("\n"))
        println(s"Writing ${line.trim}")
        if (callback != null)
          callbacks.put(count, callback)
        writer.write(line)
        count += 1
        drainQueue()
      }
    }

    while (true) {
      val (line,callback) = sendQueue.take()
      println(s"Writing! ${line.trim}")
      if (callback != null)
        callbacks.put(count, callback)
      writer.write(line)
      count += 1
      drainQueue()
      for (cmd <- garbageCollect()) {
        println("Sending GC command")
        writer.write(cmd)
        count += 1
      }
      println("Flushing.")
      writer.flush()
      Thread.sleep(100)
    }
  }

  private def parseIsabelle(outFifo: Path) : Unit = {
    val output = new FileInputStream(outFifo.toFile)
    Source.fromInputStream(output, "ascii").getLines.foreach { line =>
      val (seq,content) = line.splitAt(line.indexOf(' ')+1)
      println(s"Received: [$line]")
      callbacks.remove(seq.trim.toInt) match {
        case null => println(s"No callback $seq")
        case callback => callback(content)
      }
      println(s"#callbacks = ${callbacks.size}")
    }
  }

  private def startProcess() : java.lang.Process = {
    val isabelle = distributionDir.resolve(this.isabelle).toString
    val mlFile = distributionDir.resolve(this.mlFile).toString

    val userDir = distributionDir.resolve(this.userDir)
    assert(userDir.endsWith(".isabelle"))

    val tempDir = Files.createTempDirectory("isabellecontrol")
    tempDir.toFile.deleteOnExit()
    println(s"tempDir: $tempDir")
    val inputPipe = tempDir.resolve("in-fifo").toAbsolutePath
    inputPipe.toFile.deleteOnExit()
    val outputPipe = tempDir.resolve("out-fifo").toAbsolutePath
    outputPipe.toFile.deleteOnExit()
    if (Process(List("mkfifo", inputPipe.toString)).! != 0)
      throw new IOException(s"Cannot create fifo $inputPipe")
    if (Process(List("mkfifo", outputPipe.toString)).! != 0)
      throw new IOException(s"Cannot create fifo $outputPipe")

    // TODO: escape pipe name for ML
    val initInOut = s"""val (inputPipeName,outputPipeName) = ("$inputPipe","$outputPipe")"""

    val cmd : List[String] = List(isabelle,"process","-l",logic,"-e",initInOut,"-f",mlFile,"-e","Control_Isabelle.handleLines()") ++
      (for (r <- roots; a <- List("-d",distributionDir.resolve(r).toString)) yield a)

    val processBuilder = new java.lang.ProcessBuilder(cmd :_*)
    processBuilder.directory(distributionDir.toFile)
    processBuilder.environment.put("USER_HOME", userDir.getParent.toString)
    // TODO: It seems like the output is buffered somewhere and returned at the end of the execution. Why?
    processBuilder.redirectError(Redirect.INHERIT)
    processBuilder.redirectOutput(Redirect.INHERIT)

    val processQueueThread = new Thread("Send to Isabelle") {
      override def run(): Unit = processQueue(inputPipe) }
    processQueueThread.setDaemon(true)
    processQueueThread.start()

    val parseIsabelleThread = new Thread("Read from Isabelle") {
      override def run(): Unit = parseIsabelle(outputPipe) }
    parseIsabelleThread.setDaemon(true)
    parseIsabelleThread.start()

    processBuilder.start()
  }

  private val process: lang.Process = startProcess()

  private def send(str: String, callback: String => Unit = null) : Unit =
    sendQueue.put((str,callback))

  @deprecated("Remove", "now")
  def computeInteger(ml: String): Promise[Int] = {
    val promise : Promise[Int] = Promise()
    assert(!ml.contains('\n'))
    send(s"i$ml\n", { result => promise.success(result.toInt) })
    promise
  }

  private def intStringToID(str: String) : ID =
    new ID(str.toInt, this)

  private def storeFunction(ml : String): Promise[ID] = {
    val promise : Promise[ID] = Promise()
    assert(!ml.contains('\n'))
    send(s"f$ml\n", { result => promise.success(intStringToID(result)) })
    promise
  }

  private def storeInteger(i: Int): Promise[ID] = {
    val promise : Promise[ID] = Promise()
    send(s"s$i\n", { result => promise.success(intStringToID(result)) })
    promise
  }

  private def retrieveInteger(id: ID): Promise[Int] = {
    val promise: Promise[Int] = Promise()
    send(s"r${id.id}\n", { result => promise.success(result.toInt) })
    promise
  }

  private def applyFunction(f: ID, x: ID): Promise[ID] = {
    val promise: Promise[ID] = Promise()
    send(s"a${f.id} ${x.id}\n", { result => promise.success(intStringToID(result)) })
    promise
  }

  class MLValue[A] private[isabelle] (private val id : Future[Isabelle.ID]) {
//    final def isabelle : Isabelle = Isabelle.this

    def retrieve()(implicit retriever: MLValue.Retriever[A], ec: ExecutionContext): Future[A] =
      retriever.retrieve(this)

    def apply[D, R](arg: MLValue[D])
                   (implicit ev: MLValue[A] =:= MLValue[D => R], ec: ExecutionContext): MLValue[R] = {
      new MLValue(
        for (fVal <- ev(this).id;
             xVal <- arg.id;
             fx <- applyFunction(fVal, xVal).future)
          yield fx
      )
    }

    def apply[D1, D2, R](arg1: MLValue[D1], arg2: MLValue[D2])
                        (implicit ev: MLValue[A] =:= MLValue[D1 => D2 => R], ec: ExecutionContext): MLValue[R] =
      ev(this).apply[D1, D2 => R](arg1).apply[D2, R](arg2)

    def apply[D1, D2, D3, R](arg1: MLValue[D1], arg2: MLValue[D2], arg3: MLValue[D3])
                            (implicit ev: MLValue[A] =:= MLValue[D1 => D2 => D3 => R], ec: ExecutionContext): MLValue[R] =
      ev(this).apply[D1, D2 => D3 => R](arg1).apply[D2, D3 => R](arg2).apply[D3, R](arg3)
  }

  object MLValue {
    abstract class Retriever[A] {
      protected[Isabelle] def retrieve(value: MLValue[A])(implicit ec: ExecutionContext) : Future[A]
    }

    implicit object IntRetriever extends Retriever[Int] {
      override protected[Isabelle] def retrieve(value: MLValue[Int])(implicit ec: ExecutionContext): Future[Int] =
        value.id.flatMap(retrieveInteger(_).future)
    }

    def apply(i: Int) : MLValue[Int] =
      new MLValue(storeInteger(i).future)

    // TODO: Automatically add wrapping and unwrapping of exceptions
    def compileFunction[A,B](ml: String) : MLValue[A => B] =
      new MLValue(storeFunction(ml).future)
  }

}

object Isabelle {
  private final class ID(val id: Int, isabelle: Isabelle) {
    isabelle.cleaner.register(this, new IDCleaner(id, isabelle))
  }
  private final class IDCleaner(id: Int, isabelle: Isabelle) extends Runnable {
    def run(): Unit = isabelle.garbageQueue.add(id)
  }
}

object Test {
  def await[A](x: Future[A]): A = Await.result(x, Duration.Inf)

  def main(args: Array[String]): Unit = {


    implicit val ec: ExecutionContext = ExecutionContext.global
    implicit val isabelle: Isabelle = new Isabelle()
    import isabelle.MLValue.IntRetriever
    type MLValue[A] = isabelle.MLValue[A]
    val MLValue = isabelle.MLValue

    implicit val ev1: MLValue[Int=>Int] =:= MLValue[Int=>Int] = =:=.tpEquals
    implicit val ev2: MLValue[Int=>Int=>Int] =:= MLValue[Int=>Int=>Int] = =:=.tpEquals

    isabelle.computeInteger("1").future.onComplete(println)

    val int1 = MLValue(1234)
    val int2 = MLValue(43210000)
    val add : MLValue[Int => Int => Int] = MLValue.compileFunction("fn (E_Int i) => E_ExnExn (fn (E_Int j) => E_Int (i+j))")
    val sum = add(int1,int2)

    println(await(sum.retrieve))

    for (i <- 1 to 10000) {
//      Thread.sleep(100)
//      System.gc()
      MLValue(i)
    }
    System.gc()

    Thread.sleep(1000)
    println("GC")
    System.gc()
    Thread.sleep(1000)
//    isabelle.computeInteger("1").future.onComplete(println)
    println(s"#objects: ${await(isabelle.computeInteger("Control_Isabelle.numObjects()").future)}")
    Thread.sleep(1000)
    println(s"#objects: ${await(isabelle.computeInteger("Control_Isabelle.numObjects()").future)}")

    Thread.sleep(1000)
    println("Exiting")

  }

}

