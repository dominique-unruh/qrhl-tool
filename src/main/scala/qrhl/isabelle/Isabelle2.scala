package qrhl.isabelle

import java.io.{BufferedWriter, FileInputStream, FileOutputStream, IOException, OutputStreamWriter}
import java.nio.file.{Files, Path}
import java.util.concurrent.{ArrayBlockingQueue, BlockingQueue, ConcurrentHashMap}

import scala.annotation.tailrec
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future, Promise}
import scala.io.Source
import scala.sys.process.{Process, ProcessIO}

/*
trait MLType
object MLType {
  case object Int extends MLType
  case class Fun[A <: MLType, B <: MLType] extends MLType
}
*/

// TODO: Install cleaner that garbage collects on ML side
class MLValue[A](val id : Future[Isabelle2.ID]) {
//  def retrieve()(implicit ec: ExecutionContext) : Future[A] = throw new UnsupportedOperationException(s"Retrieving value of $this")
  def retrieve()(implicit retriever: MLValue.Retriever[A], isabelle: Isabelle2, ec: ExecutionContext) : Future[A] =
  retriever.retrieve(this)
}

object MLValue {
  abstract class Retriever[A] {
    def retrieve(value: MLValue[A])(implicit isabelle: Isabelle2, ec: ExecutionContext) : Future[A]
  }
  implicit object IntRetriever extends Retriever[Int] {
    override def retrieve(value: MLValue[Int])(implicit isabelle: Isabelle2, ec: ExecutionContext): Future[Int] =
      value.id.flatMap(isabelle.retrieveInteger(_).future)
  }

  def apply(i: Int)(implicit isabelle: Isabelle2) =
    new MLValue[Int](isabelle.storeInteger(i).future)

  // TODO: Automatically add wrapping and unwrapping of exceptions
  def compileFunction[A,B](ml: String)(implicit isabelle: Isabelle2) =
    new MLValue[A => B](isabelle.storeFunction(ml).future)

  def applyFunction[A,B](f: MLValue[A=>B], x:MLValue[A])(implicit isabelle: Isabelle2, ec: ExecutionContext) : MLValue[B] =
    new MLValue(
      for (fVal <- f.id;
           xVal <- x.id;
           fx <- isabelle.applyFunction(fVal,xVal).future)
        yield fx
    )
}

class Isabelle2 {
  import Isabelle2._

  private val distributionDir = DistributionDirectory.distributionDirectory
  private val isabelle = "Isabelle2019-RC4/bin/isabelle"
  private val logic = "QRHL"
  private val roots = List("isabelle-thys","isabelle-afp")
  private val userDir = "isabelle-temp/user/Isabelle2019-RC4/.isabelle"
  private val mlFile = "isabelle-thys/control_isabelle.ml"

  private val sendQueue : BlockingQueue[(String, String => Unit)] = new ArrayBlockingQueue(1000)
  private val callbacks : ConcurrentHashMap[Int, String => Unit] = new ConcurrentHashMap()

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
      println(s"Writing! ${line.trim}");
      if (callback != null)
        callbacks.put(count, callback)
      writer.write(line)
      count += 1
      drainQueue()
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
      callbacks.get(seq.trim.toInt) match {
        case null => println(s"No callback $seq")
        case callback => callback(content)
      }
    }
  }

  private def startProcess() : Process = {
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
      throw new IOException(s"Cannot create fifo ${inputPipe}")
    if (Process(List("mkfifo", outputPipe.toString)).! != 0)
      throw new IOException(s"Cannot create fifo ${outputPipe}")

    // TODO: escape pipe name for ML
    val initInOut = s"""val (inputPipeName,outputPipeName) = ("${inputPipe}","${outputPipe}")"""

    val cmd : List[String] = List(isabelle,"process","-l",logic,"-e",initInOut,"-f",mlFile) ++
      (for (r <- roots; a <- List("-d",distributionDir.resolve(r).toString)) yield a)

    val processBuilder = Process(cmd, distributionDir.toFile, "USER_HOME" -> userDir.getParent.toString)

    val processQueueThread = new Thread("Send to Isabelle") {
      override def run(): Unit = processQueue(inputPipe) }
    processQueueThread.setDaemon(true)
    processQueueThread.start()

    val parseIsabelleThread = new Thread("Read from Isabelle") {
      override def run(): Unit = parseIsabelle(outputPipe) }
    parseIsabelleThread.setDaemon(true)
    parseIsabelleThread.start()

    // TODO: This creates non-daemon threads
    processBuilder.run()
  }

  val process = startProcess()

  def send(str: String, callback: String => Unit = null) : Unit =
    sendQueue.put((str,callback))

  def computeInteger(ml: String): Promise[Int] = {
    val promise : Promise[Int] = Promise()
    assert(!ml.contains('\n'))
    send(s"i$ml\n", { result => promise.success(result.toInt) })
    promise
  }

  def storeFunction(ml : String): Promise[ID] = {
    val promise : Promise[ID] = Promise()
    assert(!ml.contains('\n'))
    send(s"f$ml\n", { result => promise.success(result.toInt) })
    promise
  }

  def storeInteger(i: Int): Promise[ID] = {
    val promise : Promise[ID] = Promise()
    send(s"s$i\n", { result => promise.success(result.toInt) })
    promise
  }

  def retrieveInteger(id: ID): Promise[Int] = {
    val promise: Promise[Int] = Promise()
    send(s"r$id\n", { result => promise.success(result.toInt) })
    promise
  }

  def applyFunction(f: ID, x: ID): Promise[ID] = {
    val promise: Promise[ID] = Promise()
    send(s"a$f $x\n", { result => promise.success(result.toInt) })
    promise
  }
}

object Isabelle2 {
  type ID = Int
}

object Test {
  def await[A](x: Future[A]): A = Await.result(x, Duration.Inf)

  def main(args: Array[String]): Unit = {

    implicit val ec: ExecutionContext = ExecutionContext.global
    implicit val isabelle: Isabelle2 = new Isabelle2()

    val int1 = MLValue(1234)
    val int2 = MLValue(43210000)
    val f : MLValue[Int => Int => Int] = MLValue.compileFunction("fn (E_Int i) => E_ExnExn (fn (E_Int j) => E_Int (i+j))")
    val f12 = MLValue.applyFunction(MLValue.applyFunction(f,int1),int2)

    println(await(f12.retrieve()))

    /*   val result = for (id1 <- isabelle.storeInteger(1234).future;
                         id2 <- isabelle.storeInteger(4321).future;
                         f <- isabelle.storeFunction("fn (E_Int i) => E_ExnExn (fn (E_Int j) => E_Int (i+j))").future;
                         f_id1 <- isabelle.applyFunction(f,id1).future;
                         f_id1_id2 <- isabelle.applyFunction(f_id1,id2).future;
                         result <- isabelle.retrieveInteger(f_id1_id2).future)
         yield result

       print(await(result))
   */

    Thread.sleep(2000)

    isabelle.process.destroy()

    Thread.sleep(2000)

    println("Exiting")



    import scala.collection.JavaConverters._
    for (t <- Thread.getAllStackTraces.keySet.asScala)
        println((t.isDaemon,t.getName,t))

  }

}