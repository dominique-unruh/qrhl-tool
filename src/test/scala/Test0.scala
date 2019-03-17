import qrhl.isabelle.Isabelle

import scala.collection.JavaConverters._

object Test0 {
  def main(args: Array[String]): Unit = {
    println("Loading Isabelle")
    Isabelle.globalIsabelle
    println("Loaded")
//    val threadSet = Thread.getAllStackTraces.keySet.asScala
//    for (t <- threadSet if !t.isDaemon)
//      println(s"Thread: ${t.getName}, ${t.isDaemon}, ${t.getThreadGroup}")
    println("Exiting")
  }
}