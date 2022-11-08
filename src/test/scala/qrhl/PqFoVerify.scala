package qrhl

import qrhl.toplevel.Toplevel

import java.io.File
import java.nio.file.Paths
import java.time.Instant
import java.util.Date
import scala.sys.process.Process

/** For testing Dominique Unruh's files on postquantum Fujisaki-Okamoto. Not useful for others. */
object PqFoVerify {
  def main(args: Array[String]): Unit = {
    new Thread() {
      override def run(): Unit = {
        while (true) {
          println(Instant.now().toString)
          Thread.sleep(600000)
        }
      }
    }.start()
    while (true) {
      val toplevel = Toplevel.makeToplevel(cheating = false)
      Process(List("bash", "-c", "ls -1 proofs/*.qrhl | shuf | sed -e 's/.*/include \"&\"./' >tocheck.qrhl"), cwd = new File("/home/unruh/r/pq-fo-verify"))
        .!!
      toplevel.run(Paths.get("/home/unruh/r/pq-fo-verify/tocheck.qrhl"))
    }
  }
}
