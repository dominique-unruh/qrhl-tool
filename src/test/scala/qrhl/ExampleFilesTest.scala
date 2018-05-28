package qrhl

import java.nio.file.Paths

import org.scalatest.{FlatSpec, FunSuite}
import qrhl.toplevel.Toplevel
import org.scalatest.tags.Slow

@Slow
class ExampleFilesTest extends FunSuite {

  test("prg-enc-indcpa.qrhl") {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("prg-enc-indcpa.qrhl"))
  }

  test("prg-enc-rorcpa.qrhl") {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("prg-enc-rorcpa.qrhl"))
  }

  test("equality.qrhl") {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("equality.qrhl"))
  }

  test("example.qrhl") {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("example.qrhl"))
  }

  test("rnd.qrhl") {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("rnd.qrhl"))
  }

  test("teleport.qrhl") {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("teleport.qrhl"))
  }

  test("teleport-terse.qrhl") {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("teleport-terse.qrhl"))
  }
}
