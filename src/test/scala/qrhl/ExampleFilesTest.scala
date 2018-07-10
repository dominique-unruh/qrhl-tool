package qrhl

import java.nio.file.Paths

import org.scalatest.{FlatSpec, FunSuite}
import qrhl.toplevel.Toplevel
import org.scalatest.tags.Slow

@Slow
class ExampleFilesTest extends FunSuite {

  def testFile(file:String): Unit = {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("examples",file))
    toplevel.dispose()
    System.gc()
  }

  test("prg-enc-indcpa.qrhl") {
    testFile("prg-enc-indcpa.qrhl")
  }

  test("prg-enc-rorcpa.qrhl") {
    testFile("prg-enc-rorcpa.qrhl")
  }

  test("equality.qrhl") {
    testFile("equality.qrhl")
  }

  test("example.qrhl") {
    testFile("example.qrhl")
  }

  test("rnd.qrhl") {
    testFile("rnd.qrhl")
  }

  test("teleport.qrhl") {
    testFile("teleport.qrhl")
  }

  test("teleport-terse.qrhl") {
    testFile("teleport-terse.qrhl")
  }

  test("random-oracle.qrhl") {
    testFile("random-oracle.qrhl")
  }
}
