package qrhl

import java.nio.file.Paths

import org.scalatest.FlatSpec
import qrhl.toplevel.Toplevel

class ExampleFilesTest extends FlatSpec {

  "prg-enc-indcpa.qrhl" should "execute successfully" in {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("prg-enc-indcpa.qrhl"))
  }

  "prg-enc-rorcpa.qrhl" should "execute successfully" in {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("prg-enc-rorcpa.qrhl"))
  }

  "equality.qrhl" should "execute successfully" in {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("equality.qrhl"))
  }

  "example.qrhl" should "execute successfully" in {
    val toplevel = new Toplevel()
    toplevel.run(Paths.get("example.qrhl"))
  }

}
