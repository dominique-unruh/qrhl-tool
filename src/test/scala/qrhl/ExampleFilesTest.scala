package qrhl

import java.io.File
import java.nio.file.Paths

import org.scalatest.{FlatSpec, FunSuite}
import qrhl.toplevel.Toplevel
import org.scalatest.tags.Slow

@Slow
class ExampleFilesTest extends FunSuite {

  def testFile(file:String): Unit = {
    val toplevel = Toplevel.makeToplevel(cheating = false)
    toplevel.run(Paths.get("examples",file))
    System.gc()
  }

  for (file <- new File("examples").listFiles();
       name = file.getName
       if name.endsWith(".qrhl")
       if !name.matches("test.*")) {
    println(s"Creating test $name")
    test(name) { testFile(name) }
  }
}
