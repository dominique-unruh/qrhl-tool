package qrhl

import java.io.File
import java.nio.file.Paths

import org.scalatest.{FlatSpec, FunSuite, Tag}
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
    val tags = if (name.matches("teleport.*")) List(Tag("SuperSlow")) else Nil
    println(s"Creating test $name, $tags")
    test(name,tags:_*) { testFile(name) }
  }

  test("test -- REMOVE") {
    testFile("test.qrhl")
  }
}
