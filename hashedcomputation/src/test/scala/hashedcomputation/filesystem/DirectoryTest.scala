package hashedcomputation.filesystem

import java.io.IOException
import java.nio.file.{Files, Path}
import org.scalatest.funsuite.AnyFunSuite
import org.apache.commons.lang3.SystemUtils

class DirectoryTest extends AnyFunSuite {
  test("DirectorySnapshot") {
    val delay =
      if (SystemUtils.IS_OS_MAC)
        20000 // On MacOS, the WatchService seems to use polling and large delays in noticing the change of a file can occur
      else
        500
    val dirPath = Files.createTempDirectory("test-DirectorySnapshot")
    println(s"dirPath = $dirPath")
    assert(dirPath.toString != "/") // Can happen on MacOS, apparently (?)
    dirPath.toFile.deleteOnExit()

    Files.writeString(dirPath.resolve("test1"), "test1")
    Thread.sleep(delay)

    val dir = Directory(dirPath)
    val snapshot1 = dir.snapshot()
    assert(snapshot1.keySet == Set("test1"))

    Files.writeString(dirPath.resolve("test2"), "test2")
    Thread.sleep(delay)
    val snapshot2 = dir.snapshot()
    assert(snapshot2.keySet == Set("test1","test2"))
    assert(snapshot2.hash != snapshot1.hash)

    Files.writeString(dirPath.resolve("test2"), "test2 new")
    Thread.sleep(delay)
    val snapshot3 = dir.snapshot()
    assert(snapshot3.keySet == Set("test1","test2"))
    assert(snapshot3.hash != snapshot2.hash)
    assert(snapshot3.hash != snapshot1.hash)

    Files.delete(dirPath.resolve("test2"))
    Thread.sleep(delay)
    val snapshot4 = dir.snapshot()
    assert(snapshot4.keySet == Set("test1"))
    assert(snapshot4.hash == snapshot1.hash)
  }

  test("partial snapshot") {
    val dir = Directory(Path.of("src/test/isabelle"), partial=true)
    val snapshot1 = dir.snapshot()
    assertThrows[IOException] { snapshot1.get("ROOT") }

    println("Recreating snapshot")
    val snapshot2 = dir.snapshot()
    val file2 = snapshot2.get("ROOT")
    println(file2)
    file2 match {
      case Some(_: FileSnapshot) =>
      case _ => fail()
    }
  }

  test("partial snapshot nested") {
    val dir = Directory(Path.of(""), partial = true)
    val file = Path.of("src/test/isabelle/ROOT")

    assertThrows[OutdatedSnapshotException] { dir.snapshot().get(file) }
    dir.snapshot().dump()

    dir.snapshot().get(file)

  }
}
