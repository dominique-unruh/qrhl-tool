package hashedcomputation.filesystem

import org.scalatest.funsuite.AnyFunSuite

import java.io.IOException
import java.nio.file.{Files, Path}

class RootsDirectoryTest extends AnyFunSuite {
  val roots = RootsDirectory()

  test("access file") {
    val file = Path.of("src/test/isabelle/ROOT").toAbsolutePath
    roots.registerInterest(file)
    roots.snapshot().get(file)
  }

  test("access relative path") {
    val file = Path.of("src/test/isabelle/ROOT")
    assertThrows[AssertionError] {
      roots.snapshot().get(file)
    }
  }
}
