package hashedcomputation.filesystem

import java.nio.file.Path

import hashedcomputation.Implicits.optionHashable
import hashedcomputation.{Element, Fingerprint, Fingerprinter, Hash, Hashable}

import scala.collection.mutable

/** Not thread safe */
class FingerprintedDirectorySnapshot(directory: DirectorySnapshot) {
  private val fingerprinters = new mutable.ArrayDeque[MyFingerprinter]()

  private final class MyFingerprinter extends Fingerprinter[DirectorySnapshot] {
    private val accesses = new mutable.LinkedHashSet[Path]
    def accessed(path: Path): Unit = accesses += path
    override def fingerprint(): Fingerprint[DirectorySnapshot] = {
      val entries = for (access <- accesses.toList)
        yield Fingerprint.Entry(DirectoryElement(access), directory)
      Fingerprint(directory.hash, Some(entries))
    }
    override def dispose(): Unit = fingerprinters.removeAll(fp => fp eq this)
  }

  def newFingerprinter : Fingerprinter[DirectorySnapshot] = {
    val fingerprinter = new MyFingerprinter
    fingerprinters.append(fingerprinter)
    fingerprinter
  }

  def getFile(path: Path): Option[FileSnapshot] = {
    for (fp <- fingerprinters)
      fp.accessed(path)
    directory.getFile(path)
  }

}

case class DirectoryElement(path: Path) extends Element[DirectorySnapshot, Option[FileSnapshot]] {
  override def extract(directorySnapshot: DirectorySnapshot): Option[FileSnapshot] =
    directorySnapshot.getFile(path)

  override def hash: Hash[DirectoryElement.this.type] = ???

  override def extractHash(value: DirectorySnapshot): Hash[Option[FileSnapshot]] =
    Hashable.hash(extract(value))
}

