package hashedcomputation.filesystem

import java.nio.file.Path
import hashedcomputation.Implicits.optionHashable
import hashedcomputation.{Element, Fingerprint, FingerprintBuilder, FingerprintBuilderImpl, Hash, Hashable}

import java.util.NoSuchElementException
import scala.annotation.tailrec
import scala.collection.mutable

/*
object DummyCollection extends mutable.Growable[Any] with Iterable[Nothing] {
  override def addOne(elem: Any): DummyCollection.this.type = this
  override def clear(): Unit = {}
  override def iterator: Iterator[Nothing] = new Iterator[Nothing] {
    override def hasNext: Boolean = false
    override def next(): Nothing = throw new NoSuchElementException("DummyCollection has no elements")
  }
  override def knownSize: Int = 0
}
*/

/** Not thread safe */
class FingerprintedDirectorySnapshot private (val fingerprintBuilder: FingerprintBuilder[DirectorySnapshot])
  /*extends FingerprintingView[DirectorySnapshot, FingerprintedDirectorySnapshot]*/ {
  private val directory = fingerprintBuilder.unsafeUnderlyingValue

  def getFile(path: Path): Option[FileSnapshot] = {
    val file = directory.getFile(path)
    fingerprintBuilder.access(DirectoryElement(path), file)
    file
  }

//  override def unsafePeekUnderlyingValue: DirectorySnapshot = directory

  def everything: DirectorySnapshot = {
    fingerprintBuilder.accessAll()
    directory
  }
}

object FingerprintedDirectorySnapshot {
  def apply(directory: FingerprintBuilder[DirectorySnapshot]) = new FingerprintedDirectorySnapshot(directory)
  def apply(directory: DirectorySnapshot): FingerprintedDirectorySnapshot = apply(new FingerprintBuilderImpl(directory))
  def apply(directory: GenericDirectory): FingerprintedDirectorySnapshot = apply(directory.snapshot())
}

final case class DirectoryElement(path: Path) extends Element[DirectorySnapshot, Option[FileSnapshot]] {
  override def extract(directorySnapshot: DirectorySnapshot): Option[FileSnapshot] =
    directorySnapshot.getFile(path)

  private val pathString = path.toString

  /** We override the automatic definition of `.equals` (from case class) because this invokes [[Path#equals]] which
   * does not behave well:
   *
   * On Windows, [[Path.equals]] does case-insensitive comparisons. This is invalid (1) because even on Windows, it is
   * possible to have case-sensitive directories (see https://www.windowscentral.com/how-enable-ntfs-treat-folders-case-sensitive-windows-10#enable_case_sensitivity_ntfs_windows10).
   * (2) it means that equal [[Path]]s return different sequences of names (e.g., via the iterator) and that means
   * that [[Directory#pathToList]] gives different results for equal [[DirectoryElement]]s, and that ultimately violates
   * the contract for [[Element]].
   * */
  override def equals(obj: Any): Boolean = obj match {
    case d: DirectoryElement => pathString == d.pathString
    case _ => false
  }

  override def hashCode(): Int = pathString.hashCode

  override def hash: Hash[DirectoryElement.this.type] = ???

  override def extractHash(value: DirectorySnapshot): Hash[Option[FileSnapshot]] =
    Hashable.hash(extract(value))
}

