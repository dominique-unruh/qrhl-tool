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

case class DirectoryElement(path: Path) extends Element[DirectorySnapshot, Option[FileSnapshot]] {
  override def extract(directorySnapshot: DirectorySnapshot): Option[FileSnapshot] =
    directorySnapshot.getFile(path)

  override def hash: Hash[DirectoryElement.this.type] = ???

  override def extractHash(value: DirectorySnapshot): Hash[Option[FileSnapshot]] =
    Hashable.hash(extract(value))
}

