package qrhl

import java.nio.file.Path

import hashedcomputation.Element
import hashedcomputation.filesystem.{Directory, DirectoryEntry, DirectorySnapshot, FileSnapshot, FingerprintedDirectorySnapshot}

final case class CurrentFS(root: Path, directory: FingerprintedDirectorySnapshot) {
//  val root: Path
  def relativize(path: Path): Path =
    try
      root.relativize(path).normalize()
    catch {
      case e: IllegalArgumentException =>
        throw UserException(s"""Cannot load $path.\nCan only load files on ${root} (the filesystem where qrhl-tool was invoked).""")
    }
  def getFile(path: Path): Option[FileSnapshot] = {
    assert(path.isAbsolute)
    directory.getFile(relativize(path))
  }
/*  def getFileRelative(path: Path): Option[FileSnapshot] = {
    assert(!path.isAbsolute)
    directory.getFile(path)
  }*/

  //  def fingerprinted: CurrentFSFingerprint
}

/*
final class CurrentFSNoFingerprint(val directory: DirectorySnapshot, val root: Path) extends CurrentFS {
  def getFile(path: Path): Option[FileSnapshot] = directory.getFile(relativize(path))

  override def fingerprinted: CurrentFSFingerprint =
    new CurrentFSFingerprint(FingerprintedDirectorySnapshot(directory), root)
}

final class CurrentFSFingerprint(val directory: FingerprintedDirectorySnapshot, val root: Path) extends CurrentFS {
  def getFile(path: Path): Option[FileSnapshot] = directory.getFile(relativize(path))
  override def fingerprinted: CurrentFSFingerprint = this
}

object CurrentFS {
  def apply(directory: Directory) : CurrentFS =
    new CurrentFSNoFingerprint(directory.snapshot(), directory.path)
}

object CurrentFSElementRoot extends Element[CurrentFS, Path]
object CurrentFSElementDir extends Element[CurrentFS, DirectorySnapshot]
*/
