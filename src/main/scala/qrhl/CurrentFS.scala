package qrhl

import java.nio.file.Path

import hashedcomputation.filesystem.{Directory, DirectoryEntry, DirectorySnapshot}

final class CurrentFS(val directory: DirectorySnapshot, val root: Path) {
  def relativize(path: Path): Path =
    try
      root.relativize(path).normalize()
    catch {
      case e: IllegalArgumentException =>
        throw UserException(s"""Cannot load $path.\nCan only load files on ${root} (the filesystem where qrhl-tool was invoked).""")
    }
  def get(path: Path): Option[DirectoryEntry] = directory.get(relativize(path))
}

object CurrentFS {
  def apply(directory: Directory) : CurrentFS =
    new CurrentFS(directory.snapshot(), directory.path)
}
