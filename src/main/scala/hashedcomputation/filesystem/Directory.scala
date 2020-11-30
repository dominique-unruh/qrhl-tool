package hashedcomputation.filesystem

import java.io.IOException
import java.nio.file.LinkOption.NOFOLLOW_LINKS
import java.nio.file.StandardWatchEventKinds.{ENTRY_CREATE, ENTRY_DELETE, ENTRY_MODIFY, OVERFLOW}
import java.nio.file.{Files, Path, WatchKey, WatchService}

import com.google.common.cache.{CacheBuilder, RemovalNotification}
import hashedcomputation.Fingerprint.Entry
import hashedcomputation.{Element, Fingerprint, Hash, HashedOption, HashedValue}
import hashedcomputation.filesystem.Directory.DirectoryListener
import org.log4s

import scala.collection.concurrent.TrieMap
import scala.collection.mutable
import scala.jdk.CollectionConverters.IteratorHasAsScala
import scala.ref.{ReferenceWrapper, SoftReference, WeakReference}

class Directory private (val path: Path, parent: Directory, parentKey: Path) extends DirectoryListener {
  //  def snapshot : DirectorySnapshot = new DirectorySnapshot(this)
  Directory.watchDirectory(path, this)
  private val subdirs = new TrieMap[Path, Directory]
  @volatile private var currentSnapshot = makeSnapshot

  private def makeSnapshot : DirectorySnapshot =
    Files.list(path).iterator().asScala.foldLeft(DirectorySnapshot.empty) { (snapshot, file) =>
      updateSnapshot(this.path.relativize(file), snapshot)
    }

  def dispose(): Unit = Directory.unwatchDirectory(this)

  def snapshot(): DirectorySnapshot = currentSnapshot

  private def updateSnapshot(path: Path, snapshot: DirectorySnapshot): DirectorySnapshot = {
    val fullPath = this.path.resolve(path)
    if (Files.isDirectory(fullPath, NOFOLLOW_LINKS)) {
      val dir = new Directory(fullPath, this, path)
      snapshot.updated(path.toString, dir.snapshot())
    } else if (Files.isRegularFile(fullPath, NOFOLLOW_LINKS)) {
      val file = new FileSnapshot(fullPath)
      snapshot.updated(path.toString, file)
    } else
      ???
  }

  override def onCreate(path: Path): Unit = {
    assert(path.getNameCount==1)
    for (subdir <- subdirs.remove(path)) subdir.dispose()

    currentSnapshot = updateSnapshot(path, currentSnapshot)

    if (parent!=null)
      parent.onModify(parentKey)
  }
  override def onModify(path: Path): Unit = onCreate(path)
  override def onDelete(path: Path): Unit = {
    assert(path.getNameCount==1)
    subdirs.remove(path)
    currentSnapshot = currentSnapshot.removed(path.toString)
    if (parent!=null)
      parent.onModify(parentKey)
  }
  override def onOverflow(): Unit = {
    currentSnapshot = makeSnapshot
    if (parent!=null)
      parent.onModify(parentKey)
  }
}

object Directory {
  def apply(path: Path) = new Directory(path.normalize.toAbsolutePath, null, null)

  trait DirectoryListener {
    def onCreate(path: Path): Unit
    def onModify(path: Path): Unit
    def onDelete(path: Path): Unit
    def onOverflow(): Unit
  }
  private val listeners = CacheBuilder
    .newBuilder()
    .weakValues()
    .removalListener[WatchKey, DirectoryListener]((notification:RemovalNotification[WatchKey,DirectoryListener]) => notification.getKey.cancel())
    .build[WatchKey, DirectoryListener]()

  private val logger = log4s.getLogger
  private val watchServices = new TrieMap[java.nio.file.FileSystem, WatchService]

  def unwatchDirectory(listener: DirectoryListener): Unit =
    listeners.invalidate(listener)

  def watchDirectory(path: Path, listener: DirectoryListener): Unit = {
    val filesystem = path.getFileSystem
    val watchService = watchServices.getOrElseUpdate(filesystem, {
      logger.debug(s"Found new filesystem: $filesystem")
      val watchService = filesystem.newWatchService()
      val thread = new Thread(new PollWatchService(watchService), s"Filesystem watcher for $filesystem")
      thread.setDaemon(true)
      thread.start()
      watchService
    })
    val watchKey = path.register(watchService, ENTRY_CREATE, ENTRY_DELETE, ENTRY_MODIFY)
    listeners.put(watchKey, listener)
  }

  private class PollWatchService(watchService: WatchService) extends Runnable {
    override def run(): Unit = {
      while (true) {
        val key = watchService.take()
        val events = key.pollEvents()
        key.reset()
        listeners.getIfPresent(key) match {
          case null => logger.error(s"Did not find a listener for key $key")
          case listener =>
            events.forEach { event => try {
              event.kind() match {
                case OVERFLOW => listener.onOverflow()
                case ENTRY_CREATE => listener.onCreate(event.context().asInstanceOf[Path])
                case ENTRY_MODIFY => listener.onModify(event.context().asInstanceOf[Path])
                case ENTRY_DELETE => listener.onDelete(event.context().asInstanceOf[Path])
              }}
            catch {
              case e : Throwable => logger.error(e)(s"Listener threw exception on event $event")
            }}}
      }
    }
  }
}

sealed trait DirectoryEntry extends HashedValue

final class FileSnapshot(path: Path) extends DirectoryEntry {
  private var contentRef : ReferenceWrapper[Array[Byte]] = _
  val hash: Hash[this.type] = {
    val content = Files.readAllBytes(path)
    val hash = hashContent(content)
    contentRef = WeakReference(content)
    hash
  }
  private def hashContent(content: Array[Byte]): Hash[this.type] =
    Hash.hashBytes(content) // TODO: should be tagged

  def content: Array[Byte] = {
    contentRef match {
      case WeakReference(content) =>
        contentRef = SoftReference(content)
        content
      case SoftReference(content) => content
      case _ =>
        val content = Files.readAllBytes(path)
        if (hash != hashContent(content))
          throw new IOException("Snapshot outdated")
        contentRef = SoftReference(content)
        content
    }
  }
}

class DirectorySnapshot private (content: Map[String, DirectoryEntry]) extends DirectoryEntry with Map[String, DirectoryEntry] with HashedValue {
  override def hash: Hash[this.type] =
    Hash.hashString(content.toList.map { case (s,h) => (s,h.hash) }.toString()) // TODO: proper hash

  override def get(key: String): Option[DirectoryEntry] = content.get(key)
  def get(path: Path): Option[DirectoryEntry] = {
    assert(!path.isAbsolute)
    var entry : DirectoryEntry = this
    for (name <- path.normalize.iterator().asScala) {
      entry match {
        case dir : DirectorySnapshot =>
          dir.get(name.toString) match {
            case None => return None
            case Some(entry) => entry
          }
        case _ : FileSnapshot => return None
      }
    }
    Some(entry)
  }

  override def iterator: Iterator[(String, DirectoryEntry)] = content.iterator
  override def removed(key: String): DirectorySnapshot =
    new DirectorySnapshot(content.removed(key))

  override def updated[V1 >: DirectoryEntry](key: String, value: V1): Map[String, V1] =
    content.updated(key, value)

  def updated(key: String, value: DirectoryEntry) : DirectorySnapshot =
    new DirectorySnapshot(content.updated(key, value))
}


object DirectorySnapshot {
  val empty = new DirectorySnapshot(Map.empty)
}

/** Not thread safe */
class FingerprintedDirectorySnapshot private (directory: DirectorySnapshot) {
  private val accesses = new mutable.LinkedHashSet[Path]

  def get(path: Path): Option[DirectoryEntry] = {
    val path2 = path.normalize
    accesses += path2
    directory.get(path2)
  }

  private def fingerprint(): Fingerprint[DirectorySnapshot] = {
    val entries: List[Entry[DirectorySnapshot, _]] =
      for (file <- accesses.toList) yield
        Entry(DirectoryElement(file), Fingerprint(HashedOption(directory.get(file))))
    Fingerprint(directory.hash, Some(entries))
  }
}

object FingerprintedDirectorySnapshot {
  def withFingerprint(directory: DirectorySnapshot): (FingerprintedDirectorySnapshot, () => Fingerprint[DirectorySnapshot]) = {
    val fpds = new FingerprintedDirectorySnapshot(directory)
    (fpds, fpds.fingerprint)
  }
}

case class DirectoryElement(path: Path) extends Element[DirectorySnapshot, HashedOption[DirectoryEntry]] {
  override def extract(directorySnapshot: DirectorySnapshot): HashedOption[DirectoryEntry] =
    HashedOption(directorySnapshot.get(path))

  override def hash: Hash[DirectoryElement.this.type] = ???

  override def extractHash(value: DirectorySnapshot): Hash[HashedOption[DirectoryEntry]] =
    extract(value).hash
}
