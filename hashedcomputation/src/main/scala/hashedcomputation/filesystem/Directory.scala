package hashedcomputation.filesystem

import java.io.{ByteArrayInputStream, IOException, InputStream}
import java.nio.file.LinkOption.NOFOLLOW_LINKS
import java.nio.file.StandardWatchEventKinds.{ENTRY_CREATE, ENTRY_DELETE, ENTRY_MODIFY, OVERFLOW}
import java.nio.file.{FileSystem, FileSystems, Files, Path, WatchKey, WatchService}
import java.util.concurrent.atomic.AtomicReference
import de.unruh.isabelle.misc.SharedCleaner
import hashedcomputation.Fingerprint.Entry
import hashedcomputation.{Element, Fingerprint, Hash, HashTag, HashedOption, HashedValue, RawHash, WithByteArray}
import hashedcomputation.filesystem.Directory.DirectoryListener
import hashedcomputation.filesystem.DirectorySnapshot.logger
import org.jetbrains.annotations.NotNull
import org.log4s
import org.log4s.Logger

import java.lang.ref
import scala.collection.concurrent.TrieMap
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.jdk.CollectionConverters.{IterableHasAsScala, IteratorHasAsScala}
import scala.ref.{ReferenceWrapper, SoftReference, WeakReference}

sealed abstract class GenericDirectory protected (partial: Boolean) {
  private val subdirs = new TrieMap[String, Directory]
  private val interesting = if (partial) new TrieMap[String, Unit] else null
  private val currentSnapshot = new AtomicReference(makeSnapshot)
  protected val watchKey: WatchKey = registerWatcher()

  @NotNull protected def makeSnapshot : DirectorySnapshot

  protected def registerWatcher() : WatchKey
  def registerInterest(path: List[String]): Unit = if (partial) {
    path match {
      case Nil =>
      case file :: rest =>
        var notify = false
        interesting += file -> ()
        currentSnapshot.get.content.get(file) match {
          case Some(_: UnresolvedDirectoryEntry) =>
            currentSnapshot.updateAndGet { updateSnapshot(file, _) }
            notify = true
          case _ =>
        }
        if (rest.nonEmpty)
          for (subdir <- subdirs.get(file))
            subdir.registerInterest(rest)
        if (notify) notifyParent()
    }
  }

  private[filesystem] def pathToList(path: Path) : List[String]

  def registerInterest(path: Path): Unit =
    if (partial)
      registerInterest(pathToList(path))

  protected def notifyParent(): Unit
  protected def resolve(path: String): Path

  protected def updateSnapshot(path: String, snapshot: DirectorySnapshot): DirectorySnapshot = {
//    GenericDirectory.logger.debug(s"updateSnapshot: $path $snapshot")
    if (partial && !interesting.contains(path))
      snapshot.updated(path, new UnresolvedDirectoryEntry(this, path))
    else {
      val fullPath = resolve(path)
      val entry = try {
        if (Files.isDirectory(fullPath)) {
          val dir = subdirs.getOrElseUpdate(path, {
            new Directory(fullPath, this, path, partial) })
          dir.snapshot()
        } else if (Files.isRegularFile(fullPath)) {
          new FileSnapshot(fullPath)
        } else
          UnknownDirectoryEntry
      } catch {
        case e : java.nio.file.AccessDeniedException =>
          AccessDeniedEntry
      }
      snapshot.updated(path, entry)
    }
  }

  def registerInterestEverything(): Unit =
    if (partial) {
      for ((file, content : UnresolvedDirectoryEntry) <- currentSnapshot.get.content) {
        interesting += file -> ()
        currentSnapshot.updateAndGet { updateSnapshot(file,_) }
      }
      notifyParent()
    }

  def snapshot(): DirectorySnapshot = currentSnapshot.get


  protected[filesystem] def notifySubdirectoryChange(subdir: String): Unit = {
//    GenericDirectory.logger.debug(s"Notification from child $subdir")
    currentSnapshot.updateAndGet { updateSnapshot(subdir, _) }
    notifyParent()
  }

  protected def dispose(): Unit

  protected def entryCreated(path: String): Unit = {
    for (subdir <- subdirs.remove(path)) subdir.dispose()
    currentSnapshot.updateAndGet { updateSnapshot(path, _) }
    notifyParent()
  }
  protected def entryModified(path: String): Unit = {
    assert(currentSnapshot != null)
    assert(path != null)
    currentSnapshot.updateAndGet { updateSnapshot(path, _) }
    notifyParent()
  }
  protected def entryDeleted(path: String): Unit = {
    for (subdir <- subdirs.remove(path)) subdir.dispose()
    currentSnapshot.updateAndGet { _.removed(path) }
    notifyParent()
  }
  protected def refreshAll(): Unit = {
    currentSnapshot.set(makeSnapshot)
    notifyParent()
  }

  private[filesystem] def pathAsString: String
}

object GenericDirectory {
  private val logger = log4s.getLogger
}

class Directory private[filesystem] (val path: Path, parent: GenericDirectory, parentKey: String,
                                     partial : Boolean) extends GenericDirectory(partial) with DirectoryListener {
  //  def snapshot : DirectorySnapshot = new DirectorySnapshot(this)
  override def registerWatcher(): WatchKey = Directory.watchDirectory(path, this)

  override def pathToList(path: Path) : List[String] = {
    assert(!path.isAbsolute)
    path.iterator().asScala.map(_.toString).toList
  }

  override protected def resolve(path: String): Path = this.path.resolve(path)

  override protected def makeSnapshot : DirectorySnapshot =
    Files.list(path).iterator().asScala.foldLeft(new DirectorySnapshot(this, Map.empty)) { (snapshot, file) =>
      updateSnapshot(this.path.relativize(file).toString, snapshot)
    }

  override def dispose(): Unit = Directory.unwatchDirectory(this, watchKey)

  override protected def notifyParent(): Unit = {
//    Directory.logger.debug(s"notifyParent: $parent $parentKey")
    if (parent!=null) parent.notifySubdirectoryChange(parentKey)
  }

  override def onCreate(path: Path): Unit = {
    assert(path.getNameCount==1)
    entryCreated(path.toString)
  }
  override def onModify(path: Path): Unit = {
    assert(path.getNameCount==1)
    entryModified(path.toString)
  }
  override def onDelete(path: Path): Unit = {
    assert(path.getNameCount==1)
    entryDeleted(path.toString)
    }
  override def onOverflow(): Unit = {
    refreshAll()
  }

  override def pathAsString: String = path.toString
}

class RootsDirectory private[filesystem] (fileSystem: FileSystem)
  extends GenericDirectory(partial=true) {
  protected override def registerWatcher(): WatchKey = null

  private[filesystem] override def pathToList(path: Path): List[String] = {
    assert(path.isAbsolute, s"$path not absolute")
    assert(path.getFileSystem==fileSystem)
    path.getRoot.toString :: path.iterator().asScala.map(_.toString).toList
  }

  override protected def resolve(path: String): Path = Path.of(path)

  override protected def makeSnapshot : DirectorySnapshot = {
    fileSystem.getRootDirectories.asScala.foldLeft(new DirectorySnapshot(this, Map.empty)) { (snapshot, root) =>
      updateSnapshot(root.toString, snapshot)
    }
  }

  protected override def dispose(): Unit = {}

  override protected def notifyParent(): Unit = {}

  override def pathAsString: String = "<roots>"
}

object RootsDirectory {
  def apply(fileSystem: FileSystem = FileSystems.getDefault): RootsDirectory =
    new RootsDirectory(fileSystem)
}

object Directory {
  def apply(path: Path, partial: Boolean = false) =
    new Directory(path.normalize.toAbsolutePath, parent=null, null, partial)

  trait DirectoryListener {
    def onCreate(path: Path): Unit
    def onModify(path: Path): Unit
    def onDelete(path: Path): Unit
    def onOverflow(): Unit
  }

  /** Access in `Directory.synchronized`. */
  private val listeners = mutable.HashMap[WatchKey, List[WeakReference[DirectoryListener]]]()

/*  private val listeners = CacheBuilder
    .newBuilder()
    .weakValues()
    .removalListener[WatchKey, DirectoryListener]((notification:RemovalNotification[WatchKey,DirectoryListener]) => notification.getKey.cancel())
    .build[WatchKey, DirectoryListener]()*/

  private val logger = log4s.getLogger
  private val watchServices = new TrieMap[java.nio.file.FileSystem, WatchService]

  def unwatchDirectory(listener: DirectoryListener, watchKey: WatchKey): Unit = synchronized {
    listeners.get(watchKey) match {
      case None => throw new IllegalArgumentException(s"Trying to remove listener $listener from unknown watchkey $watchKey")
      case Some(ls) =>
        val ls2 = ls filter { ref =>
          val content = ref.underlying.get
          (content == null) || (content == listener) }
        if (ls2.isEmpty) {
          watchKey.cancel()
          watchKey.pollEvents()
          listeners.remove(watchKey)
        } else
          listeners.put(watchKey, ls2)
    }
  }

  private def unwatchDirectoryRef(listenerRef: WeakReference[DirectoryListener], watchKey: WatchKey): Unit = synchronized {
    listeners.get(watchKey) match {
      case None =>
      case Some(ls) =>
        val ls2 = ls filterNot { ref => ref eq listenerRef }
        if (ls2.isEmpty) {
          watchKey.cancel()
          watchKey.pollEvents()
          listeners.remove(watchKey)
        } else
          listeners.put(watchKey, ls2)
    }
  }

  def watchDirectory(path: Path, listener: DirectoryListener): WatchKey = {
    val filesystem = path.getFileSystem
    val watchService = watchServices.getOrElseUpdate(filesystem, {
//      logger.debug(s"Found new filesystem: $filesystem")
      val watchService = filesystem.newWatchService()
      val thread = new Thread(new PollWatchService(watchService), s"Filesystem watcher for ${filesystem.getRootDirectories.asScala.mkString(";")}")
      thread.setDaemon(true)
      thread.start()
      watchService
    })
    /* We have to synchronize this even if `listeners` is thread-safe:
     * The watch service can send an event right after creation and before we added the key to `listeners`, leading to an error in PollWatchService.run
     */
    synchronized {
      val watchKey = path.register(watchService, ENTRY_CREATE, ENTRY_DELETE, ENTRY_MODIFY)
      logger.debug(s"New watch service key $watchKey for $path in ${filesystem.getRootDirectories.asScala.mkString(";")}")
      val ref = new WeakReference(listener)
      listeners.updateWith(watchKey) {
        case None => Some(List(ref))
        case Some(ls) => Some(ref :: ls)
      }
      SharedCleaner.register(listener, () => unwatchDirectoryRef(ref, watchKey))
      watchKey
    }
  }

  private class PollWatchService(watchService: WatchService) extends Runnable {
    override def run(): Unit = {
      while (true) {
        val key = watchService.take()
        try {
          val events = key.pollEvents()
          val keyListeners = synchronized(listeners.getOrElse(key, { logger.error(s"Did not find a listener for key $key"); Nil }))
          for (listenerRef <- keyListeners) {
            listenerRef.get match {
              case None =>
              case Some(listener) =>
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
        } finally
          key.reset()
      }
    }
  }
}

sealed trait MaybeDirectoryEntry extends HashedValue
sealed trait DirectoryEntry extends MaybeDirectoryEntry

object UnknownDirectoryEntry extends DirectoryEntry {
  override def hash: Hash[UnknownDirectoryEntry.this.type] = Hash.randomHash()
}

object AccessDeniedEntry extends DirectoryEntry {
  override def hash: Hash[this.type] = Hash.randomHash()
}

final class FileSnapshot(path: Path) extends DirectoryEntry {
  def inputStream(): InputStream =
    new ByteArrayInputStream(content)

  private var contentRef : ReferenceWrapper[Array[Byte]] = _
  val hash: Hash[this.type] = {
    val content = Files.readAllBytes(path)
    val hash = FileSnapshot.hashContent(content)
    contentRef = WeakReference(content)
    hash.asInstanceOf[Hash[this.type]]
  }

  def content: Array[Byte] = {
    contentRef match {
      case WeakReference(content) =>
        contentRef = SoftReference(content)
        content
      case SoftReference(content) => content
      case _ =>
        val content = Files.readAllBytes(path)
        if (hash != FileSnapshot.hashContent(content))
          throw new IOException("Snapshot outdated")
        contentRef = SoftReference(content)
        content
    }
  }
}
object FileSnapshot {
  private val hashTag = HashTag.create[FileSnapshot]
  private def hashContent(content: Array[Byte]): Hash[FileSnapshot] =
    hashTag(RawHash.hashBytes(content))
}

class DirectorySnapshot private[filesystem] (directory: GenericDirectory,
                                             private[filesystem] val content: Map[String, MaybeDirectoryEntry])
  extends DirectoryEntry with Map[String, DirectoryEntry] with HashedValue {

  def dump(hideUnresolved: Boolean = true, indent: String = ""): Unit = {
    for ((file, entry) <- content) {
      if (!(hideUnresolved && entry.isInstanceOf[UnresolvedDirectoryEntry]))
        logger.debug(s"* $indent$file (${entry.getClass.getSimpleName})")
      entry match {
        case subdir: DirectorySnapshot => subdir.dump(hideUnresolved = hideUnresolved, indent = indent + "  ")
        case _ =>
      }
    }
  }

  override def toString(): String = s"DirectorySnapshot#$hash"

  def getFile(path: Path): Option[FileSnapshot] = get(path) match {
    case Some(file : FileSnapshot) => Some(file)
    case None => None
  }


  override lazy val hash: Hash[this.type] = {
    val hashes = ListBuffer[WithByteArray]()
    for ((s,h) <- content.toList.sortBy(_._1)) {
      hashes += RawHash.hashString(s)
      hashes += h.hash.rawHash
    }
    DirectorySnapshot.hashTag(hashes.toSeq : _*)
      .asInstanceOf[Hash[this.type]]
  }

  override def get(key: String): Option[DirectoryEntry] = content.get(key) map {
    case entry: DirectoryEntry => entry
    case entry: UnresolvedDirectoryEntry => entry.failWithInterest()
  }


  def get(path: Path): Option[DirectoryEntry] =
    get(directory.pathToList(path))

  def get(path: List[String]): Option[DirectoryEntry] = path match {
    case Nil => Some(this)
    case file :: rest =>
      content.get(file) match {
        case Some(dir : DirectorySnapshot) => dir.get(rest)
        case Some(entry : UnresolvedDirectoryEntry) =>
          entry.failWithInterest(rest)
        case Some(entry : DirectoryEntry) =>
          if (rest.isEmpty) Some(entry) else None
        case None => None
      }
    }

  override def iterator: Iterator[(String, DirectoryEntry)] = content.iterator.map {
    case (str, entry: DirectoryEntry) => (str,entry)
    case (_, entry: UnresolvedDirectoryEntry) => entry.failWithInterest(everything = true)
  }
  override def removed(key: String): DirectorySnapshot =
    new DirectorySnapshot(directory, content.removed(key))

  override def updated[V1 >: DirectoryEntry](key: String, value: V1): Map[String, V1] =
    ???

  private[hashedcomputation] def updated(key: String, value: MaybeDirectoryEntry) : DirectorySnapshot =
    new DirectorySnapshot(directory, content.updated(key, value))

  def updated(key: String, value: DirectoryEntry) : DirectorySnapshot =
    updated(key, value : MaybeDirectoryEntry)

  override def size: Int = content.size
}


object DirectorySnapshot {
  private val hashTag: HashTag[DirectorySnapshot] = HashTag.create()

  private val logger: Logger = log4s.getLogger
}

/*

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
*/

/*
object FingerprintedDirectorySnapshot {
  def withFingerprint(directory: DirectorySnapshot): (FingerprintedDirectorySnapshot, () => Fingerprint[DirectorySnapshot]) = {
    val fpds = new FingerprintedDirectorySnapshot(directory)
    (fpds, fpds.fingerprint)
  }
}
*/

private case class UnresolvedDirectoryEntry(directory: GenericDirectory, path: String) extends MaybeDirectoryEntry {
  def failWithInterest(subdir: List[String] = Nil, everything: Boolean = false): Nothing = {
    if (everything)
      directory.registerInterestEverything()
    else {
      directory.registerInterest(path::subdir)
    }
    throw new OutdatedSnapshotException(s"$path in ${directory.pathAsString} was not read yet. Try again with a fresh directory snapshot.")
  }

  override val hash: Hash[UnresolvedDirectoryEntry.this.type] = UnresolvedDirectoryEntry.hash
}
private object UnresolvedDirectoryEntry {
  private val hash = Hash.randomHash() // TODO: stable hash
}

class OutdatedSnapshotException(message: String) extends IOException(message)

