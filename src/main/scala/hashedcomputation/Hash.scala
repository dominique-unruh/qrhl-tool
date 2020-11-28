package hashedcomputation

import java.io.{ByteArrayInputStream, IOException, InputStream}
import java.nio.ByteBuffer
import java.nio.file.LinkOption.NOFOLLOW_LINKS
import java.nio.file.StandardWatchEventKinds.{ENTRY_CREATE, ENTRY_DELETE, ENTRY_MODIFY, OVERFLOW}
import java.nio.file.{FileSystem, Files, LinkOption, Path, Paths, StandardWatchEventKinds, WatchEvent, WatchKey, WatchService}
import java.security.MessageDigest
import java.util
import java.util.concurrent.TimeUnit.HOURS
import java.util.concurrent.atomic.{AtomicLong, AtomicReference}
import java.util.function.Consumer

import com.google.common.cache
import com.google.common.cache.{CacheBuilder, RemovalNotification}
import hashedcomputation.Directory.DirectoryListener
import hashedcomputation.Fingerprint.Entry
import hashedcomputation.FingerprintMap.MapElement
import hashedcomputation.HashedPromise.State
import org.apache.commons.codec.binary.Hex
import org.jetbrains.annotations.{NotNull, Nullable}
import org.log4s

import scala.annotation.tailrec
import scala.collection.JavaConverters.asScalaIteratorConverter
import scala.collection.concurrent.TrieMap
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.jdk.StreamConverters.StreamHasToScala
import scala.ref.{ReferenceWrapper, SoftReference, WeakReference}
import scala.util.Random
import scala.util.control.Breaks

import HashedValue.hashedValueHashable

class Hash[+B] private (private val hash: Array[Byte]) {
  override def toString: String = Hex.encodeHexString(hash).substring(0,7)

  override def hashCode(): Int = util.Arrays.hashCode(hash)
  override def equals(obj: Any): Boolean = obj match {
    case obj : Hash[_] =>
      util.Arrays.equals(hash, obj.hash)
    case _ => false
  }
}

object Hash {

  private val digest = MessageDigest.getInstance("SHA-256")
  private val hashLen = digest.getDigestLength

  def hashBytes(bytes: Array[Byte]): Hash[Nothing] = digest.synchronized {
    digest.reset()
    digest.update(bytes)
    new Hash(digest.digest())
  }

  def hashInt(int: Int): Hash[Nothing] = hashBytes(ByteBuffer.allocate(hashLen).put(0:Byte).putInt(int).array())
  def hashString(str: String): Hash[Nothing] = hashBytes(str.getBytes)
  def randomHash(): Hash[Nothing] = new Hash(Random.nextBytes(hashLen))
}

trait Element[A, B] extends HashedValue {
  def extract(value: A): B
  def extractHash(value: A) : Hash[B]
}

final case class IDElement[A : Hashable]() extends Element[A,A] {
  override def extract(value: A): A = value
  override def extractHash(value: A) : Hash[A] = Hashable.hash(value)
  override def hash: Hash[this.type] = ???
}

final case class NestedElement[A, B, C](outer: Element[A,B], inner: Element[B,C])
  extends  Element[A,C] {
  override def extract(value: A): C =
    inner.extract(outer.extract(value))
  override def extractHash(value: A): Hash[C] =
    inner.extractHash(outer.extract(value))

  override def hash: Hash[this.type] = ???
}

object NestedElement {
  def apply[A, B, C]
  (@NotNull outerElement: Element[A, B], innerElement: Element[B, C]): Element[A, C] = outerElement match {
    case _ : IDElement[_] => innerElement
    case _ => new NestedElement(outerElement, innerElement)
  }
}

case class Fingerprint[A : Hashable](hash: Hash[A], fingerprints: Option[Seq[Entry[A, _]]]) {
  def matches(value: A): Boolean = {
    if (hash == Hashable.hash(value)) true
    else {
      fingerprints match {
        case None => false
        case Some(fingerprints) =>
          fingerprints.forall(_.matches(value))
      }
    }
  }

  type U[B] = (Element[A,B], Hash[B])
  def unfold: Seq[U[_]] = {
    val result = new ListBuffer[U[_]]
    def unfold[B](fp: Fingerprint[B], element: Element[A,B]): Unit = fp.fingerprints match {
      case None => result.append((element, fp.hash) : U[B])
      case Some(fingerprints) =>
        def doEntry[C](entry: Entry[B,C]): Unit = {
          val subElement = NestedElement(element, entry.element)
          unfold(entry.fingerprint, subElement)
        }
        for (entry <- fingerprints) doEntry(entry)
    }

    unfold(this, IDElement())
    result.toList
  }
}

object Fingerprint {
  case class Entry[A, B](element: Element[A,B], fingerprint: Fingerprint[B]) {
    type OutT = B
    type InT = A
    def matches(value: A): Boolean = {
      val extracted = element.extract(value)
      fingerprint.matches(extracted)
    }
  }

  def apply[A : Hashable](hash: Hash[A]) = new Fingerprint[A](hash, None)
  def apply[A : Hashable](value: A) = new Fingerprint[A](Hashable.hash(value), None)
}

/** Type class for values with hashes */
trait Hashable[-A] {
  @NotNull def hash[A1 <: A](value: A1): Hash[A1]
}
object Hashable {
  @NotNull def hash[A: Hashable](value: A): Hash[A] =
    implicitly[Hashable[A]].hash(value)
}


trait HashedValue {
  /** Must return a stable value */
  @NotNull def hash: Hash[this.type]
}

object HashedValue {
  implicit val hashedValueHashable: Hashable[HashedValue] = new Hashable[HashedValue] {
    override def hash[A1 <: HashedValue](value: A1): Hash[A1] = value.hash
  }
}

trait HashedFunction[A, B] {
  @NotNull def compute(input: A): Future[(B @NotNull, Fingerprint[A] @NotNull)]
  @NotNull def hash: Hash[this.type]
}
object HashedFunction {
  def apply[A : Hashable, B](f: A => B): HashedFunction[A, B] = new HashedFunction[A,B] {
    override def compute(input: A): Future[(B, Fingerprint[A])] = Future {
      val result = f(input)
      (result, Fingerprint(Hashable.hash(input)))
    }

    override val hash: Hash[this.type] = Hash.randomHash()
  }
}

object HashedPromise {
  private def apply[A : Hashable, B : Hashable](state: State[A,B]) =
    new HashedPromise[A,B](new AtomicReference[State[A, B]](state))

  /** Note: does not add hashedValue to the cache! */
  def apply[A : Hashable](hashedValue: A): HashedPromise[HashedValue, A] =
    apply(State.Result[HashedValue,A](hashedValue))

  def apply[A : Hashable, B : Hashable](function: HashedFunction[A, B], input: HashedPromise[_, A]): HashedPromise[A, B] =
    apply(State.FunctionOnly(function, input))

  def apply[A : Hashable, B : Hashable](function: HashedFunction[A, B],
                                                input: HashedPromise[_, A], hash: Hash[B]): HashedPromise[A, B] =
    apply(State.FunctionAndHash(function, input, hash))

  def apply[A : Hashable, B : Hashable](hashedFunction: HashedFunction[A, B], input: A): HashedPromise[A, B] =
    apply(hashedFunction, HashedPromise(input))

  private sealed trait State[A, B]
  private object State {
    /** A state in which a computation function is available (but was not executed yet, nor the inputs computed) */
    sealed trait StateWithFunction[A, B] extends State[A,B] {
      val function : HashedFunction[A,B]
      def inputFuture: Future[A]
      def inputPromise: HashedPromise[_, A]
    }
    /** A state where a future with the hash is available (hash computation started or finished) */
    sealed trait HashFutureState[A,B] extends State[A,B] {
      def hashFuture : Future[Hash[B]]
    }
    /** A state where a future with the result is available (hash computation started or finished) */
    sealed trait ResultFutureState[A, B] extends HashFutureState[A,B] {
      def resultFuture : Future[B]
      def _hashFuture(implicit hashable: Hashable[B]): Future[Hash[B]] =
        resultFuture.map(Hashable.hash[B])
    }
    /** A state where all computations have been performed (but possibly failed) */
    sealed trait FinalState[A, B] extends HashFutureState[A,B] with ResultFutureState[A,B]
    sealed trait Computing[A, B] extends State[A,B]

    final case class HashAndInput[A : Hashable, B](function: HashedFunction[A,B], input: A, hash: Hash[B])
      extends HashFutureState[A,B] with StateWithFunction[A,B] {
      override def hashFuture: Future[Hash[B]] = Future.successful(hash)
      override def inputFuture: Future[A] = Future.successful(input)
      override def inputPromise: HashedPromise[_, A] = HashedPromise(input)
    }
    final case class Failed[A, B](exception: Throwable) extends FinalState[A,B] {
      override def hashFuture: Future[Hash[B]] = Future.failed(exception)
      override def resultFuture: Future[B] = Future.failed(exception)
    }
    final case class Locked[A, B]() extends State[A,B]
    final case class ComputingHash[A, B](override val hashFuture: Future[Hash[B]]) extends HashFutureState[A,B] with Computing[A,B]
    final case class ComputingResult[A, B : Hashable](override val resultFuture: Future[B]) extends ResultFutureState[A,B] with Computing[A,B] {
      override def hashFuture: Future[Hash[B]] = _hashFuture
    }
    final case class Result[A, B : Hashable](result: B) extends FinalState[A,B] {
      override def hashFuture: Future[Hash[B]] = Future.successful(Hashable.hash(result))
      override def resultFuture: Future[B] = Future.successful(result)
    }
    final case class FunctionOnly[A, B](override val function: HashedFunction[A, B], input: HashedPromise[_, A]) extends StateWithFunction[A,B] {
      override def inputFuture: Future[A] = input.get
      override def inputPromise: HashedPromise[_, A] = input
    }
    final case class FunctionAndHash[A, B]
          (override val function: HashedFunction[A, B], val input: HashedPromise[_, A],
           hash: Hash[B])
      extends StateWithFunction[A,B] with HashFutureState[A,B] {
      override def hashFuture: Future[Hash[B]] = Future.successful(hash)
      override def inputFuture: Future[A] = input.get
      override def inputPromise: HashedPromise[_, A] = input
    }
  }
}


class HashedPromise[A : Hashable, B : Hashable]
  (private val state: AtomicReference[HashedPromise.State[A,B]]) {
  //  private val state: AtomicReference[State[A, B]] = new AtomicReference(initialState)

  private def doCompute(function: HashedFunction[A,B], input: A) : Future[State.FinalState[A,B]] = {

    val future = for ((result, fingerprint) <- function.compute(input);
                      _ = Cache.register(result, function.hash, fingerprint))
      yield State.Result[A,B](result)

    future.recover { exception => State.Failed[A,B](exception) }

  }

  /** Tries to get the hash of the result, but without running the function (but potentially computing the input) */
  private def getHashByInputPromise(function: HashedFunction[A,B], inputPromise: HashedPromise[_, A]): Future[Option[Hash[B]]] = {
    val functionHash = function.hash
    for (inputHash <- inputPromise.getHash; // TODO: catch exception
         hashOption = Cache.getHashByInputHash(functionHash, inputHash);
         hashOption2 <- hashOption match {
           case Some(hash) => Future.successful(Some(hash))
           case None => for (input <- inputPromise.get) yield Cache.getHashByInput(functionHash, input)
         })
      yield hashOption2
  }

  /** Guarantees that state is a HashFutureState from now on */
  @tailrec
  private def triggerHashComputation(): Unit = {
    val currentState = state.get()
    currentState match {
      case _ : State.HashFutureState[A,B] =>
      case _ : State.Locked[A,B] =>
        Thread.sleep(1)
        triggerHashComputation()
      case st : State.StateWithFunction[A,B] =>
        if (state.compareAndSet(st, State.Locked())) {
          val function = st.function
          val inputPromise = st.inputPromise
          val future = for (hashOption <- getHashByInputPromise(function, inputPromise);
                            newState <- hashOption match {
                              case Some(hash) =>
                                inputPromise.peek match {
                                  case None =>
                                    Future.successful(State.FunctionAndHash[A,B](function, inputPromise, hash))
                                  case Some(inputFuture) =>
                                    for (inputValue <- inputFuture)
                                      yield State.HashAndInput[A,B](function, inputValue, hash)
                                }
                              case None =>
                                for (inputValue <- inputPromise.get; // TODO: Catch exception!
                                     newState <- doCompute(function, inputValue))
                                  yield newState
                            };
                            _ = state.set(newState);
                            hash <- newState.hashFuture)
            yield hash
          state.set(State.ComputingHash[A, B](future))
        } else
          triggerHashComputation()
    }
  }

  /** Guarantees that stat is a ResultFutureState from now on (unless it's a Computing state, in which case triggerComputation needs to be invoked again
   * when the computation is finished). */
  @tailrec
  private def triggerComputation(): Unit = {
    val currentState = state.get()
    currentState match {
      case _ : State.Computing[A,B] =>
      case _ : State.ResultFutureState[A,B] =>
      case _ : State.Locked[A,B] =>
        Thread.sleep(1)
        triggerComputation()
      case st: State.StateWithFunction[A, B] =>
        if (state.compareAndSet(st, State.Locked())) {
          val function = st.function
          val inputPromise = st.inputPromise
          val future = for (hashOption <- getHashByInputPromise(function, inputPromise);
                            resultOption = hashOption.flatMap(Cache.getByHash).asInstanceOf[Option[B]];
                            newState <- resultOption match {
                              case Some(result) => Future.successful(State.Result[A, B](result))
                              case None =>
                                for (inputValue <- inputPromise.get; // TODO catch exceptions
                                     result <- doCompute(function, inputValue))
                                  yield result
                            };
                            _ = state.set(newState);
                            result <- newState.resultFuture)
            yield result
          state.set(State.ComputingResult[A, B](future))
        } else
          triggerComputation()
    }
  }


  def getHash: Future[Hash[B]] = state.get() match {
    case st: State.HashFutureState[A, B] => st.hashFuture
    case _ =>
      triggerHashComputation()
      getHash
  }

  def peek: Option[Future[B]] = state.get() match {
    case st : State.ResultFutureState[A, B] => Some(st.resultFuture)
    case _ => None
  }

  def get: Future[B] = state.get() match {
    case st: State.ResultFutureState[A, B] => st.resultFuture
    case st: State.ComputingHash[A, B] =>
      for (_ <- st.hashFuture; result <- get) yield result
    case _ =>
      triggerComputation()
      get
  }
}

object Cache {
  private val logger = log4s.getLogger

  private val hashCache: cache.Cache[Hash[_], AnyRef] = cache.CacheBuilder.newBuilder()
    .softValues()
    .expireAfterAccess(1, HOURS)
    .build()

  private val outputCache: cache.Cache[(Hash[_],Hash[_]), Hash[_]] = cache.CacheBuilder.newBuilder()
    .softValues()
    .expireAfterAccess(1, HOURS)
    .build()

  /** Query with (0,computationHash) -> Get (id,Element)
   * Get the hash of the extraction of that Element, query (id,hash), get next (id,Element), etc.
   * Done when getting a hash instead of an Element
   * The (id,Element) is actually a Seq, then need to backtrace over all choices
   * */
  private val fingerprintCache: cache.Cache[(Long,Hash[_]), Either[(Long,Element[_,_]), Hash[_]]] = cache.CacheBuilder.newBuilder()
    .softValues()
    .expireAfterAccess(1, HOURS)
    .build()

  private val fingerprintIdCounter = new AtomicLong(1)

  def getByHash[T](@NotNull hash: Hash[T]): Option[T] = Option(hashCache.getIfPresent(hash)).asInstanceOf[Option[T]]

  private[hashedcomputation] def register[A, B : Hashable]
  (@NotNull value: B, @NotNull computationHash: Hash[_], @NotNull fingerprint: Fingerprint[A]): Unit = {
    logger.debug(s"Registering $value in cache")
    val valueHash = Hashable.hash(value)
    hashCache.put(valueHash, value.asInstanceOf[AnyRef])
    outputCache.put((computationHash, fingerprint.hash), valueHash)

    logger.debug(s"Registering ${(computationHash, fingerprint, valueHash)} in fingerprints")

    def put[C](id: Long, hash: Hash[_], element: Element[C, _]): Long = {
      val entry = fingerprintCache.asMap().compute((id, hash), { (_, entry) =>
        entry match {
          case null =>
            Left((fingerprintIdCounter.incrementAndGet(), element))
          case Left((id, oldElement)) =>
            if (oldElement == element)
              entry
            else {
              // This can only happen if the Fingerprint-generation is nondeterministic
              Left((fingerprintIdCounter.incrementAndGet(), element))
            }
          case _ =>
            // We already have a result hash, we don't need a less precise Fingerprint, should probably not happen with welldesigned fingerprinters except maybe due to nondeterministism
            entry
        }
      })
      entry match {
        case Left((id, _)) => id
        case _ => Breaks.break() // Means we are done
      }
    }

    // TODO: We are ignoring the Fingerprint.hash entries when there are subfingerprints which would allow shortcutting

    val (id, hash) = fingerprint.unfold.foldLeft[(Long,Hash[_])]((0L,computationHash : Hash[_])) {
      case ((id, currentHash), (element, elementHash : Hash[_])) =>
        val id2 = put(id, currentHash, element)
        (id2, elementHash)
    }
    fingerprintCache.put((id, hash), Right(valueHash))

/*    def storeEntries[C](id: Long, currentHash: Hash,
                                       @Nullable outerElement: Element[A, C],
                                       entries: Seq[Fingerprint.Entry[C, _]]): (Long, Hash) = {
      def storeEntry[D](id: Long, hash: Hash, entry: Entry[C, D]): (Long, Hash) = {
        val element = NestedElement(outerElement, entry.element)
//        val extracted: D = entry.element.extract(extracted)
        entry.fingerprint.fingerprints match {
          case None =>
            val id2 = put(id, hash, element)
            (id2, entry.fingerprint.hash)
          case Some(entries) =>
            storeEntries[D](id, hash, element, entries)
        }
      }

      entries.foldLeft((id, currentHash)) { case ((id, hash), entry) => storeEntry(id, hash, entry) }
    }

    Breaks.breakable {
      val (id, hash) = fingerprint.fingerprints match {
        case Some(fingerprints) =>
          storeEntries[A](0, computationHash, IDElement[A](), fingerprints)
        case None =>
          (0, computationHash)
      }
      fingerprintCache.put((id, hash), Right(valueHash))
    }*/
  }

  def getHashByInputHash[A, B](@NotNull computationHash: Hash[HashedFunction[A,B]], @NotNull inputHash: Hash[A]): Option[Hash[B]] =
    Option(outputCache.getIfPresent((computationHash, inputHash))).asInstanceOf[Option[Hash[B]]]

  def getHashByInput[A, B](@NotNull computationHash: Hash[HashedFunction[A,B]],
                                      @NotNull input: A): Option[Hash[B]] = {
    logger.debug(s"Searching for $computationHash($input) in fingerprints")

    var hash : Hash[_] = computationHash
    var id = 0L
    while (true) {
      fingerprintCache.getIfPresent((id,hash)) match {
        case null => return None
        case Right(hash) => return Some(hash.asInstanceOf[Hash[B]])
        case Left((id2, element)) =>
          val element2 = element.asInstanceOf[Element[A,_]]
          id = id2
          hash = element2.extractHash(input)
      }
    }
    throw new AssertionError("Unreachable code")
  }

/*
  def getByInput[A](@NotNull computationHash: Hash, @NotNull input: A): Option[HashedValue] =
    for (hash <- getHashByInput(computationHash, input);
         value <- getByHash(hash))
      yield value
*/
}

trait Fingerprinter[A] {
  /** Returns the fingerprint of all actions since creation (implies [[dispose]]) */
  def fingerprint(): Fingerprint[A]
  /** Stops tracking accesses */
  def dispose(): Unit
}

trait HashedOption[+A] extends HashedValue
object HashedOption {
  def hash[A : Hashable](value: Option[A]): Hash[HashedOption[A]] = value match {
    case None => HashedNone.hash
    case Some(value2) => hash(value2)
  }
  def hash[A : Hashable](value: A): Hash[HashedSome[A]] = Hash.hashString("OPTION " + Hashable.hash(value).toString) // TODO adhoc
  def apply[A : Hashable](value: Option[A]): HashedOption[A] = value match {
    case None => HashedNone
    case Some(x) => HashedSome(x)
  }
}

case object HashedNone extends HashedOption[Nothing] {
  override def hash: Hash[this.type] = Hash.hashString(getClass.getName)
}
case class HashedSome[A : Hashable](value: A) extends HashedOption[A] {
  override def hash: Hash[this.type] = HashedOption.hash[A](value).asInstanceOf[Hash[this.type]]
}

final class HashedMap[A, B]
  (val _hash: Hash[Map[A,B]], val map: Map[A,B]) extends Map[A,B] with HashedValue {

  override def removed(key: A): Map[A, B] = map.removed(key)
  override def updated[V1 >: B](key: A, value: V1): Map[A, V1] = map.updated(key, value)
  override def get(key: A): Option[B] = map.get(key)
  override def iterator: Iterator[(A, B)] = map.iterator

  override def hash: Hash[this.type] = _hash.asInstanceOf[Hash[this.type]]
}

/** Not thread safe */
final class FingerprintMap[A, B : Hashable]
  (private val map: HashedMap[A,B]) extends Map[A,B] {

  private val accesses = new mutable.LinkedHashSet[A]

  def get(key: A): Option[B] = {
    accesses += key
    map.get(key)
  }

  private def fingerprint(): Fingerprint[HashedMap[A,B]] = {
    val entries: List[Entry[HashedMap[A,B], HashedOption[B]]] =
      for (key <- accesses.toList) yield
        Entry(MapElement(key), Fingerprint(HashedOption(map.get(key))))
    Fingerprint(map.hash, Some(entries))
  }

  override def removed(key: A): Map[A, B] = ???

  override def updated[V1 >: B](key: A, value: V1): Map[A, V1] = ???

  override def iterator: Iterator[(A, B)] = ???
}

object FingerprintMap {
  def withFingerprint[A, B : Hashable]
    (map: HashedMap[A,B]):
    (FingerprintMap[A,B], () => Fingerprint[HashedMap[A,B]]) = {

    val fpMap = new FingerprintMap(map)
    (fpMap, fpMap.fingerprint)
  }

  case class MapElement[A, B : Hashable](key: A)
    extends Element[HashedMap[A,B], HashedOption[B]] {
    override def hash: Hash[this.type] = ???

    override def extract(value: HashedMap[A, B]): HashedOption[B] =
      HashedOption(value.get(key))
    override def extractHash(value: HashedMap[A, B]): Hash[HashedOption[B]] =
      HashedOption.hash(value.get(key))
  }
}

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
  private val watchServices = new TrieMap[FileSystem, WatchService]

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
