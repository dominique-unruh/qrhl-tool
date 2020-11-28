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
import scala.collection.concurrent.TrieMap
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.ref.{ReferenceWrapper, SoftReference, WeakReference}
import scala.util.Random
import scala.util.control.Breaks

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

trait Element[A <: HashedValue, B <: HashedValue] extends HashedValue {
  def extract(value: A): B
}

final case class IDElement[A <: HashedValue]() extends Element[A,A] {
  override def extract(value: A): A = value
  override def hash: Hash[this.type] = ???
}

final case class NestedElement[A <: HashedValue, B <: HashedValue, C <: HashedValue](outer: Element[A,B], inner: Element[B,C])
  extends  Element[A,C] {
  override def extract(value: A): C =
    inner.extract(outer.extract(value))

  override def hash: Hash[this.type] = ???
}

object NestedElement {
  def apply[A <: HashedValue, B <: HashedValue, C <: HashedValue]
  (@NotNull outerElement: Element[A, B], innerElement: Element[B, C]): Element[A, C] = outerElement match {
    case _ : IDElement[_] => innerElement
    case _ => new NestedElement(outerElement, innerElement)
  }
}

case class Fingerprint[A <: HashedValue](hash: Hash[A], fingerprints: Option[Seq[Entry[A, _<:HashedValue]]]) {
  def matches(value: A): Boolean = {
    if (hash == value.hash) true
    else {
      fingerprints match {
        case None => false
        case Some(fingerprints) =>
          fingerprints.forall(_.matches(value))
      }
    }
  }

  type U[B <: HashedValue] = (Element[A,B], Hash[B])
  def unfold: Seq[U[_ <: HashedValue]] = {
    val result = new ListBuffer[U[_ <: HashedValue]]
    def unfold[B <: HashedValue](fp: Fingerprint[B], element: Element[A,B]): Unit = fp.fingerprints match {
      case None => result.append((element, fp.hash) : U[B])
      case Some(fingerprints) =>
        def doEntry[C <: HashedValue](entry: Entry[B,C]): Unit = {
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
  case class Entry[A <: HashedValue, B <: HashedValue](element: Element[A,B], fingerprint: Fingerprint[B]) {
    type OutT = B
    type InT = A
    def matches(value: A): Boolean = {
      val extracted = element.extract(value)
      fingerprint.matches(extracted)
    }
  }

  def apply[A <: HashedValue](hash: Hash[A]) = new Fingerprint[A](hash, None)
  def apply[A <: HashedValue](value: A) = new Fingerprint[A](value.hash, None)
}

trait HashedValue {
  /** Must return a stable value */
  @NotNull def hash: Hash[this.type]
}

trait HashedFunction[A <: HashedValue, B <: HashedValue] {
  @NotNull def compute(input: A): Future[(B @NotNull, Fingerprint[A] @NotNull)]
  @NotNull def hash: Hash[this.type]
}
object HashedFunction {
  def apply[A <: HashedValue, B <: HashedValue](f: A => B): HashedFunction[A, B] = new HashedFunction[A,B] {
    override def compute(input: A): Future[(B, Fingerprint[A])] = Future {
      val result = f(input)
      (result, Fingerprint(input.hash))
    }

    override val hash: Hash[this.type] = Hash.randomHash()
  }
}

object HashedPromise {
  private def apply[A <: HashedValue, B <: HashedValue](state: State[A,B]) =
    new HashedPromise[A,B](new AtomicReference[State[A, B]](state))

  /** Note: does not add hashedValue to the cache! */
  def apply[A <: HashedValue](hashedValue: A): HashedPromise[HashedValue, A] =
    apply(State.Result[HashedValue,A](hashedValue))

  def apply[A <: HashedValue, B <: HashedValue](function: HashedFunction[A, B], input: HashedPromise[_ <: HashedValue, A]): HashedPromise[A, B] =
    apply(State.FunctionOnly(function, input))

  def apply[A <: HashedValue, B <: HashedValue](function: HashedFunction[A, B],
                                                input: HashedPromise[_ <: HashedValue, A], hash: Hash[B]): HashedPromise[A, B] =
    apply(State.FunctionAndHash(function, input, hash))

  def apply[A <: HashedValue, B <: HashedValue](hashedFunction: HashedFunction[A, B], input: A): HashedPromise[A, B] =
    apply(hashedFunction, HashedPromise(input))

  private sealed trait State[A, B]
  private object State {
    /** A state in which a computation function is available (but was not executed yet, nor the inputs computed) */
    sealed trait StateWithFunction[A <: HashedValue, B <: HashedValue] extends State[A,B] {
      val function : HashedFunction[A,B]
      def inputFuture: Future[A]
      def inputPromise: HashedPromise[_ <: HashedValue, A]
    }
    /** A state where a future with the hash is available (hash computation started or finished) */
    sealed trait HashFutureState[A,B] extends State[A,B] {
      def hashFuture : Future[Hash[B]]
    }
    /** A state where a future with the result is available (hash computation started or finished) */
    sealed trait ResultFutureState[A,B <: HashedValue] extends HashFutureState[A,B] {
      def resultFuture : Future[B]
      override def hashFuture: Future[Hash[B]] = resultFuture.map(_.hash)
    }
    /** A state where all computations have been performed (but possibly failed) */
    sealed trait FinalState[A <: HashedValue, B <: HashedValue] extends HashFutureState[A,B] with ResultFutureState[A,B]
    sealed trait Computing[A <: HashedValue, B <: HashedValue] extends State[A,B]

    final case class HashAndInput[A <: HashedValue, B <: HashedValue](function: HashedFunction[A,B], input: A, hash: Hash[B])
      extends HashFutureState[A,B] with StateWithFunction[A,B] {
      override def hashFuture: Future[Hash[B]] = Future.successful(hash)
      override def inputFuture: Future[A] = Future.successful(input)
      override def inputPromise: HashedPromise[_ <: HashedValue, A] = HashedPromise(input)
    }
    final case class Failed[A <: HashedValue, B <: HashedValue](exception: Throwable) extends FinalState[A,B] {
      override def hashFuture: Future[Hash[B]] = Future.failed(exception)
      override def resultFuture: Future[B] = Future.failed(exception)
    }
    final case class Locked[A <: HashedValue, B <: HashedValue]() extends State[A,B]
    final case class ComputingHash[A <: HashedValue, B <: HashedValue](override val hashFuture: Future[Hash[B]]) extends HashFutureState[A,B] with Computing[A,B]
    final case class ComputingResult[A <: HashedValue, B <: HashedValue](override val resultFuture: Future[B]) extends ResultFutureState[A,B] with Computing[A,B]
    final case class Result[A <: HashedValue, B <: HashedValue](result: B) extends FinalState[A,B] {
      override def hashFuture: Future[Hash[B]] = Future.successful(result.hash)
      override def resultFuture: Future[B] = Future.successful(result)
    }
    final case class FunctionOnly[A <: HashedValue, B <: HashedValue](override val function: HashedFunction[A, B], input: HashedPromise[_ <: HashedValue, A]) extends StateWithFunction[A,B] {
      override def inputFuture: Future[A] = input.get
      override def inputPromise: HashedPromise[_ <: HashedValue, A] = input
    }
    final case class FunctionAndHash[A <: HashedValue, B <: HashedValue]
          (override val function: HashedFunction[A, B], val input: HashedPromise[_ <: HashedValue, A],
           hash: Hash[B])
      extends StateWithFunction[A,B] with HashFutureState[A,B] {
      override def hashFuture: Future[Hash[B]] = Future.successful(hash)
      override def inputFuture: Future[A] = input.get
      override def inputPromise: HashedPromise[_ <: HashedValue, A] = input
    }
  }
}


class HashedPromise[A <: HashedValue, B <: HashedValue](private val state: AtomicReference[HashedPromise.State[A,B]]) extends AnyVal {
  //  private val state: AtomicReference[State[A, B]] = new AtomicReference(initialState)

  private def doCompute(function: HashedFunction[A,B], input: A) : Future[State.FinalState[A,B]] = {
    val future = for ((result, fingerprint) <- function.compute(input);
                      _ = Cache.register(result, function.hash, fingerprint))
      yield State.Result[A,B](result)
    future.recover { exception => State.Failed[A,B](exception) }
  }

  /** Tries to get the hash of the result, but without running the function (but potentially computing the input) */
  private def getHashByInputPromise(function: HashedFunction[A,B], inputPromise: HashedPromise[_<:HashedValue,A]): Future[Option[Hash[B]]] = {
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

  private val hashCache: cache.Cache[Hash[_], HashedValue] = cache.CacheBuilder.newBuilder()
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

  def getByHash[T <: HashedValue](@NotNull hash: Hash[T]): Option[T] = Option(hashCache.getIfPresent(hash)).asInstanceOf[Option[T]]

  private[hashedcomputation] def register[A <: HashedValue, B <: HashedValue]
  (@NotNull value: B, @NotNull computationHash: Hash[_], @NotNull fingerprint: Fingerprint[A]): Unit = {
    logger.debug(s"Registering $value in cache")
    val valueHash = value.hash
    hashCache.put(valueHash, value)
    outputCache.put((computationHash, fingerprint.hash), valueHash)

    logger.debug(s"Registering ${(computationHash, fingerprint, value.hash)} in fingerprints")

    def put[C <: HashedValue](id: Long, hash: Hash[_], element: Element[C, _ <: HashedValue]): Long = {
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

/*    def storeEntries[C <: HashedValue](id: Long, currentHash: Hash,
                                       @Nullable outerElement: Element[A, C],
                                       entries: Seq[Fingerprint.Entry[C, _ <: HashedValue]]): (Long, Hash) = {
      def storeEntry[D <: HashedValue](id: Long, hash: Hash, entry: Entry[C, D]): (Long, Hash) = {
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

  def getHashByInputHash[A <: HashedValue, B <: HashedValue](@NotNull computationHash: Hash[HashedFunction[A,B]], @NotNull inputHash: Hash[A]): Option[Hash[B]] =
    Option(outputCache.getIfPresent((computationHash, inputHash))).asInstanceOf[Option[Hash[B]]]

  def getHashByInput[A <: HashedValue, B <: HashedValue](@NotNull computationHash: Hash[HashedFunction[A,B]],
                                                         @NotNull input: A): Option[Hash[B]] = {
    logger.debug(s"Searching for $computationHash($input) in fingerprints")

    var hash : Hash[_] = computationHash
    var id = 0L
    while (true) {
      fingerprintCache.getIfPresent((id,hash)) match {
        case null => return None
        case Right(hash) => return Some(hash.asInstanceOf[Hash[B]])
        case Left((id2, element)) =>
          val element2 = element.asInstanceOf[Element[A,_<:HashedValue]]
          id = id2
          hash = element2.extract(input).hash
      }
    }
    throw new AssertionError("Unreachable code")
  }

/*
  def getByInput[A <: HashedValue](@NotNull computationHash: Hash, @NotNull input: A): Option[HashedValue] =
    for (hash <- getHashByInput(computationHash, input);
         value <- getByHash(hash))
      yield value
*/
}


trait Fingerprintable[A <: HashedValue] {
  def fingerprinter: Fingerprinter[A]
}

trait Fingerprinter[A <: HashedValue] {
  /** Returns the fingerprint of all actions since creation (implies [[dispose]]) */
  def fingerprint(): Fingerprint[A]
  /** Stops tracking accesses */
  def dispose(): Unit
}

trait HashedOption[+A <: HashedValue] extends HashedValue
object HashedOption {
  def hash[A <: HashedValue](value: Option[A]): Hash[HashedOption[A]] = value match {
    case None => HashedNone.hash
    case Some(value2) => hash(value2)
  }
  def hash[A <: HashedValue](value: A): Hash[HashedSome[A]] = Hash.hashString("OPTION " + value.hash.toString) // TODO adhoc
  def apply[A <: HashedValue](value: Option[A]): HashedOption[A] = value match {
    case None => HashedNone
    case Some(x) => HashedSome(x)
  }
}
case object HashedNone extends HashedOption[Nothing] {
  override def hash: Hash[this.type] = Hash.hashString(getClass.descriptorString())
}
case class HashedSome[A <: HashedValue](value: A) extends HashedOption[A] {
  override def hash: Hash[this.type] = HashedOption.hash[A](value).asInstanceOf[Hash[this.type]]
}


// TODO: Should not implement HashedValue, hashing a large map might be slow
final class FingerprintMap[A <: HashedValue, B <: HashedValue](private val map: Map[A,B]) extends Map[A,B] with Fingerprintable[FingerprintMap[A,B]] with HashedValue {
  private type M = Map[A,B]
  private type FM = FingerprintMap[A,B]
  private type E = MapElement[A,B]
  private class MapFingerprinter extends Fingerprinter[FM] {
    private[FingerprintMap] val accesses = new mutable.LinkedHashSet[A]
    override def fingerprint(): Fingerprint[FM] = {
      val entries = for (access <- accesses.toList) yield {
        val value = map.get(access)
        Entry[FM,HashedOption[B]](MapElement(access) : E, Fingerprint[HashedOption[B]](HashedOption.hash(value)))
      }
      val fingerprint = new Fingerprint[FingerprintMap[A,B]](null, Some(entries))
      dispose()
      fingerprint
    }
    override def dispose(): Unit = fingerprinters -= this
  }
  private val fingerprinters = new mutable.ArrayDeque[MapFingerprinter]
  override def fingerprinter: Fingerprinter[FM] = {
    val fingerprinter = new MapFingerprinter
    fingerprinters += fingerprinter
    fingerprinter
  }

  override def hash: Hash[this.type] = Hash.hashString(toString()) // TODO: ad-hoc
  override def removed(key: A): Map[A, B] = ???
  override def updated[V1 >: B](key: A, value: V1): Map[A, V1] = ???
  override def get(key: A): Option[B] = {
    val result = map.get(key)
    for (fp <- fingerprinters) fp.accesses += key
    result
  }
  override def iterator: Iterator[(A, B)] = ???

  override def toString(): String = "Fingerprint"+map
}

object FingerprintMap {
  case class MapElement[A <: HashedValue, B <: HashedValue](key: A) extends Element[FingerprintMap[A,B], HashedOption[B]] {
    override def hash: Hash[this.type] = ???

    override def extract(value: FingerprintMap[A, B]): HashedOption[B] =
      HashedOption(value.map.get(key))
  }
}

class Directory private (val path: Path, parent: Directory, parentKey: Path) extends DirectoryListener {
//  def snapshot : DirectorySnapshot = new DirectorySnapshot(this)
  Directory.watchDirectory(path, this)
  private val subdirs = new TrieMap[Path, Directory]
  private var currentSnapshot = makeSnapshot

  private def makeSnapshot : DirectorySnapshot = ???

  def dispose(): Unit = Directory.unwatchDirectory(this)

  def snapshot: DirectorySnapshot = currentSnapshot

  override def onCreate(path: Path): Unit = {
    assert(path.getNameCount==1)
    for (subdir <- subdirs.remove(path)) subdir.dispose()
    val fullPath = this.path.resolve(path)
    if (Files.isDirectory(fullPath, NOFOLLOW_LINKS)) {
      val dir = new Directory(fullPath, this, path)
      currentSnapshot = currentSnapshot.updated(path.toString, dir.snapshot)
    } else if (Files.isRegularFile(fullPath, NOFOLLOW_LINKS)) {
      ???
    } else
      ???

    if (parent!=null)
      parent.onModify(parentKey)
  }
  override def onModify(path: Path): Unit = onCreate(path)
  override def onDelete(path: Path): Unit = {
    assert(path.getNameCount==1)
    subdirs.remove(path)
    currentSnapshot = currentSnapshot.removed(path.toString)
  }
  override def onOverflow(): Unit = currentSnapshot = makeSnapshot
}

object Directory {
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
            // TODO catch exceptions
            events.forEach { event => event.kind() match {
            case OVERFLOW => listener.onOverflow()
            case ENTRY_CREATE => listener.onCreate(event.context().asInstanceOf[Path])
            case ENTRY_MODIFY => listener.onModify(event.context().asInstanceOf[Path])
            case ENTRY_DELETE => listener.onDelete(event.context().asInstanceOf[Path])
          }}
        }
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

class DirectorySnapshot(content: Map[String, DirectoryEntry]) extends DirectoryEntry with Map[String, DirectoryEntry] with HashedValue {

/*  class DirectoryFingerprinter extends Fingerprinter[DirectorySnapshot] {
    val accesses = new mutable.ArrayDeque[String]

    override def fingerprint(): Fingerprint[DirectorySnapshot] = {
      val entries : List[Entry[DirectorySnapshot, _ <: HashedValue]] =
        for (access <- accesses.toList) yield
          Entry(DirectoryElement(access), Fingerprint(HashedOption(contents(access))))
      dispose()
      Fingerprint(hash, Some(entries))
    }
    override def dispose(): Unit = fingerprinters -= this
  }

  private val fingerprinters = new mutable.ArrayDeque[DirectoryFingerprinter]
  override def fingerprinter: Fingerprinter[DirectorySnapshot] = {
    val fingerprinter = new DirectoryFingerprinter
    fingerprinters += fingerprinter
    fingerprinter
  }*/

  override def hash: Hash[this.type] =
    Hash.hashString(content.toList.map { case (s,h) => (s,h.hash) }.toString()) // TODO: proper hash

  override def get(key: String): Option[DirectoryEntry] = content.get(key)
  override def iterator: Iterator[(String, DirectoryEntry)] = content.iterator
  override def removed(key: String): DirectorySnapshot =
    new DirectorySnapshot(content.removed(key))

  override def updated[V1 >: DirectoryEntry](key: String, value: V1): Map[String, V1] =
    content.updated(key, value)

  def updated(key: String, value: DirectoryEntry) : DirectorySnapshot =
    new DirectorySnapshot(content.updated(key, value))
}

/*
case class DirectoryElement(path: Path) extends Element[DirectorySnapshot, HashedOption[FileContent]] {
  override def extract(directorySnapshot: DirectorySnapshot): HashedOption[FileContent] =
    HashedOption(directorySnapshot.get(path))

  override def hash: Hash[DirectoryElement.this.type] = ???
}*/
