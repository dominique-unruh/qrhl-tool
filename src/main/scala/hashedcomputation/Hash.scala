package hashedcomputation

import java.nio.ByteBuffer
import java.security.MessageDigest
import java.util
import java.util.concurrent.TimeUnit.HOURS
import java.util.concurrent.atomic.AtomicReference

import com.google.common.cache
import hashedcomputation.Fingerprint.Entry
import hashedcomputation.HashedPromise.State
import org.apache.commons.codec.binary.Hex
import org.jetbrains.annotations.{NotNull, Nullable}
import org.log4s

import scala.annotation.tailrec
import scala.collection.mutable
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.util.Random

class Hash private (private val hash: Array[Byte]) {
  override def toString: String = Hex.encodeHexString(hash).substring(0,7)

  override def hashCode(): Int = util.Arrays.hashCode(hash)
  override def equals(obj: Any): Boolean = obj match {
    case obj : Hash =>
      util.Arrays.equals(hash, obj.hash)
    case _ => false
  }
}

object Hash {

  private val digest = MessageDigest.getInstance("SHA-256")
  private val hashLen = digest.getDigestLength

  def hashBytes(bytes: Array[Byte]): Hash = digest.synchronized {
    digest.reset()
    digest.update(bytes)
    new Hash(digest.digest())
  }

  def hashInt(int: Int): Hash = hashBytes(ByteBuffer.allocate(hashLen).put(0:Byte).putInt(int).array())
  def hashString(str: String): Hash = hashBytes(str.getBytes)
  def randomHash(): Hash = new Hash(Random.nextBytes(hashLen))
}

trait Element[A <: HashedValue, B <: HashedValue] extends HashedValue {
  def extract(value: A): B
}

object Fingerprint {
  case class Entry[A <: HashedValue, B <: HashedValue](element: Element[A,B], fingerprint: Fingerprint[B]) {
    def matches(value: A): Boolean = {
      val extracted = element.extract(value)
      fingerprint.matches(extracted)
    }
  }

  def apply[A <: HashedValue](hash: Hash) = new Fingerprint[A](hash, None)
  def apply[A <: HashedValue](value: A) = new Fingerprint[A](value.hash, None)
}

case class Fingerprint[A <: HashedValue](hash: Hash, fingerprints: Option[Seq[Entry[A,_]]]) {
  def matches(value: A): Boolean =
    if (hash == value.hash) true
    else {
      fingerprints match {
        case None => false
        case Some(fingerprints) =>
          fingerprints.forall(_.matches(value))
      }
    }
}

trait HashedValue {
  /** Must return a stable value */
  @NotNull def hash: Hash
}

trait HashedFunction[A <: HashedValue, B <: HashedValue] {
  @NotNull def compute(input: A): Future[(B @NotNull, Fingerprint[A] @NotNull)]
  @NotNull def hash: Hash
}
object HashedFunction {
  def apply[A <: HashedValue, B <: HashedValue](f: A => B): HashedFunction[A, B] = new HashedFunction[A,B] {
    override def compute(input: A): Future[(B, Fingerprint[A])] = Future {
      val result = f(input)
      (result, Fingerprint(input.hash))
    }

    override val hash: Hash = Hash.randomHash()
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

  def apply[A <: HashedValue, B <: HashedValue](function: HashedFunction[A, B], input: HashedPromise[_ <: HashedValue, A], hash: Hash): HashedPromise[A, B] =
    apply(State.FunctionAndHash(function, input, hash))

  def apply[A <: HashedValue, B <: HashedValue](hashedFunction: HashedFunction[A, B], input: A): HashedPromise[A, B] =
    apply(hashedFunction, HashedPromise(input))

  private sealed trait State[A, B]
  private object State {
    /** A state in which a computation function is available (but was not executed yet, nor the inputs computed) */
    sealed trait StateWithFunction[A <: HashedValue, B <: HashedValue] extends State[A,B] {
      val function : HashedFunction[A,B]
      val inputFuture: Future[A]
    }
    /** A state where a future with the hash is available (hash computation started or finished) */
    sealed trait HashFutureState[A,B] extends State[A,B] {
      def hashFuture : Future[Hash]
    }
    /** A state where a future with the result is available (hash computation started or finished) */
    sealed trait ResultFutureState[A,B <: HashedValue] extends HashFutureState[A,B] {
      def resultFuture : Future[B]
      override def hashFuture: Future[Hash] = resultFuture.map(_.hash)
    }
    /** A state where all computations have been performed (but possibly failed) */
    sealed trait FinalState[A <: HashedValue, B <: HashedValue] extends HashFutureState[A,B] with ResultFutureState[A,B]
    sealed trait Computing[A <: HashedValue, B <: HashedValue] extends State[A,B]

    final case class HashAndInput[A <: HashedValue, B <: HashedValue](function: HashedFunction[A,B], input: A, hash: Hash) extends HashFutureState[A,B] {
      override def hashFuture: Future[Hash] = Future.successful(hash)
    }
    final case class Failed[A <: HashedValue, B <: HashedValue](exception: Throwable) extends FinalState[A,B] {
      override def hashFuture: Future[Hash] = Future.failed(exception)
      override def resultFuture: Future[B] = Future.failed(exception)
    }
    final case class Locked[A <: HashedValue, B <: HashedValue]() extends State[A,B]
    final case class ComputingHash[A <: HashedValue, B <: HashedValue](override val hashFuture: Future[Hash]) extends HashFutureState[A,B] with Computing[A,B]
    final case class ComputingResult[A <: HashedValue, B <: HashedValue](override val resultFuture: Future[B]) extends ResultFutureState[A,B] with Computing[A,B]
    final case class Result[A <: HashedValue, B <: HashedValue](result: B) extends FinalState[A,B] {
      override def hashFuture: Future[Hash] = Future.successful(result.hash)
      override def resultFuture: Future[B] = Future.successful(result)
    }
    final case class FunctionOnly[A <: HashedValue, B <: HashedValue](override val function: HashedFunction[A, B], input: HashedPromise[_ <: HashedValue, A]) extends StateWithFunction[A,B] {
      override val inputFuture: Future[A] = input.get
    }
    final case class FunctionAndHash[A <: HashedValue, B <: HashedValue]
          (override val function: HashedFunction[A, B], val input: HashedPromise[_ <: HashedValue, A],
           hash: Hash)
      extends StateWithFunction[A,B] with HashFutureState[A,B] {
      override def hashFuture: Future[Hash] = Future.successful(hash)
      override val inputFuture: Future[A] = input.get
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
          val future = for (inputValue <- st.inputFuture;
                            function = st.function;
                            // TODO: We should first try whether we can do the lookup with only the input-hash. Then we might not have to compute the input
                            hashOption = Cache.getHashByInput(function.hash, inputValue);
                            newState <- hashOption match {
                              case Some(hash) => Future.successful(State.HashAndInput(function, inputValue, hash))
                              case None => doCompute(function, inputValue)
                            };
                            _ = state.set(newState);
                            hash <- newState.hashFuture)
            yield hash
          state.set(State.ComputingHash[A,B](future))
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
      case st: State.HashAndInput[A, B] =>
        ???
      case st: State.StateWithFunction[A, B] =>
        if (state.compareAndSet(st, State.Locked())) {
          val future = for (inputValue <- st.inputFuture;
                            function = st.function;
                            resultOption = Cache.getByInput(function.hash, inputValue).asInstanceOf[Option[B]];
                            newState <- resultOption match {
                              case Some(result) => Future.successful(State.Result[A, B](result))
                              case None => doCompute(function, inputValue)
                            };
                            _ = state.set(newState);
                            result <- newState.resultFuture)
            yield result
          state.set(State.ComputingResult[A, B](future))
        } else
          triggerComputation()
    }
  }


  def getHash: Future[Hash] = state.get() match {
    case st: State.HashFutureState[A, B] => st.hashFuture
    case _ =>
      triggerHashComputation()
      getHash
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

  private val hashCache: cache.Cache[Hash, HashedValue] = cache.CacheBuilder.newBuilder()
    .softValues()
    .expireAfterAccess(1, HOURS)
    .build()

  def getByHash(@NotNull hash: Hash): Option[HashedValue] = Option(hashCache.getIfPresent(hash))

  // TODO: very inefficient implementation!!!
  private val fingerprints = new mutable.ArrayBuffer[(Hash, Fingerprint[_], Hash)]

  private[hashedcomputation] def register[A <: HashedValue, B <: HashedValue](@NotNull value: B, @NotNull computationHash: Hash, @NotNull fingerprint: Fingerprint[A]): Unit = {
    logger.debug(s"Registering $value in cache")
    hashCache.put(value.hash, value)
    fingerprints.synchronized {
      logger.debug(s"Registering ${(computationHash, fingerprint, value.hash)} in fingerprints")
      fingerprints += ((computationHash, fingerprint, value.hash))
    }
  }

  // TODO: Also add getHashByInputHash
  def getHashByInput[A <: HashedValue](@NotNull computationHash: Hash, @NotNull input: A): Option[Hash] = fingerprints.synchronized {
    logger.debug(s"Searching for $computationHash($input) in fingerprints")
    for ((computationHash2, fingerprint, result) <- fingerprints) {
      logger.debug(s"Checking $computationHash2, $fingerprint, $result")
      if (computationHash == computationHash2 && fingerprint.asInstanceOf[Fingerprint[A]].matches(input)) {
        logger.debug("Found")
        return Some(result)
      }
    }
    logger.debug("Not found")

    None
  }

  def getByInput[A <: HashedValue](@NotNull computationHash: Hash, @NotNull input: A): Option[HashedValue] =
    for (hash <- getHashByInput(computationHash, input);
         value <- getByHash(hash))
      yield value
}
