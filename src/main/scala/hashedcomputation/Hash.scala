package hashedcomputation

import java.nio.ByteBuffer
import java.security.MessageDigest
import java.util
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeUnit.HOURS

import com.google.common.cache
import com.google.common.util.concurrent.Callables
import hashedcomputation.Fingerprint.Entry
import org.apache.commons.codec.binary.Hex
import org.jetbrains.annotations.{NotNull, Nullable}
import org.log4s

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

class HashedPromise[A <: HashedValue, B <: HashedValue] {
  /*
   * At least one of the following must be defined (non-null):
   * - hashedFunction & computationInput
   * - value
   */
  /** Only switches from null to non-null. Never changes once non-null */
  @Nullable private var hash: Hash = _
  /** Only switches from non-null to null, never changes otherwise */
  @Nullable private var hashedFunction: HashedFunction[A,B] = _
  /** Only switches from non-null to null, never changes otherwise */
  @Nullable private var computationInput: HashedPromise[_,A] = _
//  /** Only switches from non-null to null, never changes otherwise */
//  @Nullable private var computationHash: Hash = _
  /** Only switches from null to non-null. Never changes once non-null */
  @Nullable private var value: B = _

  // TODO: Make sure the computation is never executed twice!
  def getHash: Future[Hash] =
    if (hash!=null) Future.successful(hash)
    else if (value!=null) Future.successful(value.hash)
    else
      for (input <- computationInput.get;
           hash <- getHashUsingInput(input))
        yield hash


  // TODO: Make sure the computation is never executed twice!
  def get: Future[B] = synchronized {
    if (value != null) return Future.successful(value)
    if (hash != null) Cache.getByHash(hash) match {
      case Some(hv) => return Future.successful(hv.asInstanceOf[B])
      case None =>
    }

    for (input <- computationInput.get;
         result <- getUsingInput(input))
      yield result
  }

  private def getHashUsingInput(input: A): Future[Hash] = synchronized {
    if (hashedFunction == null) return Future.successful(hash)

    Cache.getHashByInput(hashedFunction.hash, input) match {
      case Some(hash) => return Future.successful(hash)
      case None =>
    }

    for (value <- compute(input))
      yield { hash = value.hash; hash }
  }

  private def compute(input: A): Future[B] =
    for ((result, fingerprint) <- hashedFunction.compute(input);
         _ = registerResult(result, input, fingerprint))
      yield result

  private def getUsingInput(input: A): Future[B] = synchronized {
    if (hashedFunction == null) return Future.successful(value)

    Cache.getByInput(hashedFunction.hash, input) match {
      case None =>
      case Some(result) => return Future.successful(result.asInstanceOf[B])
    }

    compute(input)
  }

  private def registerResult(result: B, input: A, fingerprint: Fingerprint[A]): Unit = synchronized {
    val hashedFunctionHash = hashedFunction.hash
    computationInput = null
    hashedFunction = null
    value = result
    Cache.register(result, hashedFunctionHash, fingerprint)
  }
}

object HashedPromise {
  def apply[A <: HashedValue](hashedValue: A): HashedPromise[HashedValue, A] = {
    val promise = new HashedPromise[HashedValue, A]
    promise.value = hashedValue
    promise
  }

  def apply[A <: HashedValue, B <: HashedValue](hashedFunction: HashedFunction[A, B], input: HashedPromise[_, A]): HashedPromise[A, B] = {
    val promise = new HashedPromise[A, B]
    promise.hashedFunction = hashedFunction
    promise.computationInput = input
    promise
  }

  def apply[A <: HashedValue, B <: HashedValue](hashedFunction: HashedFunction[A, B], input: A): HashedPromise[A, B] =
    apply(hashedFunction, HashedPromise(input))
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
