package hashedcomputation

import java.nio.ByteBuffer
import java.nio.charset.Charset
import java.security.MessageDigest
import java.util
import java.util.concurrent.ConcurrentHashMap

import org.apache.commons.codec.binary.Hex
import org.log4s

import scala.collection.mutable

class DefaultContext extends Context {
  import DefaultContext._

  private val digest = MessageDigest.getInstance("SHA-1")
  private val buffer = ByteBuffer.allocate(4)

  final class H private[DefaultContext] (private[DefaultContext] val bytes: Array[Byte]) {
    override def equals(obj: Any): Boolean = obj match {
      case h: H => util.Arrays.equals(bytes, h.bytes)
      case _ => false
    }
    override def hashCode(): Int =
      util.Arrays.hashCode(bytes)

    override def toString: String = Hex.encodeHexString(bytes)
  }
  override type Hash = H


  override def hash(values: Any*): Hash = digest.synchronized {
    digest.reset()
    for (v <- values) v match {
      case a: Array[Byte] => digest.update(0 : Byte); digest.update(a)
      case s: String => digest.update(1 : Byte); digest.update(s.getBytes(charset))
      case i: Int => digest.update(2: Byte); buffer.rewind(); buffer.putInt(i); digest.update(buffer.array(), 0, 4)
        // Hashed and Hash intentionally hash the same way
      case h: Hashed[_] => digest.update(3: Byte); digest.update(h.hash.bytes)
      case h: Hash => digest.update(3: Byte); digest.update(h.bytes)
      case b: Boolean => if (b) digest.update(4: Byte); else digest.update(5: Byte)
      case _ => throw new IllegalArgumentException(s"Trying to hash value of type ${v.getClass}")
    }
    new H(digest.digest())
  }

  // TODO: should be a soft reference map or something like that
  type HashTable[T] = ConcurrentHashMap[Hash,Computation[T]]

//  private def createHashTable[T]: HashTable[T] = new mutable.HashMap[Hash,T]()

  class Function[T,U] private[DefaultContext] (function: Hashed[T]=>U) extends FunctionTrait[T,U] {
    private val hashTable: HashTable[U] = new ConcurrentHashMap[Hash,Computation[U]]()

    def apply(argument: Hashed[T]): Computation[U] = {
      val hashStr = argument.hash.toString
//      logger.debug(s"Checking: $hashStr")
      hashTable.computeIfAbsent(argument.hash,
        { _ =>
          new Computation[U]({
//            logger.debug(s"Computing: $hashStr")
            function(argument)
          })})
    }
  }

  def createFunction[T,U](function: Hashed[T]=>U) : Function[T,U] =
    new Function[T,U](function)
}

object DefaultContext {
  private val charset = Charset.forName("UTF-16")
  private val logger = log4s.getLogger
}