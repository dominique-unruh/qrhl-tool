package hashedcomputation

import java.nio.ByteBuffer
import java.nio.file.Path
import java.security.MessageDigest
import java.util
import org.apache.commons.codec.binary.Hex
import org.jetbrains.annotations.NotNull

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.util.Random

import scala.language.implicitConversions

class Hash[+B] private (private val hash: Array[Byte]) {
  override def toString: String = hex.substring(0,7)
  def hex: String = Hex.encodeHexString(hash)

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

trait Element[-A, +B] extends HashedValue {
  def extract(value: A): B
  def extractHash(value: A) : Hash[B]
}

abstract class AbstractElement[A,B : Hashable] extends Element[A,B] {
  def extractHash(value: A): Hash[B] = Hashable.hash(extract(value))
  override def hash: Hash[this.type] = ???
}

final case class Tuple3Element1[A:Hashable,B,C]() extends AbstractElement[(A,B,C), A] {
  override def extract(value: (A, B, C)): A = value._1
}
final case class Tuple3Element2[A,B:Hashable,C]() extends AbstractElement[(A,B,C), B] {
  override def extract(value: (A, B, C)): B = value._2
}
final case class Tuple3Element3[A,B,C:Hashable]() extends AbstractElement[(A,B,C), C] {
  override def extract(value: (A, B, C)): C = value._3
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





/** Type class for values with hashes */
trait Hashable[-A] extends Any {
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


// TODO: remove this class
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



object Implicits {
  implicit def optionHashable[A: Hashable]: OptionHashable[A] = new OptionHashable(implicitly)
  implicit def listHashable[A: Hashable]: ListHashable[A] = new ListHashable(implicitly)
  implicit def tuple2Hashable[A : Hashable, B : Hashable]: Tuple2Hashable[A,B] = new Tuple2Hashable
  implicit def tuple3Hashable[A : Hashable, B : Hashable, C : Hashable]: Tuple3Hashable[A,B,C] = new Tuple3Hashable
  implicit val pathHashable: PathHashable.type = PathHashable
  implicit val stringHashable: StringHashable.type = StringHashable
  implicit val intHashable: IntHashable.type = IntHashable
  implicit val booleanHashable: BooleanHashable.type = BooleanHashable
}

class Tuple2Hashable[A : Hashable, B : Hashable] extends Hashable[(A,B)] {
  override def hash[A1 <: (A, B)](value: A1): Hash[A1] =
    Hash.hashString(s"PAIR: ${Hashable.hash(value._1)} ${Hashable.hash(value._2)}")
}

class Tuple3Hashable[A : Hashable, B : Hashable, C : Hashable] extends Hashable[(A,B,C)] {
  override def hash[A1 <: (A, B, C)](value: A1): Hash[A1] =
    Hash.hashString(s"Tuple3: ${Hashable.hash(value._1)} ${Hashable.hash(value._2)} ${Hashable.hash(value._3)}")
}

class OptionHashable[A](val aHashable: Hashable[A]) extends AnyVal with Hashable[Option[A]] {
  override def hash[A1 <: Option[A]](value: A1): Hash[A1] = HashedOption.hash(value)(aHashable).asInstanceOf[Hash[A1]]
}

class ListHashable[A](val aHashable: Hashable[A]) extends AnyVal with Hashable[List[A]] {
  override def hash[A1 <: List[A]](value: A1): Hash[A1] =
    Hash.hashString(value.map(Hashable.hash(_)(aHashable).hex).mkString(",")) // TODO: something better
}

object PathHashable extends Hashable[Path] {
  override def hash[A1 <: Path](value: A1): Hash[A1] =
    Hash.hashString("PATH " + value.toString) // TODO: something better, with tag
}

object IntHashable extends Hashable[Int] {
  override def hash[A1 <: Int](value: A1): Hash[A1] =
    Hash.hashString("INT " + value.toString) // TODO: something better, with tag
}

object BooleanHashable extends Hashable[Boolean] {
  private val trueHash = Hash.randomHash()
  private val falseHash = Hash.randomHash()
  override def hash[A1 <: Boolean](value: A1): Hash[A1] =
    if (value) trueHash else falseHash
}

object StringHashable extends Hashable[String] {
  override def hash[A1 <: String](value: A1): Hash[A1] =
    Hash.hashString("String: " + value) // TODO: something better, with tag
}
