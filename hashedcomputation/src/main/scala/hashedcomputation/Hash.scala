package hashedcomputation

import java.nio.ByteBuffer
import java.nio.file.Path
import java.security.MessageDigest
import java.util
import org.apache.commons.codec.binary.Hex
import org.jetbrains.annotations.NotNull
import sourcecode.File

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.language.experimental.macros
import scala.util.Random
import scala.language.implicitConversions

class RawHash private (private val hash: Array[Byte]) extends WithByteArray {
  def literalExpressionForMacros(c: scala.reflect.macros.blackbox.Context): c.Expr[RawHash] = {
    import c.universe._
    //noinspection MakeArrayToString
    c.Expr(q"hashedcomputation.RawHash.createFromByteArray($hash)")
  }

  def hex: String = Hex.encodeHexString(hash)
  override def toString: String = "RAW#" + hex.substring(0,7)
  override def hashCode(): Int = util.Arrays.hashCode(hash)
  override def equals(obj: Any): Boolean = obj match {
    case obj : RawHash =>
      util.Arrays.equals(hash, obj.hash)
    case _ => false
  }

  override private[hashedcomputation] def byteArray = hash
}

object RawHash {
  def apply(hashTag: HashTag[_], hashes: WithByteArray*): RawHash = digest.synchronized {
    digest.reset()
    digest.update(hashTag.rawHash.hash)
    for (h <- hashes)
      digest.update(h.byteArray)
    new RawHash(digest.digest())
  }

  /** Should be considered private. */
  def createFromByteArray(bytes: Array[Byte]) = new RawHash(bytes)

  // TODO: using synchronize to access this is probably slow. Use something else
  private val digest = MessageDigest.getInstance("SHA-256")
  private val hashLen = digest.getDigestLength

  def hashBytes(bytes: Array[Byte]): RawHash = digest.synchronized {
    digest.reset()
    digest.update(bytes)
    new RawHash(digest.digest())
  }

  def hashInt(int: Int): RawHash =
    hashBytes(ByteBuffer.allocate(4).putInt(int).array())
  def hashString(str: String): RawHash = hashBytes(str.getBytes)
  def randomHash(): RawHash = new RawHash(Random.nextBytes(hashLen))
}

class HashTag[+B] private (val rawHash: RawHash) extends AnyVal {
  def apply(hashes: WithByteArray*): Hash[B] =
    Hash(this, hashes:_*)
}

object HashTag {
  /** Use this inside hashedcomputation because HashTag.apply is not available here
   * (because the latter is a macro) */
  private[hashedcomputation] def create[T]()(implicit file: sourcecode.File, line: sourcecode.Line) = {
    val string = s"HashTag ${file.value}:${line.value}"
    new HashTag[T](RawHash.hashString(string))
  }

  def randomHashTag[B]() = new HashTag[B](RawHash.randomHash())
  def macroImplementationApply[B](c: scala.reflect.macros.blackbox.Context)(): c.Expr[HashTag[B]] = {
    import c.universe._
    val pos = c.enclosingPosition
    val string = s"HashTag ${pos.source.path}:${pos.line}:${pos.column}"
    val rawHash = RawHash.hashString(string)
    val rawLiteral = rawHash.literalExpressionForMacros(c)
    val literal = c.Expr(q"hashedcomputation.HashTag.createFromRawHash($rawLiteral)")
//    c.info(pos, s"Position = ${string}, hash literal = $literal", force = true)
    literal
  }
  def apply[B](): HashTag[B] = macro macroImplementationApply[B]

  def createFromRawHash[B](rawHash: RawHash) = new HashTag[B](rawHash)
}

class Hash[+B] private (val rawHash: RawHash) extends AnyVal with WithByteArray {
  override def toString: String = hex.substring(0,7)
  def hex: String = rawHash.hex

  override private[hashedcomputation] def byteArray = rawHash.byteArray
}

trait WithByteArray extends Any {
  private[hashedcomputation] def byteArray : Array[Byte]
}

object Hash {
  @inline def apply[T](hashTag: HashTag[T], hashes: WithByteArray*): Hash[T] =
    new Hash(RawHash(hashTag, hashes: _*))

  def randomHash[T]() = new Hash[T](RawHash.randomHash())

  /** Prefer to use functions using [[HashTag]]s. */
  def createHashFromRawHash[A](rawHash: RawHash) = new Hash[A](rawHash)
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

    override val hash: Hash[this.type] = Hash.randomHash[this.type]()
  }
//  private val hashTag = HashTag[HashedFunction[_,_]]()
}


// TODO: remove this class
trait HashedOption[+A] extends HashedValue
object HashedOption {
  def hash[A : Hashable](value: Option[A]): Hash[HashedOption[A]] = value match {
    case None => HashedNone.hash
    case Some(value2) => hash(value2)
  }
  private val hashTag1 : HashTag[HashedSome[Nothing]] = HashTag.randomHashTag()
  def hash[A : Hashable](value: A): Hash[HashedSome[A]] =
    Hash(hashTag1, Hashable.hash(value))
  def apply[A : Hashable](value: Option[A]): HashedOption[A] = value match {
    case None => HashedNone
    case Some(x) => HashedSome(x)
  }

}

case object HashedNone extends HashedOption[Nothing] {
  override val hash: Hash[this.type] = Hash.randomHash()
}
case class HashedSome[+A : Hashable](value: A) extends HashedOption[A] {
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
    Tuple2Hashable.hashTag(Hashable.hash(value._1), Hashable.hash(value._2))
      .asInstanceOf[Hash[A1]]
}
object Tuple2Hashable {
  private val hashTag = HashTag.create[(Nothing,Nothing)]()
}

class Tuple3Hashable[A : Hashable, B : Hashable, C : Hashable] extends Hashable[(A,B,C)] {
  override def hash[A1 <: (A, B, C)](value: A1): Hash[A1] =
    Tuple3Hashable.hashTag(Hashable.hash(value._1), Hashable.hash(value._2), Hashable.hash(value._3))
      .asInstanceOf[Hash[A1]]
}
object Tuple3Hashable {
  private val hashTag = HashTag.create[(Nothing,Nothing,Nothing)]()
}

class OptionHashable[A](val aHashable: Hashable[A]) extends AnyVal with Hashable[Option[A]] {
  override def hash[A1 <: Option[A]](value: A1): Hash[A1] = HashedOption.hash(value)(aHashable).asInstanceOf[Hash[A1]]
}

class ListHashable[A](val aHashable: Hashable[A]) extends AnyVal with Hashable[List[A]] {
  override def hash[A1 <: List[A]](value: A1): Hash[A1] =
    ListHashable.hashTag(value.map(Hashable.hash(_)(aHashable)) :_*)
}
object ListHashable {
  private val hashTag = HashTag.create()
}

object PathHashable extends Hashable[Path] {
  private val hashTag = HashTag.create()
  override def hash[A1 <: Path](value: A1): Hash[A1] =
  // TODO: There is an unnecessary level of hashing here
    hashTag(RawHash.hashString(value.toString))
}

object IntHashable extends Hashable[Int] {
  private val hashTag = HashTag.create()
  override def hash[A1 <: Int](value: A1): Hash[A1] = {
    // TODO: There is an unnecessary level of hashing here
    hashTag(RawHash.hashInt(value))
  }
}

object BooleanHashable extends Hashable[Boolean] {
  private val trueHash = Hash.randomHash()
  private val falseHash = Hash.randomHash()
  override def hash[A1 <: Boolean](value: A1): Hash[A1] =
    if (value) trueHash else falseHash
}

object StringHashable extends Hashable[String] {
  private val hashTag = HashTag.create()
  override def hash[A1 <: String](value: A1): Hash[A1] =
  // TODO: There is an unnecessary level of hashing here
    hashTag(RawHash.hashString(value))
}
