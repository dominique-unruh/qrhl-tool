package hashedcomputation

import hashedcomputation.Fingerprint.Entry
import org.jetbrains.annotations.{NotNull, Nullable}

import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.util.control.Breaks
import scala.util.control.Breaks.{break, tryBreakable}

object Fingerprint {
  /** An entry inside a fingerprint. It consists of an [[Element]] that was accessed, and a [[Fingerprint]] of the value of the element. */
  final case class Entry[A, B](element: Element[A, B], fingerprint: Fingerprint[B]) {
    type OutT = B
    type InT = A

    def matches(value: A): Boolean = {
      val extracted = element.extract(value)
      fingerprint.matches(extracted)
    }
  }

  object Entry {
    def apply[A, B: Hashable](element: Element[A, B], value: A): Entry[A, B] =
      Entry(element, Fingerprint(Hashable.hash(element.extract(value))))
  }

  def apply[A: Hashable](hash: Hash[A]) = new Fingerprint[A](hash, None)

  def apply[A: Hashable](value: A) = new Fingerprint[A](Hashable.hash(value), None)
}

/** fingerprints==None means no fingerprinting, can only rely on the overall hash */
case class Fingerprint[A: Hashable](@NotNull hash: Hash[A], @NotNull fingerprints: Option[Seq[Entry[A, _]]]) {
  /** Transform this fingerprint of some value `a` into a fingerprint of a subvalue `b` of `a`.
   * @param targetHash The hash of the subvalue
   * @param projectEntry function that maps an [[Entry]] `e` relative to `a` into a sequence of entries `e'` relative to `b`.
   *                     The meaning: Access `e` on `a` implicitly made the accesses `e'` on `b`.
   *                     (If in doubt, return *more* accesses, not less.)
   *                     Returning `None` means: The whole of `b` has been accessed.
   * @tparam B the type of the subvalue `b` */
  def project[B: Hashable](targetHash: Hash[B], projectEntry: Entry[A,_] => Option[Seq[Entry[B, _]]]): Fingerprint[B] =
    fingerprints match {
      case None => new Fingerprint[B](targetHash, None)
      case Some(fingerprints) =>
        tryBreakable {
          val merged = for (entry <- fingerprints;
                            projFp = projectEntry(entry).getOrElse { break() };
                            fp2 <- projFp)
            yield fp2
          new Fingerprint[B](targetHash, Some(merged))
        } catchBreak {
          new Fingerprint[B](targetHash, None)
        }
    }

  /** Must be fingerprints for the same value */
  def join(other: Fingerprint[A]): Fingerprint[A] = {
    type SE = Seq[Entry[A, _]]
    assert(hash == other.hash)
    val fp : Option[SE] = (fingerprints, other.fingerprints) match {
      case (None, None) => None
      case (f : Some[SE], None) => None
      case (None, f: Some[SE]) => None
      case (Some(f1), Some(f2)) => Some(f1 ++ f2)
    }
    new Fingerprint(hash, fp)
  }

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

  type U[B] = (Element[A, B], Hash[B])

  def unfold: Seq[U[_]] = {
    val result = new ListBuffer[U[_]]

    def unfold[B](fp: Fingerprint[B], element: Element[A, B]): Unit = fp.fingerprints match {
      case None => result.append((element, fp.hash): U[B])
      case Some(fingerprints) =>
        def doEntry[C](entry: Entry[B, C]): Unit = {
          val subElement = NestedElement(element, entry.element)
          unfold(entry.fingerprint, subElement)
        }

        for (entry <- fingerprints) doEntry(entry)
    }

    unfold(this, IDElement())
    result.toList
  }
}

object DummyMap extends mutable.Map[Any, Any] {
  override def get(key: Any): Option[Nothing] =
    throw new UnsupportedOperationException
  override def subtractOne(elem: Any): DummyMap.this.type = this
  override def addOne(elem: (Any, Any)): DummyMap.this.type = this
  override def iterator: Iterator[(Any, Any)] = new Iterator[(Any, Any)] {
    override def hasNext: Boolean = throw new UnsupportedOperationException
    override def next(): Nothing = throw new UnsupportedOperationException
  }
  override def updateWith(key: Any)(remappingFunction: Option[Any] => Option[Any]): Option[Any] =
    throw new UnsupportedOperationException
}

/** A class that tracks accesses to [[Element]]s of value and creates a fingerprint in the end that logs the hashes of those elements.
 * @tparam The type of the value. */
trait FingerprintBuilder[A] {
  def access[B](element: Element[A,B], fingerprint: Fingerprint[B]): Unit
  /** Mark the whole value as accessed. */
  def accessAll(): Unit

  def access[B : Hashable](element: Element[A,B], value: B): Unit =
    access(element, Hashable.hash(value))
  def access[B: Hashable](element: Element[A,B], hash: Hash[B]) : Unit =
    access(element, Fingerprint(hash))
  def access(fingerprint: Fingerprint[A]): Unit = fingerprint.fingerprints match {
    case None => accessAll()
    case Some(entries) =>
      for (entry <- entries)
        entry match {
          case entry : Entry[A,b] =>
            access(entry.element, entry.fingerprint)
        }
  }
  // TODO: rename to something like buildFingerprint
  def fingerprint : Fingerprint[A]
  def unsafeUnderlyingValue : A
}

/** Not thread safe */
final class FingerprintBuilderImpl[A : Hashable](value: A) extends FingerprintBuilder[A] {
  private type MapType = mutable.Map[Element[A, _], Fingerprint[_]]
  private var entries : MapType =
    new mutable.LinkedHashMap[Element[A, _], Fingerprint[_]]

  override def unsafeUnderlyingValue: A = value

  def access[B](element: Element[A,B], fingerprint: Fingerprint[B]): Unit =
    if (entries eq DummyMap)
      {}
    else
      entries.updateWith(element) {
        case None => Some(fingerprint)
        case Some(fingerprint1) =>
          assert(fingerprint.hash == fingerprint1.hash)
          Some(fingerprint1.asInstanceOf[Fingerprint[B]].join(fingerprint))
      }

  def accessAll(): Unit = entries = DummyMap.asInstanceOf[MapType]

  def fingerprint : Fingerprint[A] = {
    if (entries eq DummyMap)
      Fingerprint(Hashable.hash(value), None)
    else
      Fingerprint(Hashable.hash(value),
        Some(entries.toSeq.map { case (elem, fp) =>
          new Entry(elem, fp.asInstanceOf[Fingerprint[Any]]) }))
  }
}

/*
trait FingerprintingView[A, B] { this: B =>
  /** This function returns the underlying value without registering the access in the fingerprint */
  def unsafePeekUnderlyingValue: A

  /** Will cause the whole object to be marked as accessed */
  def everything : A
}

trait HasFingerprintingView[A, B] extends Hashable[A] {
  @NotNull def newView(@NotNull value: A, @NotNull fingerprintBuilder: FingerprintBuilder[A]) : FingerprintingView[A,B]
}

trait WithFingerprintingView[B] extends HashedValue {
  @NotNull def newView(@NotNull fingerprintBuilder: FingerprintBuilder[this.type]) : FingerprintingView[this.type,B]
}

object WithFingerprintingView {
  implicit def withFingerprintingViewHasFingerprintingView[B]: HasFingerprintingView[WithFingerprintingView[B], B] =
    new HasFingerprintingView[WithFingerprintingView[B], B] {
      override def hash[A1 <: HashedValue](value: A1): Hash[A1] = value.hash
      override def newView(value: WithFingerprintingView[B], fingerprintBuilder: FingerprintBuilder[WithFingerprintingView[B]]): FingerprintingView[WithFingerprintingView[B], B] =
        value.newView(fingerprintBuilder)
    }
}
*/
