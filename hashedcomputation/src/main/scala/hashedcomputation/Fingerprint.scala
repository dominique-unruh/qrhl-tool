package hashedcomputation

import hashedcomputation.Fingerprint.Entry
import org.jetbrains.annotations.NotNull

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object Fingerprint {
  case class Entry[A, B](element: Element[A, B], fingerprint: Fingerprint[B]) {
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

case class Fingerprint[A: Hashable](hash: Hash[A], fingerprints: Option[Seq[Entry[A, _]]]) {
  /** Must be fingerprints for the same value */
  def join(other: Fingerprint[A]): Fingerprint[A] = {
    type SE = Seq[Entry[A, _]]
    assert(hash==other.hash)
    val fp : Option[SE] = (fingerprints, other.fingerprints) match {
      case (None,None) => None
      case (f : Some[SE], None) => f
      case (None, f: Some[SE]) => f
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

object DummyMap extends mutable.Map[Nothing, Nothing] {
  override def get(key: Nothing): Option[Nothing] =
    throw new UnsupportedOperationException
  override def subtractOne(elem: Nothing): DummyMap.this.type = this
  override def addOne(elem: (Nothing, Nothing)): DummyMap.this.type = this
  override def iterator: Iterator[(Nothing, Nothing)] = new Iterator[(Nothing, Nothing)] {
    override def hasNext: Boolean = throw new UnsupportedOperationException
    override def next(): Nothing = throw new UnsupportedOperationException
  }
  override def updateWith(key: Nothing)(remappingFunction: Option[Nothing] => Option[Nothing]): Option[Nothing] =
    throw new UnsupportedOperationException
}

trait FingerprintBuilder[A] {
  def access[B : Hashable](element: Element[A,B], value: B): Unit
  def access[B: Hashable](element: Element[A,B], hash: Hash[B]) : Unit
  def access[B](element: Element[A,B], fingerprint: Fingerprint[B]): Unit
  def accessAll(): Unit
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

  def access[B : Hashable](element: Element[A,B], value: B): Unit =
    access(element, Hashable.hash(value))

  def access[B: Hashable](element: Element[A,B], hash: Hash[B]) : Unit =
    access(element, Fingerprint(hash))

  def access[B](element: Element[A,B], fingerprint: Fingerprint[B]): Unit =
    entries.updateWith(element) {
      case None => Some(fingerprint)
      case Some(fingerprint1) =>
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
