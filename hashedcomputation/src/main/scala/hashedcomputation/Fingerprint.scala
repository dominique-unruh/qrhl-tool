package hashedcomputation

import hashedcomputation.Fingerprint.Entry

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


trait Fingerprinter[A] {
  /** Returns the fingerprint of all actions since creation (implies [[dispose]]) */
  def fingerprint(): Fingerprint[A]
  /** Stops tracking accesses */
  def dispose(): Unit
}
