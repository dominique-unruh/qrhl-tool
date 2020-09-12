package qrhl

import java.io.FileInputStream
import java.lang.AbstractMethodError
import java.nio.file.Path
import java.security.MessageDigest

import hashedcomputation.Context.default
import qrhl.logic.{CVariable, Variable}
import scalaz.Memo

import scala.collection.immutable.ListSet
import scala.collection.{AbstractSet, GenSet, GenTraversableOnce, IterableFactory, IterableFactoryDefaults, SeqOps, SetOps, mutable}
import scala.language.implicitConversions
import scala.ref.SoftReference

object Utils {
  def symmetricDifferrence[A](a: Set[A], b: Set[A]) : Set[A] =
    (a -- b) ++ (b -- a)

//  implicit class ListSetUpcast[A](set : ListSet[A]) {
//    def upcast[B >: A]: ListSet[B] = set.asInstanceOf[ListSet[B]]
//  }

  implicit def listSetUpcast[B, A <: B](set : ListSet[A]) : ListSet[B] =
    set.asInstanceOf[ListSet[B]]

  implicit class ListSetUtils[A](set : ListSet[A]) {
    def upcast[B >: A] : ListSet[B] = listSetUpcast(set)
    /** Same as ++. Was needed earlier because ++ was reversing element order */
    def +++[B >: A](other : GenTraversableOnce[B]): ListSet[B] =
      set ++ other.toSeq
  }

  private val digest = MessageDigest.getInstance("SHA-1")
  def hashFile(file: Path): Array[Byte] = {
    val inputStream = new FileInputStream(file.toFile)
    val content = inputStream.readAllBytes()
    digest.synchronized {
      digest.reset()
      digest.digest(content)
    }
  }

  def hashFileSet(files: Iterable[Path]) : Array[Byte] = {
    val hashes = files.toSeq.sorted.map(Utils.hashFile)
    digest.synchronized {
      digest.reset()
      for (h <- hashes)
        digest.update(h)
      digest.digest()
    }
  }

  def isSorted[A](list: List[A])(implicit ord: Ordering[A]): Boolean = {
    if (list.isEmpty) return true
    var previous = list.head
    for (x <- list.tail) {
      if (ord.lt(x,previous))
        return false
      previous = x
    }
    true
  }

  def isSortedUnique[A](list: List[A])(implicit ord: Ordering[A]): Boolean = {
    if (list.isEmpty) return true
    var previous = list.head
    for (x <- list.tail) {
      if (ord.lteq(x,previous))
        return false
      previous = x
    }
    true
  }

  def areDistinct[A](values:TraversableOnce[A]): Boolean = {
    val seen = new mutable.HashSet[A]()
    for (v <- values)
      if (!seen.add(v))
        return false
    true
  }

  class MapMatch[A,B](map : Map[A,B]) {
    def unapply(name: A): Option[B] = map.get(name)
  }

  def singleMemo[K<:AnyRef,V]: Memo[K, V] = {
    var previous : SoftReference[(K,V)] = SoftReference(null)
    Memo.memo[K,V] { f => k =>
      previous match {
        case SoftReference((prevK,prevV)) if prevK eq k =>
          prevV
        case _ =>
          val v = f(k)
          previous = SoftReference((k,v))
          v
      }
    }
  }
}

/** A set that can either be finite, or the set of all elements.
 * Backed by a `ListSet`, so it shares `ListSet`'s guarantees about insertion order
 *  */
sealed trait MaybeAllSet[A] extends AbstractSet[A]
  with IterableFactoryDefaults[A, MaybeAllSet] {

  override def iterableFactory: IterableFactory[MaybeAllSet] = MaybeAllSet

  override def intersect(that: collection.Set[A]): MaybeAllSet[A] =
    throw new AbstractMethodError() : AbstractMethodError

//  def intersect(that: MaybeAllSet[A]): MaybeAllSet[A]

  def isAll: Boolean
  def isEmpty: Boolean
}

object MaybeAllSet extends IterableFactory[MaybeAllSet] {
  override def from[A](source: IterableOnce[A]): MaybeAllSet[A] = source match {
    case AllSet() => all
    case _ => NotAllSet(ListSet.from(source))
  }

  def subtract[A](set1: ListSet[A], set2: MaybeAllSet[A]) : ListSet[A] = set2 match {
    case _ : AllSet[A] => ListSet.empty
    case NotAllSet(set2) => set1 -- set2
  }

  def subtract[A](set1: Set[A], set2: MaybeAllSet[A]) : Set[A] = set2 match {
    case _ : AllSet[A] => ListSet.empty
    case NotAllSet(set2) => set1 -- set2
  }

  override def empty[A]: NotAllSet[A] = emptyInstance.asInstanceOf[NotAllSet[A]]

  val emptyInstance: NotAllSet[Any] = NotAllSet[Any](ListSet.empty)
  private val allInstance : AllSet[Nothing] = AllSet()
  def all[A] : AllSet[A] = allInstance.asInstanceOf[AllSet[A]]

  override def newBuilder[A]: mutable.Builder[A, NotAllSet[A]] = new mutable.Builder[A, NotAllSet[A]] {
    private val builder = ListSet.newBuilder[A]
    override def addOne(elem: A): this.type = {builder += elem; this}
    override def clear(): Unit = builder.clear()
    override def result(): NotAllSet[A] = NotAllSet(builder.result())
  }
}

case class AllSet[A] private () extends MaybeAllSet[A] {
  override def concat(elems: GenTraversableOnce[A]): AllSet[A] = this

  override def contains(elem: A): Boolean = true

  override def concat[B >: A](suffix: IterableOnce[B]): MaybeAllSet[B] = MaybeAllSet.all

  override def +(elem: A): AllSet[A] = this

  override def -(elem: A): Nothing =
    throw new UnsupportedOperationException("Removing an element from the set containing everything")

  override def iterator: Nothing =
    throw new UnsupportedOperationException("Iterating over the set containing everything")

  override def size: Int =
    throw new UnsupportedOperationException("Size of the set containing everything")

  /** Returns false. This is not correct in case A is an uninhabited type */
  override def isEmpty: Boolean = false

  override def isAll: Boolean = true

  override def intersect(that: collection.Set[A]): MaybeAllSet[A] = that match {
    case _ : AllSet[A] => this
    case that : NotAllSet[A] => that
    case _ => NotAllSet(ListSet(that.toSeq:_*))
  }

  override def toString(): String = "Set(everything)"

  override def diff(that: collection.Set[A]): collection.Set[A] = that match {
    case AllSet() => empty
    case _ =>
      if (that.isEmpty) this
      else throw new UnsupportedOperationException("Removing finite set from set of all elements")
  }
}

case class NotAllSet[A](set: ListSet[A]) extends MaybeAllSet[A] {
  import Utils.ListSetUtils

  override def diff(that: collection.Set[A]): collection.Set[A] = that match {
    case AllSet() => empty
    case _ =>
      if (that.isEmpty) this
      else NotAllSet(set.diff(that))
  }

  override def concat[B >: A](suffix: IterableOnce[B]): MaybeAllSet[B] = suffix match {
    case AllSet() => MaybeAllSet.all
    case NotAllSet(set2) => NotAllSet(set ++ set2)
    case _ => NotAllSet(set ++ suffix)
  }

  override def contains(elem: A): Boolean = set.contains(elem)

  override def +(elem: A): NotAllSet[A] = NotAllSet(set + elem)

  override def -(elem: A): NotAllSet[A] = NotAllSet(set - elem)

  override def iterator: Iterator[A] = set.iterator

  override def intersect(that: collection.Set[A]): NotAllSet[A] = that match {
    case _ : AllSet[A] => this
    case NotAllSet(set2) => NotAllSet(set.intersect(set2))
    case _ => NotAllSet(set.intersect(that))
  }

  override def size: Int = set.size
  override def isEmpty: Boolean = set.isEmpty

  override def isAll: Boolean = false

  override def toString(): String = s"Set(${set.mkString(", ")})"
}
