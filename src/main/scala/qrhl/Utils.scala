package qrhl

import java.io.FileInputStream
import java.nio.file.Path
import java.security.MessageDigest

import hashedcomputation.Context.default
import qrhl.logic.CVariable
import scalaz.Memo

import scala.collection.immutable.ListSet
import scala.collection.mutable
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
    /** Like ListSet.++, but makes sure that the appended collection is not inserted in reverse order */
    def +++[B >: A](other : TraversableOnce[B]): ListSet[B] =
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
    return true
  }

  def isSortedUnique[A](list: List[A])(implicit ord: Ordering[A]): Boolean = {
    if (list.isEmpty) return true
    var previous = list.head
    for (x <- list.tail) {
      if (ord.lteq(x,previous))
        return false
      previous = x
    }
    return true
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
