package qrhl

import scalaz.Memo

import scala.collection.mutable
import scala.ref.SoftReference

object Utils {
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
