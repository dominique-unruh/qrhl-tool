package qrhl

import scala.collection.mutable

object Utils {
  def areDistinct[A](values:TraversableOnce[A]): Boolean = {
    val seen = new mutable.HashSet[A]()
    for (v <- values)
      if (!seen.add(v))
        return false
    true
  }
}
