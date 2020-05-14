import qrhl.isabelle.Isabelle

import scala.collection.JavaConverters._
import scala.collection.immutable.ListSet

import qrhl.Utils.ListSetUtils

object Test0 {
  def main(args: Array[String]): Unit = {
    val l1 = ListSet(1,2,3)
    val l2 = ListSet(4,5,6)
    for (x <- l2) println(x)
    val l = l1 +++ l2
    println(l)
    println(ListSet.empty +++ l2)
  }
}