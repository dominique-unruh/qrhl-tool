package hashedcomputation

import hashedcomputation.datatypes.{FingerprintMap, HashedMap}
import org.scalatest.funsuite.AnyFunSuite

import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Awaitable, Future}
import scala.util.control.Breaks

// Implicits
import hashedcomputation.Implicits._
import scala.concurrent.ExecutionContext.Implicits.global

class CacheTest extends AnyFunSuite {
  def await[A](a : Awaitable[A]) : A = Await.result(a, Duration.Inf)

/*  implicit object hashableInt extends Hashable[Int] {
    override def hash[A1 <: Int](int: A1): Hash[A1] = Hash.hashInt(int)
  }*/

/*
  case class HashedIntMap(map: Map[Int,Int]) extends HashedValue {
    override lazy val hash: Hash[this.type] = Hash.hashString(getClass.toString + map.toString())
    // Hack to simplify MapElement
  }
*/

  val emptyInt: Int = -472834729

/*
  case class MapElement(i: Int) extends Element[HashedIntMap, HashedInt] {
    override def extract(value: HashedIntMap): HashedInt =
      HashedInt(value.map.getOrElse(i, emptyInt))

    override def hash: Hash[this.type] = HashedInt(i).hash.asInstanceOf[Hash[this.type]]
  }
*/


/*
  test ("fingerprinted caching OLD") {
    var counter = 0
    val computation: HashedFunction[HashedIntMap, HashedInt] = new HashedFunction[HashedIntMap, HashedInt] {
      override def compute(input: HashedIntMap): Future[(HashedInt, Fingerprint[HashedIntMap])] = Future {
        val map = input.map
        println(s"Computing $map")
        counter += 1
        val looked = new ListBuffer[Int]
        var length = 0
        var current = 0
        Breaks.breakable {
          while (true) {
            val next = map.get(current)
            looked += current
            if (next.isEmpty) Breaks.break();
            length += 1
            current = next.get
            if (length >= 100) Breaks.break()
          }
        }

        val fingerprintEntries = for (i <- looked.toList)
          yield Entry(MapElement(i), Fingerprint(HashedInt(map.getOrElse(i, emptyInt))))
        val fingerprint = Fingerprint(input.hash, Some(fingerprintEntries))
        (HashedInt(length), fingerprint)
      }

      override val hash: Hash[this.type] = Hash.randomHash()
    }

    def compute(map : Map[Int,Int]) : Int = {
      val hashedI = HashedIntMap(map)
      val hashedResultPromise = HashedPromise[HashedIntMap,HashedInt](computation, hashedI)
      val hashedResult = await(hashedResultPromise.get)
      hashedResult.int
    }

    def somethingHappened: Boolean = {
      val happened = counter > 0
      counter = 0
      happened
    }

    assert(!somethingHappened)

    val m1 = Map(0->1, 1->2, 3->4)
    println(s"Compute ${m1}")
    assert(compute(m1) == 2)
    assert(somethingHappened)

    val m2 = Map(0->1, 1->2, 3->4)
    println(s"Compute($m2)")
    assert(compute(m2) == 2)
    assert(!somethingHappened)

    val m3 = Map(0->1, 1->2, 2->3, 3->4)
    println(s"Compute($m3)")
    assert(compute(m3) == 4)
    assert(somethingHappened)
  }
*/

  test ("fingerprinted caching") {
    var counter = 0
    type FM = HashedMap[Int, Int]
    val computation: HashedFunction[FM, Int] = new HashedFunction[FM, Int] {
      override def compute(input: FM): Future[(Int, Fingerprint[FM])] = Future {
//        val map = input.map
        println(s"Computing $input")
        val (map, getFingerprint) = FingerprintMap.withFingerprint(input)
        counter += 1
//        val looked = new ListBuffer[Int]
        var length = 0
        var current = 0
        Breaks.breakable {
          while (true) {
            val next = map.get(current)
//            looked += current
            if (next.isEmpty) Breaks.break();
            length += 1
            current = next.get
            if (length >= 100) Breaks.break()
          }
        }

//        val fingerprintEntries = for (i <- looked.toList)
//          yield Entry(MapElement(i), Fingerprint(HashedInt(map.getOrElse(i, emptyInt))))
//        val fingerprint = Fingerprint(input.hash, Some(fingerprintEntries))
        (length, getFingerprint())
      }

      override val hash: Hash[this.type] = Hash.randomHash()
    }

    def compute(map : Map[Int,Int]) : Int = {
      val map2 = new HashedMap(Hash.randomHash(), map)
      val hashedResultPromise = HashedPromise[FM,Int](computation, map2)
      val hashedResult = await(hashedResultPromise.get)
      hashedResult
    }

    def somethingHappened: Boolean = {
      val happened = counter > 0
      counter = 0
      happened
    }

    assert(!somethingHappened)

    val m1 = Map(0->1, 1->2, 3->4)
    println(s"Compute ${m1}")
    assert(compute(m1) == 2)
    assert(somethingHappened)

    val m2 = Map(0->1, 1->2, 3->4)
    println(s"Compute($m2)")
    assert(compute(m2) == 2)
    assert(!somethingHappened)

    val m3 = Map(0->1, 1->2, 2->3, 3->4)
    println(s"Compute($m3)")
    assert(compute(m3) == 4)
    assert(somethingHappened)
  }


  test ("simple caching") {
    var counter = 0
    val computation: HashedFunction[Int, Int] = HashedFunction[Int, Int] { i =>
      println(s"compute($i)")
      counter += 1;
      i*i
    }

    def compute(i: Int) : Int = {
      val hashedResultPromise = HashedPromise[Int,Int](computation, i)
      val hashedResult = await(hashedResultPromise.get)
      hashedResult
    }

    def somethingHappened: Boolean = {
      val happened = counter > 0
      counter = 0
      happened
    }

    assert(!somethingHappened)

    println("Compute(4)")
    assert(compute(4) == 16)
    assert(somethingHappened)

    println("Compute(4)")
    assert(compute(4) == 16)
    assert(!somethingHappened)

    println("Compute(5)")
    assert(compute(5) == 25)
    assert(somethingHappened)

    println("Compute(4)")
    assert(compute(4) == 16)
    assert(!somethingHappened)
  }

}
