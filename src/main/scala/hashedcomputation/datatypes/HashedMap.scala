package hashedcomputation.datatypes

import hashedcomputation.Fingerprint.Entry
import hashedcomputation.datatypes.FingerprintMap.MapElement
import hashedcomputation.{Element, Fingerprint, Hash, Hashable, HashedOption, HashedValue}

import scala.collection.mutable

final class HashedMap[A, B]
(val _hash: Hash[Map[A, B]], val map: Map[A, B]) extends Map[A, B] with HashedValue {

  override def removed(key: A): Map[A, B] = map.removed(key)

  override def updated[V1 >: B](key: A, value: V1): Map[A, V1] = map.updated(key, value)

  override def get(key: A): Option[B] = map.get(key)

  override def iterator: Iterator[(A, B)] = map.iterator

  override def hash: Hash[this.type] = _hash.asInstanceOf[Hash[this.type]]
}



/** Not thread safe */
final class FingerprintMap[A, B : Hashable]
(private val map: HashedMap[A,B]) extends Map[A,B] {

  private val accesses = new mutable.LinkedHashSet[A]

  def get(key: A): Option[B] = {
    accesses += key
    map.get(key)
  }

  private def fingerprint(): Fingerprint[HashedMap[A,B]] = {
    val entries: List[Entry[HashedMap[A,B], HashedOption[B]]] =
      for (key <- accesses.toList) yield
        Entry(MapElement[A,B](key), Fingerprint(HashedOption(map.get(key))))
    Fingerprint(map.hash, Some(entries))
  }

  override def removed(key: A): Map[A, B] = ???

  override def updated[V1 >: B](key: A, value: V1): Map[A, V1] = ???

  override def iterator: Iterator[(A, B)] = ???
}

object FingerprintMap {
  def withFingerprint[A, B : Hashable]
  (map: HashedMap[A,B]):
  (FingerprintMap[A,B], () => Fingerprint[HashedMap[A,B]]) = {

    val fpMap = new FingerprintMap(map)
    (fpMap, fpMap.fingerprint)
  }

  case class MapElement[A, B : Hashable](key: A)
    extends Element[HashedMap[A,B], HashedOption[B]] {
    override def hash: Hash[this.type] = ???

    override def extract(value: HashedMap[A, B]): HashedOption[B] =
      HashedOption(value.get(key))
    override def extractHash(value: HashedMap[A, B]): Hash[HashedOption[B]] =
      HashedOption.hash(value.get(key))
  }
}
