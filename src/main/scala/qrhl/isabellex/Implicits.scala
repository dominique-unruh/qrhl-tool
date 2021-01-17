package qrhl.isabellex

import com.google.common.cache.{CacheBuilder, CacheLoader, LoadingCache}
import de.unruh.isabelle.pure.{Abs, App, Bound, Const, Free, TFree, TVar, Term, Typ, Type, Var}
import hashedcomputation.{Hash, HashTag, Hashable, RawHash}
import hashedcomputation.Implicits._
import qrhl.isabellex.Implicits.TypHashable

object Implicits {
  implicit object TypHashable extends Hashable[Typ] {
    implicit private val tH : Hashable[Typ] = TypHashable

    private val cache = CacheBuilder.newBuilder().weakKeys().build(new CacheLoader[Typ, Hash[Typ]] {
      override def load(typ: Typ): Hash[Typ] = typ match {
        case Type(name, typs @ _*) =>
          HashTag()(RawHash.hashString(name), Hashable.hash(typs.toList))
        case TFree(name, sort) =>
          HashTag()(RawHash.hashString(name), Hashable.hash(sort))
        case TVar(name, index, sort) =>
          HashTag()(RawHash.hashString(name), RawHash.hashInt(index), Hashable.hash(sort))
      }
    })
    override def hash[A1 <: Typ](typ: A1): Hash[A1] = cache.get(typ).asInstanceOf[Hash[A1]]
  }

  implicit object TermHashable extends Hashable[Term] {
    implicit private val tH : Hashable[Term] = TermHashable

    private val cache: LoadingCache[Term, Hash[Term]] = CacheBuilder.newBuilder().weakKeys().build(new CacheLoader[Term, Hash[Term]] {
      override def load(term: Term): Hash[Term] = term match { // TODO better hashing
        case Const(name, typ) =>
          HashTag()(RawHash.hashString(name), Hashable.hash(typ))
        case App(t1, t2) =>
          HashTag()(Hashable.hash(t1), Hashable.hash(t2))
        case Free(name, typ) =>
          HashTag()(RawHash.hashString(name), Hashable.hash(typ))
        case Var(name, index, typ) =>
          HashTag()(RawHash.hashString(name), RawHash.hashInt(index), Hashable.hash(typ))
        case Bound(index) =>
          HashTag()(RawHash.hashInt(index))
        case Abs(name, typ, body) =>
          HashTag()(RawHash.hashString(name), Hashable.hash(typ), Hashable.hash(body))
      }
    })
    override def hash[A1 <: Term](term: A1): Hash[A1] = cache.get(term).asInstanceOf[Hash[A1]]
  }
}
