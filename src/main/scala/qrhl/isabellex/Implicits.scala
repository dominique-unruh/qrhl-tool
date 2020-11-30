package qrhl.isabellex

import com.google.common.cache.{CacheBuilder, CacheLoader, LoadingCache}
import de.unruh.isabelle.pure.{Abs, App, Bound, Const, Free, TFree, TVar, Term, Typ, Type, Var}
import hashedcomputation.{Hash, Hashable}
import hashedcomputation.Implicits._
import qrhl.isabellex.Implicits.TypHashable

object Implicits {
  implicit object TypHashable extends Hashable[Typ] {
    implicit private val tH : Hashable[Typ] = TypHashable

    private val cache = CacheBuilder.newBuilder().weakKeys().build(new CacheLoader[Typ, Hash[Typ]] {
      override def load(typ: Typ): Hash[Typ] = typ match { // TODO better hashing
        case Type(name, typs @ _*) =>
          Hash.hashString(s"Type: ${Hash.hashString(name)} ${Hashable.hash(typs.toList)}")
        case TFree(name, sort) =>
          Hash.hashString(s"TFree: ${Hashable.hash(name::sort)}")
        case TVar(name, index, sort) =>
          Hash.hashString(s"TFree: ${Hashable.hash(name::sort)} $index")
      }
    })
    override def hash[A1 <: Typ](typ: A1): Hash[A1] = cache.get(typ).asInstanceOf[Hash[A1]]
  }

  implicit object TermHashable extends Hashable[Term] {
    implicit private val tH : Hashable[Term] = TermHashable

    private val cache: LoadingCache[Term, Hash[Term]] = CacheBuilder.newBuilder().weakKeys().build(new CacheLoader[Term, Hash[Term]] {
      override def load(term: Term): Hash[Term] = term match { // TODO better hashing
        case Const(name, typ) =>
          Hash.hashString(s"Const: $name ${Hashable.hash(typ)}")
        case App(t1, t2) =>
          Hash.hashString(s"App: ${Hashable.hash(t1)}, ${Hashable.hash(t2)}")
        case Free(name, typ) =>
          Hash.hashString(s"Free: $name ${Hashable.hash(typ)}")
        case Var(name, index, typ) =>
          Hash.hashString(s"Var: $name $index ${Hashable.hash(typ)}")
        case Bound(index) =>
          Hash.hashString(s"Bound: $index")
        case Abs(name, typ, body) =>
          Hash.hashString(s"Abs: $name ${Hashable.hash(typ)} ${Hashable.hash(body)}")
      }
    })
    override def hash[A1 <: Term](term: A1): Hash[A1] = cache.get(term).asInstanceOf[Hash[A1]]
  }
}
