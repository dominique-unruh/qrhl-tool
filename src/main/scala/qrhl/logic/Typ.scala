package qrhl.logic

import info.hupel.isabelle.hol.HOLogic
import qrhl.isabelle.Isabelle
import info.hupel.isabelle.pure.{Abs, App, Bound, Const, Free, Term, Var, Typ => ITyp, Type => IType}

final class Typ private (private val isabelle:Isabelle.Context, val isabelleTyp:ITyp) {
  def distr: Typ = Typ(isabelle, IType("QRHL.distr",List(isabelleTyp)))

  override val toString: String = isabelle.prettyTyp(isabelleTyp)
//  val isabelleTyp : ITyp = typ

  override def equals(o: Any): Boolean = o match {
    case t:Typ => isabelleTyp==t.isabelleTyp
    case _ => false
  }

  def *(o: Typ) = Typ(isabelle, IType("Product_Type.prod",List(isabelleTyp,o.isabelleTyp)))

  override def hashCode: Int = isabelleTyp.hashCode
}

object Typ {
  def typeCon(name: String, args: Typ*): Typ =
    Typ(args.head.isabelle,
      IType(name, args.map { _.isabelleTyp }.toList))
  def bool(isabelle: Isabelle.Context): Typ = Typ(isabelle,HOLogic.boolT)

  def apply(isabelle:Isabelle.Context, str:String) : Typ = {
    val typ = isabelle.readTyp(Isabelle.unicodeToSymbols(str))
    Typ(isabelle,typ)
  }
  def apply(isabelle:Isabelle.Context, typ:ITyp) : Typ = {
//    val pretty = Isabelle.symbolsToUnicode(isabelle.prettyTyp(typ))
    new Typ(isabelle, typ)
  }
}

