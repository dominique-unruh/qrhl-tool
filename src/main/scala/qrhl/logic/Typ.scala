package qrhl.logic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.{Typ => ITyp, Type => IType}
import qrhl.isabelle.Isabelle

final class Typ private (val isabelleTyp:ITyp) {
  def distr: Typ = Typ(IType("QRHL_Core.distr",List(isabelleTyp)))

  override val toString: String = Isabelle.theContext.prettyTyp(isabelleTyp)
//  val isabelleTyp : ITyp = typ

  override def equals(o: Any): Boolean = o match {
    case t:Typ => isabelleTyp==t.isabelleTyp
    case _ => false
  }

  def *(o: Typ) = Typ(Isabelle.prodT(isabelleTyp,o.isabelleTyp))

  override def hashCode: Int = isabelleTyp.hashCode
}

object Typ {
  def typeCon(name: String, args: Typ*): Typ =
    Typ(IType(name, args.map { _.isabelleTyp }.toList))
  def bool(isabelle: Isabelle.Context): Typ = Typ(HOLogic.boolT)

  def apply(isabelle:Isabelle.Context, str:String) : Typ = {
    val typ = isabelle.readTyp(Isabelle.unicodeToSymbols(str))
    Typ(typ)
  }
  def apply(typ:ITyp) : Typ = {
//    val pretty = Isabelle.symbolsToUnicode(isabelle.prettyTyp(typ))
    new Typ(typ)
  }
}

