package qrhl.logic

import info.hupel.isabelle.hol.HOLogic
import qrhl.isabelle.Isabelle
import info.hupel.isabelle.pure.{Abs, App, Bound, Const, Free, Term, Var, Typ => ITyp, Type => IType}

final class Typ private (private val isabelle:Isabelle.Context, typ:ITyp) {
  override val toString: String = isabelle.prettyTyp(typ)
  val isabelleTyp : ITyp = typ
}
/* object Typ {
  def typeCon(name: String, args: Typ*): Typ =
    IsabelleTyp.typeCon(name, args map { _.asInstanceOf[IsabelleTyp] } :_*)

  def apply(isabelle: Isabelle.Context, str: String): Typ = isabelle match {
    case Some(isa) => IsabelleTyp(isa, str)
    case None => ???
  }
  def bool(isabelle: Option[Isabelle.Context]): Typ = isabelle match {
    case Some(isa) => IsabelleTyp(isa,HOLogic.boolT)
    case None => ???
  }
} */
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

