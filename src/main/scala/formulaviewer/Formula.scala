package formulaviewer

import de.unruh.isabelle.control.{Isabelle, IsabelleControllerException}
import de.unruh.isabelle.pure.{Abs, App, Bound, Const, Context, Free, Term, Var}
import formulaviewer.Formula.AppMulti

class Formula(val term: Term)(implicit val isabelle: Isabelle, val context: Context) {
  def pretty(contextMap: ContextMap): String = term.pretty(contextMap(context))
  def prettyTyp(contextMap: ContextMap): String =
    try term.fastType.pretty(contextMap(context))
    catch {
      case _: IsabelleControllerException => "??"
    }

  def descriptiveString(contextMap: ContextMap) = term match {
    case Const(name, _) => s"${pretty(contextMap)} :: ${prettyTyp(contextMap)} (const: $name)"
    case Bound(i) => s"Bound variable (index $i)"
    case _ => s"${pretty(contextMap)} :: ${prettyTyp(contextMap)}"
  }

  override lazy val toString: String = pretty(ContextMap.id)

  lazy val children : List[Formula] = term match {
    case AppMulti(ts @ _*) => ts.map(new Formula(_)).toList
    case Abs(_, _, body) => List(new Formula(body))
    case Const(_,_) | Free(_,_) | Var(_,_,_) | Bound(_) => Nil
  }
}

object Formula {
  def fromString(string: String)(implicit isabelle: Isabelle, context: Context): Formula = {
    val term = Term(context, string)
    new Formula(term)
  }

  object Numeral {
    private def numeralToInt(term: Term): BigInt = term match {
      case Const("Num.num.One", _) => BigInt(1)
      case App(Const("Num.num.Bit0", _), n) => numeralToInt(n) << 1
      case App(Const("Num.num.Bit1", _), n) => (numeralToInt(n) << 1).setBit(0)
    }

    def unapply(term: Term): Option[BigInt] = term match {
      case App(Const("Num.numeral_class.numeral", _), num) =>
        try Some(numeralToInt(num))
        catch { case _ : MatchError => None }
      case _ => None
    }
  }

  object AppMulti {
    def unapplySeq(term: Term): Option[Seq[Term]] = term match {
      case App(t1, t2) => t1 match {
        case AppMulti(ts@_*) => Some(ts.appended(t2))
        case _ => Some(Seq(t1, t2))
      }
      case _ => None
    }
  }
}