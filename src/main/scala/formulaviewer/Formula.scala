package formulaviewer

import de.unruh.isabelle.control.{Isabelle, IsabelleControllerException}
import de.unruh.isabelle.pure.{Abs, App, Bound, Const, Context, Free, Term, Var}

class Formula(term: Term)(implicit isabelle: Isabelle, context: Context) {
  val pretty: String = term.pretty(context)
  val prettyTyp: String =
    try term.fastType.pretty(context)
    catch {
      case _: IsabelleControllerException => "??"
    }

  override def toString: String = term match {
    case Const(name, _) => s"$pretty :: $prettyTyp (const: $name)"
    case Bound(i) => s"Bound variable (index $i)"
    case _ => s"$pretty :: $prettyTyp"
  }
  lazy val children : List[Formula] = term match {
    case App(t1,t2) => List(new Formula(t1), new Formula(t2))
    case Abs(_, _, body) => List(new Formula(body))
    case Const(_,_) | Free(_,_) | Var(_,_,_) | Bound(_) => Nil
  }
}

object Formula {
  def fromString(string: String)(implicit isabelle: Isabelle, context: Context): Formula = {
    val term = Term(context, string)
    new Formula(term)
  }
}