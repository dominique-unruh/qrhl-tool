package formulaviewer

import de.unruh.isabelle.control.{Isabelle, OperationCollection}
import de.unruh.isabelle.pure.{Context, Term, Theory}
import qrhl.isabellex.IsabelleX
import qrhl.isabellex.IsabelleX.globalIsabelle

import scala.concurrent.Future

import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._

object Utils {
  def printTermReliably(context: Context, term: Term)(implicit isabelle: Isabelle): String = {
    // Only works when the implicit isabelle is actually the globalIsabelle from qrhl-tool
    // Could be avoided but then we need to copy the definition of print_term (in ML) somewhere accessible (or inline it here).
    assert(isabelle eq globalIsabelle.isabelleControl)
    globalIsabelle.Ops.print_term(context, term).retrieveNow
  }
}
