package formulaviewer

import de.unruh.isabelle.pure.Context

class ContextMap(val function: Context => Context) extends AnyVal {
  def apply(ctxt: Context): Context = function(ctxt)

  def *(other: ContextMap) = new ContextMap(ctxt => apply(other(ctxt)))

  def same(other: ContextMap): Boolean = function eq other.function
}

object ContextMap {
  val id = new ContextMap(identity)
}