package qrhl.tactic

import de.unruh.isabelle.mlvalue.Implicits._

case class SquashTac(left:Boolean)
  extends IsabelleTac[Boolean]("squash_tac", { _ => left }) {
  override def toString: String = if (left) "squash left" else "squash right"
}
