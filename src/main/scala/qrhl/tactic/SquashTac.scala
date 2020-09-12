package qrhl.tactic

import isabelle.mlvalue.MLValue.Implicits._

case class SquashTac(left:Boolean)
  extends IsabelleTac[Boolean]("squash_tac", { _ => left }) {
  override def toString: String = if (left) "squash left" else "squash right"
}
