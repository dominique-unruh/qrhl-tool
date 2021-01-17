package qrhl.tactic

import de.unruh.isabelle.mlvalue.Implicits._
import hashedcomputation.Implicits._

import hashedcomputation.{Hash, HashTag, Hashable}

case class SquashTac(left:Boolean)
  extends IsabelleTac[Boolean]("squash_tac", { _ => left }) {
  override def toString: String = if (left) "squash left" else "squash right"

  override def hash: Hash[SquashTac.this.type] = HashTag()(Hashable.hash(left))
}
