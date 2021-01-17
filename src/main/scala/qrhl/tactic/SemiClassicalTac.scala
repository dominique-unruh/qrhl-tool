package qrhl.tactic

import de.unruh.isabelle.mlvalue.Implicits._
import hashedcomputation.{Hash, HashTag}

case object SemiClassicalTac extends IsabelleTac("semiclassical_tac", {_=>()}) {
  override val hash: Hash[SemiClassicalTac.this.type] = HashTag()()
}
