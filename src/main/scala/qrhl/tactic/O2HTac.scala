package qrhl.tactic

import de.unruh.isabelle.mlvalue.Implicits._
import hashedcomputation.{Hash, HashTag}

case object O2HTac extends IsabelleTac("o2h_tac", {_=>()}) {
  override val hash: Hash[O2HTac.this.type] = HashTag()()
}
