package qrhl.tactic

import de.unruh.isabelle.mlvalue.Implicits._
import hashedcomputation.{Hash, HashTag}

case object SymTac extends IsabelleTac("sym_tac", { _=>() }) {
  override val hash: Hash[SymTac.this.type] = HashTag()()
}
