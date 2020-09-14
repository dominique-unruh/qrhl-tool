package qrhl.tactic

import de.unruh.isabelle.mlvalue.MLValue.Implicits._

case object SymTac extends IsabelleTac("sym_tac", { _=>() })
