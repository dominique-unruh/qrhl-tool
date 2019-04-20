package qrhl.tactic

import info.hupel.isabelle.pure.{App, Const}
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}

case object O2HTac extends IsabelleTac("o2h_tac", {_=>()}) {
  // TODO: produces a lot of subgoals -> remove as many as possible
}
