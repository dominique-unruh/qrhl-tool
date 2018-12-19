package qrhl.tactic

import info.hupel.isabelle.{Operation, pure}
import info.hupel.isabelle.pure.Term
import org.log4s
import qrhl.isabelle.RichTerm

import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec

object JointMeasureTacTmp {
  val op: Operation[(Unit, Term, BigInt), Option[(List[RichTerm],BigInt)]] =
    Operation.implicitly[(Unit, pure.Term, BigInt), Option[(List[RichTerm],BigInt)]]("joint_measure_simple_tac")
}

case object JointMeasureTac extends IsabelleTac(JointMeasureTacTmp.op, { _ => () }) {
  override def toString: String = "measure"
  private val logger = log4s.getLogger
}
