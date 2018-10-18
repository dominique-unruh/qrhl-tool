package qrhl.tactic

import info.hupel.isabelle.{Operation, pure}
import info.hupel.isabelle.pure.Term
import org.log4s


object JointMeasureTacTmp {
  val op: Operation[(Unit, Term, BigInt), Option[List[Term]]] =
    Operation.implicitly[(Unit, pure.Term, BigInt), Option[List[pure.Term]]]("joint_measure_simple_tac")
}

case object JointMeasureTac extends IsabelleTac(JointMeasureTacTmp.op, { _ => () }) {
  override def toString: String = "measure"
  private val logger = log4s.getLogger
}
