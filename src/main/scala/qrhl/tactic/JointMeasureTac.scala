package qrhl.tactic

import org.log4s
import de.unruh.isabelle.mlvalue.Implicits._

//object JointMeasureTacTmp {
//  val op: Operation[(Unit, Term, BigInt), Option[(List[RichTerm],BigInt)]] =
//    Operation.implicitly[(Unit, pure.Term, BigInt), Option[(List[RichTerm],BigInt)]]("joint_measure_simple_tac")
//}

case object JointMeasureTac extends IsabelleTac[Unit]("joint_measure_simple_tac", { _ => () }) {
  override def toString: String = "measure"
  private val logger = log4s.getLogger
}
