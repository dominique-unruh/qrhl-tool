package qrhl.tactic
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.logic.{CVariable, ExpressionIndexed, Sample, Statement, VarTerm}
import qrhl.{State, UserException}
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.pure.Term
import hashedcomputation.{Hash, HashTag, Hashable}

case object RndEqualTac
  extends IsabelleTac[Unit]("joint_sample_equal_tac", { _ => () }) {
  override def toString: String = s"rnd"

  override val hash: Hash[RndEqualTac.this.type] = HashTag()()
}

case class RndWitnessTac(left:VarTerm[CVariable], right:VarTerm[CVariable], witness:ExpressionIndexed)
  extends IsabelleTac[Term]("joint_sample_tac", { _ => witness.term.isabelleTerm }) {
  override def toString: String = s"rnd $left,$right <- $witness"

  override def hash: Hash[RndWitnessTac.this.type] = HashTag()(Hashable.hash(left), Hashable.hash(right))
}

