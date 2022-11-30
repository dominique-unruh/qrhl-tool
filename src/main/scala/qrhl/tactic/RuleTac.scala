package qrhl.tactic

import org.log4s
import qrhl._
import qrhl.isabellex.IsabelleX
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.exceptions.ErrorMLException
import hashedcomputation.{Hash, HashTag, Hashable}
import hashedcomputation.Implicits._

import java.io.PrintWriter

case class RuleTac(rule:String) extends IsabelleTac[String]("apply_rule",
  { _ => IsabelleX.symbols.unicodeToSymbols(rule) }) {
  override def toString: String = "rule "+rule

  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] =
    try super.apply(state, goal)
    catch {
      case e : ErrorMLException => throw UserException(e.message) // Usually a more-or-less informative message, can forward it to the user as a non-internal error
    }

  override def hash: Hash[RuleTac.this.type] = HashTag()(Hashable.hash(rule))
}

object RuleTac {
//  private val logger = log4s.getLogger
}
