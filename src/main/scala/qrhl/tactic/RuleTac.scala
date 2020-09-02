package qrhl.tactic

import info.hupel.isabelle.ml.Expr
import info.hupel.isabelle.pure.Term
import info.hupel.isabelle.{Operation, pure}
import org.log4s
import qrhl._
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.toplevel.Parser

import isabelle.control.MLValue.Implicits._

case class RuleTac(rule:String) extends IsabelleTac[String]("apply_rule",
  { _ => IsabelleX.symbols.unicodeToSymbols(rule) }) {
  override def toString: String = "rule "+rule
}

object RuleTac {
  private val logger = log4s.getLogger
}
