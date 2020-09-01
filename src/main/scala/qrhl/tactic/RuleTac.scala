package qrhl.tactic

import info.hupel.isabelle.ml.Expr
import info.hupel.isabelle.pure.Term
import info.hupel.isabelle.{Operation, pure}
import org.log4s
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.toplevel.Parser

import scala.collection.immutable.Nil
import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec

case class RuleTac(rule:String) extends IsabelleTac[String]("apply_rule",
  { _ => Isabelle.symbols.unicodeToSymbols(rule) }) {
  override def toString: String = "rule "+rule
}

object RuleTac {
  private val logger = log4s.getLogger
}
