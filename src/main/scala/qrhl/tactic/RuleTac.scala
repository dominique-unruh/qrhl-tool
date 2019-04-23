package qrhl.tactic

import info.hupel.isabelle.ml.Expr
import info.hupel.isabelle.pure.Term
import info.hupel.isabelle.{Operation, pure}
import org.log4s
import qrhl._
import qrhl.isabelle.RichTerm
import qrhl.toplevel.Parser

import scala.collection.immutable.Nil

import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec

case class RuleTac(rule:String, instantiations:List[(String,RichTerm)]=Nil) extends IsabelleTac[(String,List[(String,Term)])]("apply_rule",
  { _ => (rule,instantiations.map{case (n,t) => (n,t.isabelleTerm)}) }) {
  override def toString: String =
    if (instantiations.isEmpty) "rule "+rule
    else s"rule $rule with (${instantiations.map{case (n,t) => s"$n:=$t"}.mkString("; ")})"
}

object RuleTac {
  private val logger = log4s.getLogger
}
