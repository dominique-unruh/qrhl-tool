// This file is for temporary experiments only

import java.nio.file.Paths

import info.hupel.isabelle.api.{Configuration, Version}
import info.hupel.isabelle.hol.HOLogic
import qrhl.{logic, _}
import qrhl.logic._
import qrhl.toplevel.{Parser, ParserContext, Toplevel, ToplevelTest}
import info.hupel.isabelle.pure._
import info.hupel.isabelle.setup.{Resources, Setup}
import info.hupel.isabelle.{Platform, System, ml}
import qrhl.isabelle.Isabelle
import qrhl.tactic.CaseTac
import qrhl.toplevel.ToplevelTest.isabellePath

import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scala.language.implicitConversions
import info.hupel.isabelle.pure.{Abs, App, Bound, Const, Free, Term, Theory, Type, Var, Context => IContext, Typ => ITyp}

object Test0 {
  def main(args: Array[String]): Unit = {
    try {
      println(1)
      val isabelle = ToplevelTest.isabelle
      println(3)
//      throw new RuntimeException("KJKKJ")
      val isa = isabelle.getQRHLContextWithFiles()
      println(441)
//      val expr = ml.Expr.uncheckedLiteral[String]("\"1\"")
//      isabelle.runExpr(expr, "QRHL_Session")
      isa.prettyTyp(HOLogic.boolT)
      //    isa.runExpr(expr)
      println(5)
    } catch {
      case e : Exception =>
        println(s"EXN $e")
        e.printStackTrace()
//        sys.exit(1)
    } finally {
      sys.exit
    }
  }
}
