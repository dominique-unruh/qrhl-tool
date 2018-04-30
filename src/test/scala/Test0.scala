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

import scala.util.Right


import monix.execution.Scheduler.Implicits.global

object Test0 {
  def main(args: Array[String]): Unit = {
    try {
      val version = Version.Stable("2017")
      val localStoragePath = Paths.get("/tmp/isabelle-temp")

      val platform: Platform = Platform.guess match {
        case Some(p) => p.withLocalStorage(localStoragePath)
      }

      val setup: Setup = Setup(Paths.get("/tmp/xxx"), platform, version)

      val resources = Resources.dumpIsabelleResources() match {
        case Right(r) => r
      }

      val environment = Await.result(setup.makeEnvironment(resources, Nil), Duration.Inf)
    }
    finally {
      sys.exit(0)
    }
  }
}
