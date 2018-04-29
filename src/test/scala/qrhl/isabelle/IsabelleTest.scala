package qrhl.isabelle

import java.io.IOException
import java.nio.file.Paths

import info.hupel.isabelle.{OfficialPlatform, Platform, System}
import info.hupel.isabelle.api.{Configuration, Version}
import info.hupel.isabelle.setup.Setup.Absent
import info.hupel.isabelle.setup.{Resources, Setup}
import org.scalatest.{FlatSpec, FunSpec, FunSuite}
import qrhl.UserException
import qrhl.toplevel.{Toplevel, ToplevelTest}

import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scala.util.{Left, Right}

import monix.execution.Scheduler.Implicits.global

class IsabelleTest extends FunSuite {
//  test("wrong path") {
//    assertThrows[UserException] {
//      new Isabelle("/tmp/xxx")
//    }
//  }

  test("initialize with path=auto") {
    new Isabelle("auto")
  }

  test("load an empty theory") {
    ToplevelTest.isabelle.getQRHLContextWithFiles("Empty")
  }

//  test("temp") {
//      val version = Version.Stable("2017")
//      val localStoragePath = Paths.get("/tmp/isabelle-temp")
//
//      val platform : Platform = Platform.guess match {
//        case Some(p) => p.withLocalStorage(localStoragePath)
//      }
//
//      val setup : Setup = Setup(Paths.get("/tmp/xxx"), platform, version)
//
//      val resources = Resources.dumpIsabelleResources() match {
//        case Right(r) => r
//      }
//
//      val environment = Await.result(setup.makeEnvironment(resources, Nil), Duration.Inf)
//  }

}
