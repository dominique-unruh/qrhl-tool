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

class IsabelleTest extends FunSuite {
  test("wrong path") {
    assertThrows[UserException] {
      new Isabelle("/tmp/xxx")
    }
  }

  test("initialize with path=auto") {
    new Isabelle("auto")
  }

  test("load an empty theory") {
    ToplevelTest.isabelle.getQRHLContextWithFiles("Empty")
  }

}
