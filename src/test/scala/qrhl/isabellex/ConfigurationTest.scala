package qrhl.isabellex

import org.scalatest.funsuite.AnyFunSuite

class ConfigurationTest extends AnyFunSuite {
  test("can load config") {
    val isabelleHome = Configuration.isabelleHome
    println(isabelleHome)
//    val isabelleUser = Configuration.isabelleUserDir
//    println(isabelleUser)
  }
}
