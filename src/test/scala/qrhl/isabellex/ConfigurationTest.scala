package qrhl.isabellex

import org.scalatest.FunSuite

class ConfigurationTest extends FunSuite {
  test("can load config") {
    val isabelleHome = Configuration.isabelleHome
    println(isabelleHome)
    val isabelleUser = Configuration.isabelleUserDir
    println(isabelleUser)
  }
}
