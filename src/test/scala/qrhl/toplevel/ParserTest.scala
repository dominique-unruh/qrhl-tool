package qrhl.toplevel

import info.hupel.isabelle.ProverResult
import info.hupel.isabelle.hol.HOLogic
import org.scalatest.FunSuite
import qrhl.UserException
import qrhl.logic.{Block, Call, VTCons, VTSingle}

class ParserTest extends FunSuite {
  implicit lazy val parserContext: ParserContext = {
    val tl = Toplevel.makeToplevelWithTheory()
    // If this fails for parsing reasons, just directly compose commands instead
    tl.execCmd("classical var x : int")
    tl.execCmd("classical var y : int")
    tl.execCmd("classical var z : int")
    tl.execCmd("classical var w : int")
    tl.execCmd("adversary A0 vars x")
    tl.execCmd("adversary B0 vars x")
    tl.execCmd("adversary A1 vars x calls ?")
    tl.execCmd("adversary A2 vars x calls ?, ?")
    tl.state.parserContext
  }

  test("nested varterm paren") {
    implicit val vtSingle: String => VTSingle[String] = VTSingle[String]
    val vt = Parser.parseAll(Parser.varterm, "((x,y),w,z)")
    println(vt)
    assert(vt.get==VTCons(VTCons("x","y"),VTCons("w","z")))
  }

  test("nested varterm noparen") {
    implicit val vtSingle: String => VTSingle[String] = VTSingle[String]
    val vt = Parser.parseAll(Parser.varterm, "(x,y),w,z")
    println(vt)
    assert(vt.get==VTCons(VTCons("x","y"),VTCons("w","z")))
  }

  test("assign tuple") {
    val assign = Parser.parseAll(Parser.assign, "(x,y) <- (y,x);").get
    println(assign)
    assert(assign.variable.toList.map(_.name)==List("x","y"))
    assign.checkWelltyped(parserContext.isabelle.get)
  }

  test("sample tuple") {
    val sample = Parser.parseAll(Parser.sample, "(x,y) <$ uniform UNIV;").get
    println(sample)
    assert(sample.variable.toList.map(_.name)==List("x","y"))
    sample.checkWelltyped(parserContext.isabelle.get)
  }

  test("parse while loop") {
    val whileLoop = Parser.parseAll(Parser.whileLoop, "while (True) { skip; }").get
    println(whileLoop)
  }

  test("parse undeclared variable") {
    assertThrows[UserException] {
      Parser.parseAll(Parser.expression(HOLogic.boolT), "hello")
    }
  }

  test("fail to parse while loop") {
    assertThrows[ProverResult.Failure] {
      val whileLoop = Parser.parseAll(Parser.whileLoop, "while (1) { skip; }")
    }
  }

  test("adversary") {
    val decl = Parser.parseAll(Parser.declareAdversary, "adversary A vars x, y").get
    assert(decl.name=="A")
    assert(decl.cvars.map(_.name)==List("x","y"))
    assert(decl.qvars.isEmpty)
    assert(decl.numOracles==0)
  }

  test("adversary calls") {
    val decl = Parser.parseAll(Parser.declareAdversary, "adversary A vars x, y calls ?, ?").get
    assert(decl.name=="A")
    assert(decl.cvars.map(_.name)==List("x","y"))
    assert(decl.qvars.isEmpty)
    assert(decl.numOracles==2)
  }

  test("call") {
    val call = Parser.parseAll(Parser.call, "call A0;").get
    assert(call==Call("A0"))
  }

  test("call 1 arg") {
    val call = Parser.parseAll(Parser.call, "call A1(A0);").get
    assert(call==Call("A1",Call("A0")))
  }

  test("call 2 arg") {
    val call = Parser.parseAll(Parser.call, "call A2(A0,B0);").get
    assert(call==Call("A2",Call("A0"),Call("B0")))
  }

  test("call 2 nested") {
    val call = Parser.parseAll(Parser.call, "call A2(A1(B0),A0);").get
    assert(call==Call("A2",Call("A1",Call("B0")),Call("A0")))
  }

  test("call wrong num args") {
    assertThrows[UserException] {
      val call = Parser.parseAll(Parser.call, "call A1").get
      print(call)
    }
  }

  test("program with oracles") {
    val progDecl = Parser.parseAll(Parser.declareProgram,
      """
        |program test(a,b,c) := { call a; call b; call A1(c); }
      """.stripMargin)

    assert(progDecl.successful)
    val progDecl2 = progDecl.get

    println(progDecl2)
    assert(progDecl2.name == "test")
    assert(progDecl2.oracles == List("a","b","c"))
    assert(progDecl2.program == Block(Call("a"),Call("b"),Call("A1",Call("c"))))
  }

}
