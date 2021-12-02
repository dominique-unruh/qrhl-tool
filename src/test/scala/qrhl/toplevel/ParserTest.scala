package qrhl.toplevel

import java.io.IOException

import org.scalatest.funsuite.AnyFunSuite
import qrhl.UserException
import qrhl.isabellex.IsabelleX
import qrhl.logic.{Block, CVariable, Call, Local, VTCons, VTSingle}
import IsabelleX.{globalIsabelle => GIsabelle}

class ParserTest extends AnyFunSuite {
  implicit lazy val parserContext: ParserContext = {
    val tl = ToplevelTest.makeToplevelWithTheory()
    // If this fails for parsing reasons, just directly compose commands instead
    tl.execCmd("classical var x : int")
    tl.execCmd("classical var y : int")
    tl.execCmd("classical var z : int")
    tl.execCmd("classical var w : int")
    tl.execCmd("adversary A0 free x")
    tl.execCmd("adversary B0 free x")
    tl.execCmd("adversary A1 free x calls ?")
    tl.execCmd("adversary A2 free x calls ?, ?")
    tl.state.parserContext
  }

  test("fact") {
    val vt = Parser.parseAll(Parser.fact, "a[b, c]")
    println(vt)
    assert(vt.get=="a[b, c]")
  }

  test("fact (multiple)") {
    val vt = Parser.parseAll(Parser.rep(Parser.fact), "a[b, c] hello(1) bla[blubb[hello]]")
    println(vt)
    assert(vt.get==List("a[b, c]", "hello(1)", "bla[blubb[hello]]"))
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
      Parser.parseAll(Parser.expression(GIsabelle.boolT, indexed = false), "hello")
    }
  }

  test("parse expression with indexed classical variables") {
    val e = Parser.parseAll(Parser.expression(GIsabelle.intT, indexed=true), "x1").get
    assert(e.toString == "x1")
  }

  test("parse expression with indexed quantum variables") {
    val e = Parser.parseAll(Parser.expression(GIsabelle.boolT, indexed=true), "q1 = id").get
    assert(e.toString == "q1 = id")
  }

  test("fail to parse while loop") {
    assertThrows[IOException] { // TODO: Mark which exception is actually thrown
      val whileLoop = Parser.parseAll(Parser.whileLoop, "while (1) { skip; }")
    }
  }

  test("adversary") {
    val decl = Parser.parseAll(Parser.declareAdversary, "adversary A free x, y").get
    assert(decl.name=="A")
    assert(decl.free.map(_.name)==List("x","y"))
    assert(decl.numOracles==0)
  }

  test("adversary calls") {
    val decl = Parser.parseAll(Parser.declareAdversary, "adversary A free x, y calls ?, ?").get
    assert(decl.name=="A")
    assert(decl.free.map(_.name)==List("x","y"))
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
    assert(progDecl2.program == Block(Call("a"), Call("b"), Call("A1", Call("c"))))
  }

  test("program with oracles - name conflict with program variable") {
    assertThrows[UserException] {
      Parser.parseAll(Parser.declareProgram, "program P(x) := { call x; }.").get
    }
  }

  test("local variables") {
    val block = Parser.parseAll(Parser.parenBlock,
      """{
        |  local x;
        |  skip;
        |}""".stripMargin)

    println(block)

    assert(block.get == new Local(List(CVariable.fromName("x", GIsabelle.intT)), Block()))
  }

  test("commandSpan") {
    def check(str: String, expect: String) = {
      Parser.parse(Parser.commandSpan, str) match {
        case Parser.Success(_, next) =>
          assert(str.substring(0, next.offset) == expect)
        case Parser.NoSuccess(_, _) =>
          fail(s"No match ($str)")
      }
    }

    check("test { 1.2 }.", "test { 1.2 }.")
    check("hello. huhu.", "hello.")
    check("""include "x.html". bla""", """include "x.html".""")
    check("rule x.y. bla", "rule x.y.")
  }
}
