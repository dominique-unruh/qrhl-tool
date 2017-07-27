import java.nio.file.Paths

import info.hupel.isabelle.api.{Configuration, Version}
import qrhl._
import qrhl.logic._
import qrhl.toplevel.{Parser, ParserContext, Toplevel, ToplevelTest}
import info.hupel.isabelle.pure._
import info.hupel.isabelle.setup.{Resources, Setup}
import info.hupel.isabelle.{Platform, System, ml}
import qrhl.isabelle.Isabelle
import qrhl.toplevel.ToplevelTest.isabellePath

import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scala.language.implicitConversions

object Test0 {
/*
  var state: State = State.empty
  implicit def parserContext : ParserContext = state.parserContext
  implicit def pp(str:String) : Block = Parser.parseAll(Parser.block,str).get
  implicit def pe(str:String) : Expression = Parser.parseAll(Parser.expression(state.assertionT),str).get
  implicit def pt(str:String) : Typ = Typ(parserContext.isabelle.get, str)
*/

/*
  def openGoal(goal:Subgoal) : Unit = {
    println("Starting proof.")
    state = state.openGoal(goal)
    println(state)
  }

  def applyTactic(tactic:Tactic) : Unit = {
    println(s"Applying tactic $tactic.")
    state = state.applyTactic(tactic)
    println(state)
  }
*/

//  def loadIsabelle(path:String) : Unit = {
//    println(s"Loading Isabelle at $path.")
//    state = state.loadIsabelle(path)
//  }

/*
  def declareVariable(name:String, typ:Typ, quantum:Boolean=false) : Unit = {
    println(s"Declaring ${if (quantum) "quantum" else "classical"} variable $name : $typ.")
    state = state.declareVariable(name,typ,quantum=quantum)
  }
*/

/*
  def declareAmbientVariable(name:String, typ:Typ) : Unit = {
    println(s"Declaring ambient variable $name : $typ.")
    state = state.declareAmbientVariable(name,typ)
  }
*/

/*
  def declareProgram(name: String, program: Block) : Unit = {
    println(s"Declaring program $program.")
    state = state.declareProgram(name,program)
  }
*/

/*
  def testSimple(): Unit = {
    import tactic._
    try {
//      loadIsabelle("/opt/Isabelle2016-1")

      declareVariable("a", "int")
      declareVariable("b", "int")
      declareVariable("c", "int")
      declareVariable("q", "nat", quantum = true)
      declareProgram("test", "c <$ uniform {0,1}; b <- b+c;")
      declareAmbientVariable("z", "int")

      openGoal(QRHLSubgoal(
        "a <- z;",
        "call test;",
        "Qeq[q1=q2] ⊓ Cla[b2=1]",
        "Cla[a1 <= b2+z]    ⊓    Qeq[q1=q2]"))

      applyTactic(InlineTac("test"))

      applyTactic(WpTac(left = true))
      applyTactic(SimpTac)

      applyTactic(WpTac(left = false))
      applyTactic(SimpTac)

      applyTactic(WpTac(left = false))
      applyTactic(SimpTac)

      applyTactic(SkipTac)
      applyTactic(SimpTac)
      applyTactic(TrueTac)
    } catch {
      case e: Throwable => e.printStackTrace()
    } finally {
      System.exit(0)
    }
  }
*/

//  def run(cmd:String) : Unit = {
//    Parser.parseAll(Parser.command,cmd) match {
//      case Parser.Success(cmd2,_) =>
//        state = cmd2.act (state)
//      case res @ Parser.NoSuccess(msg) =>
//        println(msg)
//        println(res)
//    }
//  }



  def main(args: Array[String]): Unit = {
//    val version = Version.Stable("2016-1")
//    val isabellePath = "/opt/Isabelle2016-1"
//    val setup = Setup(Paths.get(isabellePath), Platform.guess.get, version)
//    val resources = Resources.dumpIsabelleResources().right.get
//    val environment = Await.result(setup.makeEnvironment(resources), Duration.Inf)
//    val config: Configuration = Configuration.simple("QRHL")
//    assert(System.build(environment, config))
//    val system = Await.result(System.create(environment, config), Duration.Inf)
    val isa = new Isabelle(isabellePath)

    try {
/*
      val use0: ml.Expr[String => Unit] =
        ml.Expr.uncheckedLiteral("(fn name => Thy_Info.use_thy (name,Position.none))")
      val get0: ml.Expr[String => Unit] =
        ml.Expr.uncheckedLiteral("Thy_Info.get_theory name")
//      val use: ml.Expr[String => Theory] =
//        ml.Expr.uncheckedLiteral("(fn name => Thy_Info.use_thy (name,Position.none); Thy_Info.get_theory name)")
      val thyName = "PrgEnc"
      println("use0")
      isa.runExpr(use0(thyName),"QRHL_Protocol")
      println("done")
//      val ref = isa.getRef(Context.initGlobal(get0(thyName)), thyName)
//      println(ref)
*/
      val ctx = isa.getContextFile("PrgEnc")
      println(ctx)
    } finally {
      isa.dispose()
    }
  }
}
