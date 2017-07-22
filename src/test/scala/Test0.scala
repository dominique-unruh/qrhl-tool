import qrhl._
import qrhl.logic._
import qrhl.toplevel.{Parser, ParserContext}

import scala.language.implicitConversions

object Test0 {
  var state: State = State.empty
  implicit def parserContext : ParserContext = state.parserContext
  implicit def pp(str:String) : Block = Parser.parseAll(Parser.block,str).get
  implicit def pe(str:String) : Expression = Parser.parseAll(Parser.expression(state.assertionT),str).get
  implicit def pt(str:String) : Typ = Typ(parserContext.isabelle.get, str)

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

//  def loadIsabelle(path:String) : Unit = {
//    println(s"Loading Isabelle at $path.")
//    state = state.loadIsabelle(path)
//  }

  def declareVariable(name:String, typ:Typ, quantum:Boolean=false) : Unit = {
    println(s"Declaring ${if (quantum) "quantum" else "classical"} variable $name : $typ.")
    state = state.declareVariable(name,typ,quantum=quantum)
  }

  def declareAmbientVariable(name:String, typ:Typ) : Unit = {
    println(s"Declaring ambient variable $name : $typ.")
    state = state.declareAmbientVariable(name,typ)
  }

  def declareProgram(name: String, program: Block) : Unit = {
    println(s"Declaring program $program.")
    state = state.declareProgram(name,program)
  }

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

  def run(cmd:String) : Unit = {
    Parser.parseAll(Parser.command,cmd) match {
      case Parser.Success(cmd2,_) =>
        state = cmd2.act (state)
      case res @ Parser.NoSuccess(msg) =>
        println(msg)
        println(res)
    }
  }

  def main(args: Array[String]): Unit = {
    import tactic._
    try {
//      val test = "a(b);)"
//      val res = Parser.parse(Parser.scanExpression,test)
//      println(res)

      run("isabelle /opt/Isabelle2016-1")

//      loadIsabelle("/opt/Isabelle2016-1")
//      println("A,B <q EPR;" : Block)
//      return

      run("classical var a : bit")
      run("classical var c : bit")

//      declareVariable("a", "bit")
//      declareVariable("c", "bit")
      run("quantum var A : bit")
//      declareVariable("A", "bit", quantum=true)
      declareVariable("B", "bit", quantum=true)
      declareVariable("C", "bit", quantum=true)

      // teleports from C to B
//      declareProgram("teleport", "" +
      run("program teleport :=" +
        "A,B <q EPR;" +
        "on C,A apply CNOT;" +
        "on C apply H;" +
        "a <- measure A in computational_basis;" +
        "c <- measure B in computational_basis;" +
        "if (a=1) then on B apply X; else skip;" +
        "if (c=1) then on B apply Z; else skip;" +
        "")

//      println("Declared teleport.")

      run("qrhl {Qeq[C1=A2]} call teleport; ~ skip; {Qeq[B1=A2]}")

//      openGoal(QRHLSubgoal(
//        "call teleport;",
//        "skip;",
//        "Qeq[C1=A2]",
//        "Qeq[B1=A2]"))

      run("admit")

//      applyTactic(InlineTac("teleport"))
//
//      applyTactic(WpTac(left=true))
//      applyTactic(SimpTac)
//
//      applyTactic(WpTac(left=true))
//      applyTactic(SimpTac)
//
//      applyTactic(WpTac(left=true))
//      applyTactic(SimpTac)
//
//      applyTactic(WpTac(left=true))
//      applyTactic(SimpTac)
//
//      applyTactic(WpTac(left=true))
//      applyTactic(SimpTac)
//
//      applyTactic(WpTac(left=true))
//      applyTactic(SimpTac)
//
//      applyTactic(WpTac(left=true))
//      applyTactic(SimpTac)
//
//      applyTactic(SkipTac)
//      applyTactic(SimpTac)
////      applyTactic(TrueTac)

    } catch {
      case e : Throwable => e.printStackTrace()
    } finally {
      System.exit(0)
    }
  }
}
