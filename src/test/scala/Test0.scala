import qrhl._
import qrhl.logic._
import qrhl.parser.{Parser, ParserContext}

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

  def loadIsabelle(path:String) : Unit = {
    println(s"Loading Isabelle at $path.")
    state = state.loadIsabelle(path)
  }

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

  def testSimple(): Unit = {
    import tactic._
    try {
      loadIsabelle("/opt/Isabelle2016-1")

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

      applyTactic(AssignTac(left = true))
      applyTactic(SimpTac)

      applyTactic(AssignTac(left = false))
      applyTactic(SimpTac)

      applyTactic(SampleTac(left = false))
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

  def main(args: Array[String]): Unit = {
    import tactic._
    try {
      loadIsabelle("/opt/Isabelle2016-1")

      declareVariable("a", "int")
      declareVariable("c", "int")
      declareVariable("A", "bit", quantum=true)
      declareVariable("B", "bit", quantum=true)
      declareVariable("C", "bit", quantum=true)

      declareProgram("teleport", "" +
        "A,B <q EPR;" +
        "on C,A apply CNOT;" +
        "on C apply H;" +
//        "a <- measure A in computational_basis;" +
//        "c <- measure B in computational_basis;" +
//        "if (a=1) then on B apply X;" +
//        "if (c=1) then on B apply Z;" +
        "")

      openGoal(QRHLSubgoal(
        "call teleport;",
        "skip;",
        "Qeq[A1=A2]",
        "Qeq[B1=A2]"))

      applyTactic(InlineTac("teleport"))

      applyTactic(QInitTac(left=true))

      applyTactic(AssignTac(left=true))
      applyTactic(SimpTac)

      applyTactic(AssignTac(left=false))
      applyTactic(SimpTac)

      applyTactic(SampleTac(left=false))
      applyTactic(SimpTac)

      applyTactic(SkipTac)
      applyTactic(SimpTac)
      applyTactic(TrueTac)
    } catch {
      case e : Throwable => e.printStackTrace()
    } finally {
      System.exit(0)
    }
  }
}
