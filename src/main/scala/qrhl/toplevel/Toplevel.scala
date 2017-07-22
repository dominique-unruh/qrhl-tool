package qrhl.toplevel

import org.jline.reader.LineReaderBuilder
import org.jline.terminal.TerminalBuilder
import qrhl.{State, UserException}

import scala.collection.mutable
import scala.io.StdIn
import scala.util.matching.Regex


object Toplevel {
  private val commandEnd: Regex = """\.\s*$""".r

  private val terminal = TerminalBuilder.terminal()
  private val lineReader = LineReaderBuilder.builder().terminal(terminal).build()

  private def readCommand(): String = {
    val str = new StringBuilder()
    var first = true
    while (true) {
      //      val line = StdIn.readLine("qrhl> ")
      val line =
        try {
          lineReader.readLine(if (first) "qrhl> " else "...> ")
        } catch {
          case _: org.jline.reader.EndOfFileException =>
            sys.exit(0)
          case _: org.jline.reader.UserInterruptException =>
            println("Aborted.")
            sys.exit(1)
        }

      str.append(line).append('\n')

//      println(s"line [$line] ${commandEnd.regex}")

      if (commandEnd.findFirstIn(line).isDefined)
        return commandEnd.replaceAllIn(str.toString, "")
      first = false
    }

    "" // unreachable
  }

  def parseCommand(state:State, str:String): Command = {
    implicit val parserContext = state.parserContext
    Parser.parseAll(Parser.command,str) match {
      case Parser.Success(cmd2,_) => cmd2
      case res @ Parser.NoSuccess(msg, _) =>
        throw UserException(msg)
    }
  }

  def main(args: Array[String]): Unit = {
    val states : mutable.Stack[State] = new mutable.Stack()
    states.push(State.empty)
    while (true) {
      try {
        val cmdStr = readCommand()
        println("KKK")
//        println(s"cmd: [$cmdStr]")
        val cmd = parseCommand(states.top, cmdStr)
        cmd match {
          case UndoCommand(n) =>
            for (_ <- 1 to n) states.pop()
            println(states.top)
          case _ =>
            val newState = cmd.act(states.top)
            println(newState)
            states.push(newState)
        }
      } catch {
        case UserException(msg) =>
          println("[ERROR] "+msg)
        case e : Exception =>
          println("[ERROR] "+e)
        case e : AssertionError =>
          println("[ERROR] "+e)
      }
    }
  }
}
