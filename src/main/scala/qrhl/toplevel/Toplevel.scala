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

  /** Returns null on EOF */
  private def readCommand(): String = {
    val str = new StringBuilder()
    var first = true
    while (true) {
      //      val line = StdIn.readLine("qrhl> ")
      val line =
        try {
//          lineReader.readLine(if (first) "\nqrhl> " else "\n...> ")
          StdIn.readLine(if (first) "\nqrhl> " else "\n...> ")
        } catch {
          case _: org.jline.reader.EndOfFileException =>
            null;
          case _: org.jline.reader.UserInterruptException =>
            println("Aborted.")
            sys.exit(1)
        }

      if (line==null) {
        val str2 = str.toString()
        if (str2.trim == "") return null
        return str2
      }

      str.append(line).append('\n')

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
        if (cmdStr==null) { println("EOF"); sys.exit() }
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
        case e : AssertionError =>
          println("[ERROR]")
          e.printStackTrace()
      }
    }
  }
}
