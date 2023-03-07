package qrhl

import hashedcomputation.HashedValue
import qrhl.toplevel.{Parser, ParserContext}

import java.io.PrintWriter

trait Schema extends HashedValue {
  val name: String
  def parser(implicit context:ParserContext): Parser.Parser[SchemaInstantiation]
}

trait SchemaInstantiation extends HashedValue {
  def act(state: State, output: PrintWriter): State
}
