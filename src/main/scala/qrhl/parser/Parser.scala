package qrhl.parser

import info.hupel.isabelle.pure.{Typ => ITyp, Type => IType}
import qrhl.UserException
import qrhl.isabelle.Isabelle
import qrhl.logic._

import scala.util.parsing.combinator._

case class ParserContext(environment: Environment,
                          isabelle: Option[Isabelle.Context])

object Parser extends RegexParsers {

  val identifier : Parser[String] = """[a-zA-Z][a-zA-Z0-9_']*""".r
  val identifierListSep : Parser[String] = ","
  val identifierList : Parser[List[String]] = rep1sep(identifier,identifierListSep)

//  val natural : Parser[BigInt] = """[0-9]+""".r ^^ { BigInt(_) }

  private val statementSeparator = literal(";")
  def expression(typ:Typ)(implicit context:ParserContext) : Parser[Expression] =
    rep1 (elem("expression",{c => c!=';'})) ^^ { str:List[_] => context.isabelle match {
      case None => throw UserException("""Need isabelle command first. Try "isabelle <path>." or "isabelle auto." or "isabelle none."""")
      case Some(isabelle) => Expression(isabelle, str.mkString.trim, typ)
    } }

  private val assignSymbol = literal("<-")
  def assign(implicit context:ParserContext) : Parser[Assign] =
    for (v <- identifier;
         _ <- assignSymbol;
         // TODO: add a cut
         typ = context.environment.cVariables(v).typ;
         e <- expression(typ))
     yield Assign(context.environment.cVariables(v), e)

  private val sampleSymbol = literal("<$")
  def sample(implicit context:ParserContext) : Parser[Sample] =
    for (v <- identifier;
         _ <- sampleSymbol;
         // TODO: add a cut
         typ = context.environment.cVariables(v).typ;
         e <- expression(Typ.typeCon("QRHL.distr",typ)))
      yield Sample(context.environment.cVariables(v), e)

  def call(implicit context:ParserContext) : Parser[Call] =
    literal("call") ~! identifier ^^ { case _ ~ name =>
      if (!context.environment.programs.contains(name))
      throw UserException(s"""Program $name not defined (in "call $name").""")
      Call(name)
    }

  private val qInitSymbol = literal("<q")
  def qInit(implicit context:ParserContext) : Parser[QInit] =
    for (vs <- identifierList;
         _ <- qInitSymbol;
    // TODO: add a cut
         _ = assert(vs.nonEmpty);
         qvs = vs.map { context.environment.qVariables(_) };
         typ = Typ(context.isabelle.get, IType("QRHL.state",List(Isabelle.tupleT(qvs.map(_.typ.isabelleTyp):_*))));
         e <- expression(typ))
      yield QInit(qvs,e)

  def statement(implicit context:ParserContext) : Parser[Statement] = assign | sample | call | qInit

  def statementWithSep(implicit context:ParserContext) : Parser[Statement] = statement ~ statementSeparator ^^ { case s ~ _ => s }

  def skip : Parser[Block] = "skip" ~! statementSeparator ^^ { _ => Block.empty }

  def block(implicit context:ParserContext) : Parser[Block] =
    (statementSeparator ^^ { _ => Block.empty }) |
      (rep1(statementWithSep) ^^ { s => Block(s:_*) }) |
        skip
}
