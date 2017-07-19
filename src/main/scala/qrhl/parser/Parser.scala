package qrhl.parser

import info.hupel.isabelle.pure.{Typ => ITyp, Type => IType}
import qrhl.UserException
import qrhl.isabelle.Isabelle
import qrhl.logic._

import scala.util.parsing.combinator._

case class ParserContext(environment: Environment,
                          isabelle: Option[Isabelle.Context],
                        boolT: Typ)

object Parser extends RegexParsers {

  val identifier : Parser[String] = """[a-zA-Z][a-zA-Z0-9_']*""".r
  val identifierListSep : Parser[String] = ","
  val identifierList : Parser[List[String]] = rep1sep(identifier,identifierListSep)

//  val natural : Parser[BigInt] = """[0-9]+""".r ^^ { BigInt(_) }

  private val statementSeparator = literal(";")
  // TODO expression should stop at ) as well

  def repWithState[S](p : S => Parser[S], start : S) : Parser[S] =
    p(start).?.flatMap { case Some(s) => repWithState(p,s); case None => success(start) }

  val scanExpression : Parser[String] = repWithState[(Int,List[Char])]({
    case (0, chars) =>
      elem("expression", { c => c != ';' && c != ')' }) ^^ { c =>
        val cs = c :: chars
        val lvl = if (c == '(') 1 else 0
        (lvl, cs)
      }
    case (level, chars) =>
      elem("expression", { _ => true }) ^^ { c =>
        assert(level > 0)
        val cs = c :: chars
        val lvl = if (c == '(') level + 1 else if (c == ')') level - 1 else level
        (lvl, cs)
      }
  }, (0,Nil)) ^^ { case (_,chars) => chars.reverse.mkString.trim }

  def expression(typ:Typ)(implicit context:ParserContext) : Parser[Expression] =
//    rep1 (elem("expression",{c => c!=';'})) ^^ { str:List[_] => context.isabelle match {
    scanExpression ^^ { str:String => context.isabelle match {
      case None => throw UserException("""Need isabelle command first. Try "isabelle <path>." or "isabelle auto." or "isabelle none."""")
      case Some(isabelle) => Expression(isabelle, str  /*str.mkString.trim*/, typ)
    } }

  private val assignSymbol = literal("<-")
  def assign(implicit context:ParserContext) : Parser[Assign] =
    for (v <- identifier;
         _ <- assignSymbol;
         // TODO: add a cut
         typ = context.environment.cVariables(v).typ;
         e <- expression(typ);
         _ <- statementSeparator)
     yield Assign(context.environment.cVariables(v), e)

  private val sampleSymbol = literal("<$")
  def sample(implicit context:ParserContext) : Parser[Sample] =
    for (v <- identifier;
         _ <- sampleSymbol;
         // TODO: add a cut
         typ = context.environment.cVariables(v).typ;
         e <- expression(Typ.typeCon("QRHL.distr",typ));
         _ <- statementSeparator)
      yield Sample(context.environment.cVariables(v), e)

  def call(implicit context:ParserContext) : Parser[Call] =
    literal("call") ~! identifier <~ statementSeparator ^^ { case _ ~ name =>
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
    // TODO: check that all vars are distinct
         qvs = vs.map { context.environment.qVariables(_) };
         typ = Typ(context.isabelle.get, IType("QRHL.state",List(Isabelle.tupleT(qvs.map(_.typ.isabelleTyp):_*))));
         e <- expression(typ);
         _ <- statementSeparator)
      yield QInit(qvs,e)

  def qApply(implicit context:ParserContext) : Parser[QApply] =
      for (_ <- literal("on");
           vs <- identifierList;
           _ <- literal("apply");
           _ = assert(vs.nonEmpty);
           qvs = vs.map { context.environment.qVariables(_) };
           // TODO: check that all vars are distinct
           typ = Typ(context.isabelle.get, IType("QRHL.isometry",
             List(Isabelle.tupleT(qvs.map(_.typ.isabelleTyp):_*),
                  Isabelle.tupleT(qvs.map(_.typ.isabelleTyp):_*))));
           e <- expression(typ);
           _ <- statementSeparator)
        yield QApply(qvs,e)

  val measureSymbol : Parser[String] = assignSymbol
  def measure(implicit context:ParserContext) : Parser[Measurement] =
    for (res <- identifier;
         _ <- measureSymbol;
         _ <- literal("measure");
         vs <- identifierList;
         resv = context.environment.cVariables(res);
         qvs = vs.map { context.environment.qVariables(_) };
         _ <- literal("in");
         etyp = Typ(context.isabelle.get, IType("QRHL.measurement",
           List(resv.isabelleTyp, Isabelle.tupleT(qvs.map(_.typ.isabelleTyp):_*))
         ));
         e <- expression(etyp);
         _ <- statementSeparator)
      yield Measurement(resv,qvs,e)

  def ifThenElse(implicit context:ParserContext) : Parser[IfThenElse] =
    for (_ <- literal("if");
         _ <- literal("(");
         e <- expression(context.boolT);
         _ <- literal(")");
         _ <- literal("then");
         thenBranch <- statementOrParenBlock; // TODO: allow nested block
         _ <- literal("else");
         elseBranch <- statementOrParenBlock)  // TODO: allow nested block
      yield IfThenElse(e,thenBranch,elseBranch)

  def statement(implicit context:ParserContext) : Parser[Statement] = measure | assign | sample | call | qInit | qApply | ifThenElse

//  def statementWithSep(implicit context:ParserContext) : Parser[Statement] = statement ~ statementSeparator ^^ { case s ~ _ => s }

  def skip : Parser[Block] = "skip" ~! statementSeparator ^^ { _ => Block.empty }

  def statementOrParenBlock(implicit context:ParserContext) : Parser[Block] =
    parenBlock | skip | (statement ^^ { s => Block(s) })

  def parenBlock(implicit context:ParserContext) : Parser[Block] =
    ("{" ~ "}" ^^ { _ => Block() }) |
    ("{" ~> block <~ "}")

  def block(implicit context:ParserContext) : Parser[Block] =
    (statementSeparator ^^ { _ => Block.empty }) |
      (rep1(statement) ^^ { s => Block(s:_*) }) |
      skip
}
