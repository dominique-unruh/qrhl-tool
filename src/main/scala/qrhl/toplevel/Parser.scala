package qrhl.toplevel

import info.hupel.isabelle.pure.{Typ => ITyp, Type => IType}
import qrhl._
import qrhl.isabelle.Isabelle
import qrhl.logic._
import qrhl.tactic._

import scala.util.parsing.combinator._

case class ParserContext(environment: Environment,
                          isabelle: Option[Isabelle.Context],
                        boolT: Typ, assertionT: Typ)

object Parser extends RegexParsers {

  val identifier : Parser[String] = """[a-zA-Z][a-zA-Z0-9_']*""".r
  val identifierListSep : Parser[String] = ","
  val identifierList : Parser[List[String]] = rep1sep(identifier,identifierListSep)

  //  val natural : Parser[BigInt] = """[0-9]+""".r ^^ { BigInt(_) }
  val natural: Parser[Int] = """[0-9]+""".r ^^ { _.toInt }

  val noIsabelleError: String = """Need isabelle command first. Try "isabelle <path>." or "isabelle auto."""""

  private val statementSeparator = literal(";")

  def repWithState[S](p : S => Parser[S], start : S) : Parser[S] =
    p(start).?.flatMap { case Some(s) => repWithState(p,s); case None => success(start) }

  val scanInnerSyntax : Parser[String] = repWithState[(Int,List[Char])]({
    case (0, chars) =>
      elem("expression", { c => c != ';' && c != ')' && c != '}' }) ^^ { c =>
        val cs = c :: chars
        val lvl = if (c == '(' || c == '{') 1 else 0
        (lvl, cs)
      }
    case (level, chars) =>
      elem("expression", { _ => true }) ^^ { c =>
        assert(level > 0)
        val cs = c :: chars
        val lvl = if (c == '(' || c== '{') level + 1 else if (c == ')' || c=='}') level - 1 else level
        (lvl, cs)
      }
  }, (0,Nil)) ^^ { case (_,chars) => chars.reverse.mkString.trim }

  def expression(typ:Typ)(implicit context:ParserContext) : Parser[Expression] =
//    rep1 (elem("expression",{c => c!=';'})) ^^ { str:List[_] => context.isabelle match {
    scanInnerSyntax ^^ { str:String => context.isabelle match {
      case None => throw UserException(noIsabelleError)
      case Some(isa) => Expression(isa, str  /*str.mkString.trim*/, typ)
    } }

  private val assignSymbol = literal("<-")
  def assign(implicit context:ParserContext) : Parser[Assign] =
    for (v <- identifier;
         _ <- assignSymbol;
         // TODO: add a cut
         typ = context.environment.cVariables.
           getOrElse(v, throw UserException(s"Undefined variable $v")).typ;
         e <- expression(typ);
         _ <- statementSeparator)
     yield Assign(context.environment.cVariables(v), e)

  private val sampleSymbol = literal("<$")
  def sample(implicit context:ParserContext) : Parser[Sample] =
    for (v <- identifier;
         _ <- sampleSymbol;
         // TODO: add a cut
         typ = context.environment.cVariables.
           getOrElse(v, throw UserException(s"Undefined variable $v")).typ;
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

  val quotedString : Parser[String] = """"[^"]*"""".r ^^ { s => s.substring(1,s.length-1) }

  val unquotedStringNoComma : Parser[String] = "[^.,]+".r

//  val commandEndSymbol : Parser[_] = literal(".")
  val isabelle : Parser[IsabelleCommand] =
    literal("isabelle") ~> OnceParser(
      (quotedString | unquotedStringNoComma) ~ (literal(",") ~> literal("theory") ~> identifier).?
    ) ^^ {
      case path ~ None => IsabelleCommand(path)
      case path ~ Some(thy) => IsabelleCommand(path,Some(thy))
    }

  def typ(implicit context:ParserContext) : Parser[Typ] =
  //    rep1 (elem("expression",{c => c!=';'})) ^^ { str:List[_] => context.isabelle match {
    scanInnerSyntax ^^ { str:String => context.isabelle match {
      case None => throw UserException(noIsabelleError)
      case Some(isa) => Typ(isa, str)
    } }

  def variableKind : Parser[String] = "classical|quantum|ambient".r
  def variable(implicit context:ParserContext) : Parser[DeclareVariableCommand] =
    variableKind ~ OnceParser(literal("var") ~ identifier ~ literal(":") ~ typ) ^^ {
      case kind~(_~id~_~typ) => kind match {
        case "classical" => DeclareVariableCommand(id,typ,quantum=false)
        case "quantum" => DeclareVariableCommand(id,typ,quantum=true)
        case "ambient" => DeclareVariableCommand(id,typ,ambient=true)
      }
    }

//  def quantumVariable(implicit context:ParserContext) : Parser[DeclareVariableCommand] =
//    literal("quantum") ~> literal("var") ~> OnceParser(identifier ~ literal(":") ~ typ) ^^ { case id~_~typ =>
//      DeclareVariableCommand(id,typ,quantum=true)
//    }

  def declareProgram(implicit context:ParserContext) : Parser[DeclareProgramCommand] =
    literal("program") ~> OnceParser(identifier ~ literal(":=") ~ parenBlock) ^^ { case id~_~prog =>
      DeclareProgramCommand(id,prog)
    }

  def declareAdversary(implicit context:ParserContext) : Parser[DeclareAdversaryCommand] =
    literal("adversary") ~> OnceParser(identifier ~ literal("vars") ~ identifierList) ^^ {
      case name ~ _ ~ vars =>
        for (v <- vars) if (!context.environment.cVariables.contains(v) && !context.environment.qVariables.contains(v))
          throw UserException(s"Not a program variable: $v")
        val cvars = vars.flatMap(context.environment.cVariables.get)
        val qvars = vars.flatMap(context.environment.qVariables.get)
        DeclareAdversaryCommand(name,cvars,qvars)
    }

  def goal(implicit context:ParserContext) : Parser[GoalCommand] =
    literal("goal") ~> OnceParser((identifier <~ ":").? ~ expression(context.boolT)) ^^ {
      case name ~ e => GoalCommand(name.getOrElse(""), AmbientSubgoal(e)) }

  def qrhl(implicit context:ParserContext) : Parser[GoalCommand] =
  literal("qrhl") ~> OnceParser(for (
    _ <- literal("{");
    pre <- expression(context.assertionT);
    _ <- literal("}");
    left <- block;
    _ <- literal("~");
    right <- block;
    _ <- literal("{");
    post <- expression(context.assertionT);
    _ <- literal("}")
  ) yield GoalCommand("",QRHLSubgoal(left,right,pre,post,Nil)))

  val tactic_wp: Parser[WpTac] =
    literal("wp") ~> OnceParser("left|right".r) ^^ {
      case "left" => WpTac(left=true)
      case "right" => WpTac(left=false)
    }

  val tactic_swap: Parser[SwapTac] =
    literal("swap") ~> OnceParser("left|right".r) ^^ {
      case "left" => SwapTac(left=true)
      case "right" => SwapTac(left=false)
    }

  val tactic_inline: Parser[InlineTac] =
    literal("inline") ~> identifier ^^ InlineTac

  def tactic_seq(implicit context:ParserContext): Parser[SeqTac] =
    literal("seq") ~> OnceParser(for (
      left <- natural;
      right <- natural;
      _ <- literal(":");
      inner <- expression(context.assertionT))
      yield SeqTac(left,right,inner))

  def tactic_conseq(implicit context:ParserContext): Parser[ConseqTac] =
    literal("conseq") ~> OnceParser("pre|post".r ~ literal(":") ~ expression(context.assertionT)) ^^ {
      case "pre" ~ _ ~ e => ConseqTac(pre=Some(e))
      case "post" ~ _ ~ e => ConseqTac(post=Some(e))
    }

  def tactic_rnd(implicit context:ParserContext): Parser[RndTac] =
    literal("rnd") ~> (for (
      x <- identifier;
      xT = context.environment.cVariables(x).typ;
      _ <- literal(",");
      y <- identifier;
      yT = context.environment.cVariables(y).typ;
      _ <- sampleSymbol | assignSymbol;
      e <- expression((xT*yT).distr)
    ) yield e).? ^^ RndTac

  def tactic_case(implicit context:ParserContext): Parser[CaseTac] =
    literal("case") ~> OnceParser(for (
      x <- identifier;
      xT = context.environment.ambientVariables(x);
      _ <- literal(":=");
      e <- expression(xT)
    ) yield CaseTac(x,e))

  val tactic_simp : Parser[SimpTac] =
    literal("simp") ~> OnceParser(rep(identifier)) ^^ SimpTac.apply

  def tactic_split(implicit context:ParserContext) : Parser[CaseSplitTac] =
    literal("casesplit") ~> OnceParser(expression(context.boolT)) ^^ CaseSplitTac

  def tactic(implicit context:ParserContext): Parser[Tactic] =
    literal("admit") ^^ { _ => Admit } |
      tactic_wp |
      tactic_swap |
      tactic_simp |
      literal("skip") ^^ { _ => SkipTac } |
      literal("true") ^^ { _ => TrueTac } |
      tactic_inline |
      tactic_seq |
      tactic_conseq |
      literal("call") ^^ { _ => CallTac } |
      tactic_rnd |
      literal("byqrhl") ^^ { _ => ByQRHLTac } |
      tactic_split |
      tactic_case

  val undo: Parser[UndoCommand] = literal("undo") ~> natural ^^ UndoCommand

  val qed : Parser[QedCommand] = "qed" ^^ { _ => QedCommand() }

//  val quit: Parser[QuitCommand] = "quit" ^^ { _ => QuitCommand() }

  def command(implicit context:ParserContext): Parser[Command] =
    (isabelle | variable | declareProgram | declareAdversary | qrhl | goal | (tactic ^^ TacticCommand) | undo | qed).named("command")
}
