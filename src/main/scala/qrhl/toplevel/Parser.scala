package qrhl.toplevel

import info.hupel.isabelle.pure
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.logic._
import qrhl.tactic._
import java.nio.file.{Path, Paths}

import scala.util.parsing.combinator._

case class ParserContext(environment: Environment,
                         isabelle: Option[Isabelle.Context])

object Parser extends JavaTokenParsers {

  val identifier : Parser[String] = """[a-zA-Z][a-zA-Z0-9_']*""".r
  val identifierListSep : Parser[String] = ","
  val identifierList : Parser[List[String]] = rep1sep(identifier,identifierListSep)

  //  val natural : Parser[BigInt] = """[0-9]+""".r ^^ { BigInt(_) }
  val natural: Parser[Int] = """[0-9]+""".r ^^ { _.toInt }

  val noIsabelleError: String = """Need isabelle command first. Try "isabelle." or "isabelle <theory name>."""""

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

  def expression(typ:pure.Typ)(implicit context:ParserContext) : Parser[RichTerm] =
//    rep1 (elem("expression",{c => c!=';'})) ^^ { str:List[_] => context.isabelle match {
    scanInnerSyntax ^^ { str:String => context.isabelle match {
      case None => throw UserException(noIsabelleError)
      case Some(isa) =>
        val e = RichTerm(isa, str  /*str.mkString.trim*/, typ)
        for (v <- e.variables)
          if (!context.environment.variableExists(v))
            throw UserException(s"Variable $v was not declared (in expression $str")
        e
    } }

  private val assignSymbol = literal("<-")
  def assign(implicit context:ParserContext) : Parser[Assign] =
    for (v <- identifier;
         _ <- assignSymbol;
         // TODO: add a cut
         typ = context.environment.getCVariable(v).valueTyp;
         e <- expression(typ);
         _ <- statementSeparator)
     yield Assign(context.environment.getCVariable(v), e)

  private val sampleSymbol = literal("<$")
  def sample(implicit context:ParserContext) : Parser[Sample] =
    for (v <- identifier;
         _ <- sampleSymbol;
         // TODO: add a cut
         typ = context.environment.getCVariable(v).valueTyp;
         e <- expression(Isabelle.distrT(typ));
         _ <- statementSeparator)
      yield Sample(context.environment.getCVariable(v), e)

  def programExp(implicit context:ParserContext) : Parser[Call] = identifier ~
    (literal("(") ~ rep1sep(programExp,identifierListSep) ~ ")").? ^^ {
    case name ~ args =>
      val args2 = args match { case None => Nil; case Some(_ ~ a ~ _) => a }
      context.environment.programs.get(name) match {
        case None => throw UserException(s"""Program $name not defined (in call-statement).""")
        case Some(decl) =>
          if (decl.numOracles!=args2.length)
            throw UserException(s"""Program $name expects ${decl.numOracles} oracles (in call-statement)""")
      }
      Call(name,args2 : _*)
  }

  def call(implicit context:ParserContext) : Parser[Call] =
    literal("call") ~! programExp ~ statementSeparator ^^ { case _ ~ call ~ _ => call }

  private val qInitSymbol = literal("<q")
  def qInit(implicit context:ParserContext) : Parser[QInit] =
    for (vs <- identifierList;
         _ <- qInitSymbol;
    // TODO: add a cut
         _ = assert(vs.nonEmpty);
         _ = assert(vs.distinct.length==vs.length); // checks if all vs are distinct
         qvs = vs.map { context.environment.getQVariable };
         typ = Isabelle.vectorT(Isabelle.tupleT(qvs.map(_.valueTyp):_*));
         e <- expression(typ);
         _ <- statementSeparator)
      yield QInit(qvs,e)

  def qApply(implicit context:ParserContext) : Parser[QApply] =
      for (_ <- literal("on");
           vs <- identifierList;
           _ <- literal("apply");
           _ = assert(vs.nonEmpty);
           _ = assert(vs.distinct.length==vs.length); // checks if all vs are distinct
           qvs = vs.map { context.environment.getQVariable };
           typ = Isabelle.boundedT(Isabelle.tupleT(qvs.map(_.valueTyp):_*));
           e <- expression(typ);
           _ <- statementSeparator)
        yield QApply(qvs,e)

  val measureSymbol : Parser[String] = assignSymbol
  def measure(implicit context:ParserContext) : Parser[Measurement] =
    for (res <- identifier;
         _ <- measureSymbol;
         _ <- literal("measure");
         vs <- identifierList;
         resv = context.environment.getCVariable(res);
         qvs = vs.map { context.environment.getQVariable };
         _ <- literal("with");
         etyp = Isabelle.measurementT(resv.valueTyp, Isabelle.tupleT(qvs.map(_.valueTyp):_*));
         e <- expression(etyp);
         _ <- statementSeparator)
      yield Measurement(resv,qvs,e)

  def ifThenElse(implicit context:ParserContext) : Parser[IfThenElse] =
    for (_ <- literal("if");
         _ <- literal("(");
         e <- expression(Isabelle.boolT);
         _ <- literal(")");
         _ <- literal("then");
         thenBranch <- statementOrParenBlock; // TODO: allow nested block
         _ <- literal("else");
         elseBranch <- statementOrParenBlock)  // TODO: allow nested block
      yield IfThenElse(e,thenBranch,elseBranch)

  def whileLoop(implicit context:ParserContext) : Parser[While] =
    for (_ <- literal("while");
         _ <- literal("(");
         e <- expression(Isabelle.boolT);
         _ <- literal(")");
         body <- statementOrParenBlock)
      yield While(e,body)

  def statement(implicit context:ParserContext) : Parser[Statement] = measure | assign | sample | call | qInit | qApply | ifThenElse | whileLoop

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

  // TODO does not match strings like "xxx\"xxx" or "xxx\\xxx" properly
  val quotedString : Parser[String] = stringLiteral ^^ { s:String =>
    val result = new StringBuilder()
    val iterator = s.substring(1,s.length-1).iterator
    for (c <- iterator)
      if (c=='\\') result.append(iterator.next())
      else result.append(c)
    result.toString()
  }

  val unquotedStringNoComma : Parser[String] = "[^.,]+".r

//  val commandEndSymbol : Parser[_] = literal(".")
  val isabelle : Parser[IsabelleCommand] =
    literal("isabelle") ~> identifier.? ^^ IsabelleCommand

  def typ(implicit context:ParserContext) : Parser[pure.Typ] =
  //    rep1 (elem("expression",{c => c!=';'})) ^^ { str:List[_] => context.isabelle match {
    scanInnerSyntax ^^ { str:String => context.isabelle match {
      case None => throw UserException(noIsabelleError)
      case Some(isa) => isa.readTypUnicode(str)
    } }

  def variableKind : Parser[String] = "classical|quantum|ambient".r
  //noinspection RedundantDefaultArgument
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

  private def declareAdversaryCalls: Parser[Int] = (literal("calls") ~ rep1sep(literal("?"),identifierListSep)).? ^^ {
    case None => 0
    case Some(_ ~ progs) => progs.length
  }

  def declareAdversary(implicit context:ParserContext) : Parser[DeclareAdversaryCommand] =
    literal("adversary") ~> OnceParser(identifier ~ literal("vars") ~ identifierList ~ declareAdversaryCalls) ^^ {
      case name ~ _ ~ vars ~ calls =>
        for (v <- vars) if (!context.environment.cVariables.contains(v) && !context.environment.qVariables.contains(v))
          throw UserException(s"Not a program variable: $v")
        val cvars = vars.flatMap(context.environment.cVariables.get)
        val qvars = vars.flatMap(context.environment.qVariables.get)
        DeclareAdversaryCommand(name,cvars,qvars,calls)
    }

  def goal(implicit context:ParserContext) : Parser[GoalCommand] =
    literal("lemma") ~> OnceParser((identifier <~ ":").? ~ expression(Isabelle.boolT)) ^^ {
      case name ~ e => GoalCommand(name.getOrElse(""), AmbientSubgoal(e)) }

  def qrhl(implicit context:ParserContext) : Parser[GoalCommand] =
  literal("qrhl") ~> OnceParser(for (
    _ <- literal("{");
    pre <- expression(Isabelle.predicateT);
    _ <- literal("}");
    left <- block;
    _ <- literal("~");
    right <- block;
    _ <- literal("{");
    post <- expression(Isabelle.predicateT);
    _ <- literal("}")
  ) yield GoalCommand("",QRHLSubgoal(left,right,pre,post,Nil)))

  val tactic_wp: Parser[WpTac] =
    literal("wp") ~> {
      (literal("left") ~> natural.? ^^ { n => WpTac(left = n.getOrElse(1), right = 0) }) |
        (literal("right") ~> natural.? ^^ { n => WpTac(right = n.getOrElse(1), left = 0) }) |
        (natural ~ natural ^^ { case l ~ r => WpTac(left = l, right = r) })
    }
  OnceParser("left|right".r) ^^ {
      case "left" => WpTac(left=1,right=0)
      case "right" => WpTac(left=0,right=1)
    }

  val tactic_swap: Parser[SwapTac] =
    literal("swap") ~> OnceParser("left|right".r ~ natural.?) ^^ {
      case "left" ~ n => SwapTac(left=true, n.getOrElse(1))
      case "right" ~ n => SwapTac(left=false, n.getOrElse(1))
      case _ ~ _ => throw new InternalError("Should not occur")
    }

  val tactic_inline: Parser[InlineTac] =
    literal("inline") ~> identifier ^^ InlineTac

  def tactic_seq(implicit context:ParserContext): Parser[SeqTac] =
    literal("seq") ~> OnceParser(for (
      left <- natural;
      right <- natural;
      _ <- literal(":");
      inner <- expression(Isabelle.predicateT))
      yield SeqTac(left,right,inner))

  def tactic_conseq(implicit context:ParserContext): Parser[ConseqTac] =
    literal("conseq") ~> OnceParser("pre|post".r ~ literal(":") ~ expression(Isabelle.predicateT)) ^^ {
      case "pre" ~ _ ~ e => ConseqTac(pre=Some(e))
      case "post" ~ _ ~ e => ConseqTac(post=Some(e))
    }

  def tactic_equal(implicit context:ParserContext) : Parser[EqualTac] =
    literal("equal") ~> (literal("exclude") ~> identifierList).? ^^ {
      case None => EqualTac(Nil)
      case Some(ps) =>
        for (p <- ps if !context.environment.programs.contains(p))
          throw UserException(s"Undeclared program $p")
        EqualTac(ps)
    }

  def tactic_rnd(implicit context:ParserContext): Parser[RndTac] =
    literal("rnd") ~> (for (
      x <- identifier;
      xVar = context.environment.getCVariable(x);
      _ <- literal(",");
      y <- identifier;
      yVar = context.environment.getCVariable(y);
      _ <- sampleSymbol | assignSymbol;
      e <- expression(Isabelle.distrT(Isabelle.prodT(xVar.valueTyp,yVar.valueTyp)))
    ) yield (xVar,yVar,e)).? ^^ RndTac

  def tactic_case(implicit context:ParserContext): Parser[CaseTac] =
    literal("case") ~> OnceParser(for (
      x <- identifier;
      xT = context.environment.getAmbientVariable(x);
      _ <- literal(":=");
      e <- expression(xT)
    ) yield CaseTac(x,e))

  val tactic_simp : Parser[SimpTac] =
    literal("simp") ~> OnceParser(literal("!").? ~ rep(identifier)) ^^ {
      case None ~ lemmas => SimpTac(lemmas)
      case Some(_) ~ lemmas => SimpTac(lemmas, force = true)
    }

  val tactic_rule : Parser[RuleTac] =
    literal("rule") ~> OnceParser(identifier) ^^ RuleTac.apply

  val tactic_clear : Parser[ClearTac] =
    literal("clear") ~> OnceParser(natural) ^^ ClearTac.apply

  def tactic_split(implicit context:ParserContext) : Parser[CaseSplitTac] =
    literal("casesplit") ~> OnceParser(expression(Isabelle.boolT)) ^^ CaseSplitTac

  def tactic_fix : Parser[FixTac] =
    literal("fix") ~> identifier ^^ FixTac

  def tactic(implicit context:ParserContext): Parser[Tactic] =
    literal("admit") ^^ { _ => Admit } |
      tactic_wp |
      tactic_swap |
      tactic_simp |
      tactic_rule |
      tactic_clear |
      literal("skip") ^^ { _ => SkipTac } |
//      literal("true") ^^ { _ => TrueTac } |
      tactic_inline |
      tactic_seq |
      tactic_conseq |
      literal("call") ^^ { _ => ErrorTac("Call tactic was renamed. Use \"equal\" instead.") } |
      tactic_equal |
      tactic_rnd |
      literal("byqrhl") ^^ { _ => ByQRHLTac } |
      tactic_split |
      tactic_case |
      tactic_fix |
      literal("measure") ^^ { _ => JointMeasureTac }

  val undo: Parser[UndoCommand] = literal("undo") ~> natural ^^ UndoCommand

  val qed : Parser[QedCommand] = "qed" ^^ { _ => QedCommand() }

//  val quit: Parser[QuitCommand] = "quit" ^^ { _ => QuitCommand() }

  val debug : Parser[DebugCommand] = "debug:" ~>
    ("goal" ^^ { _ => DebugCommand.goals((context,goals) => for (g <- goals) println(g.toTerm(context))) })

  val changeDirectory : Parser[ChangeDirectoryCommand] = literal("changeDirectory") ~> quotedString ^^ ChangeDirectoryCommand.apply

  val cheat : Parser[CheatCommand] =
    ("cheat:file" ^^ {_ => CheatCommand(file=true)}) |
      ("cheat:proof" ^^ {_ => CheatCommand(proof=true)}) |
      ("cheat:stop" ^^ {_ => CheatCommand(stop=true)}) |
      ("cheat" ^^ {_ => CheatCommand()})

  val include : Parser[IncludeCommand] =
    "include" ~> quotedString ^^ IncludeCommand.apply

  def command(implicit context:ParserContext): Parser[Command] =
    (debug | isabelle | variable | declareProgram | declareAdversary | qrhl | goal | (tactic ^^ TacticCommand) |
      include | undo | qed | changeDirectory | cheat).named("command")
}
