package qrhl.isabelle

import java.io.{BufferedReader, File, InputStreamReader}
import java.lang.RuntimeException
import java.nio.file.Paths

import info.hupel.isabelle.{Codec, Platform, Program, System, ml}
import info.hupel.isabelle.api.{Configuration, Version}
import info.hupel.isabelle.ml.Expr
import info.hupel.isabelle.pure.{Abs, App, Bound, Const, Free, Term, Theory, Var, Context => IContext, Typ => ITyp, Type => IType}
import info.hupel.isabelle.setup.{Resources, Setup}
import monix.execution.Scheduler.Implicits.global

import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scala.util.matching.Regex

class Isabelle(path:String) {
  val version = Version.Stable("2016-1")

  private val setup = {
    if (path=="auto")
      Setup.default(version).right.get
    else
//      Setup.detect(Platform.genericPlatform(new File(path).toPath), version).right.get
      Setup(Paths.get(path), Platform.guess.get, version)
  }

  private val resources = Resources.dumpIsabelleResources().right.get

  private val environment : info.hupel.isabelle.api.Environment = {
    if (path=="auto") println("Downloading Isabelle if needed (may take a while)")
    Await.result(setup.makeEnvironment(resources), Duration.Inf)
  }

  private val config : Configuration = Configuration.simple("QRHL")

  private def build() {
    println("Building Isabelle (may take a while)")
    if (!System.build(environment,config))
      throw qrhl.UserException("Building Isabelle failed")
  }

  private val system = { build(); Await.result(System.create(environment,config), Duration.Inf) }


  private val readTypeExpr: ml.Expr[IContext => String => ITyp] =
    ml.Expr.uncheckedLiteral("(fn ctxt => (Syntax.read_typ ctxt))")

  private def printTypExpr(t:ITyp): ml.Expr[IContext => String] =
    ml.Expr.uncheckedLiteral[ITyp => IContext => String]("(fn T => fn ctxt => YXML.content_of (Syntax.string_of_typ ctxt T))")(t)

  private val parseTermExpr: ml.Expr[IContext => String => Term] =
    ml.Expr.uncheckedLiteral("(fn ctxt => (Syntax.parse_term ctxt))")

  private val checkTermExpr: ml.Expr[IContext => Term => Term] =
    ml.Expr.uncheckedLiteral("(fn ctxt => (Syntax.check_term ctxt))")

  private def declareVariableExpr(name:String, typ: ITyp) : ml.Expr[IContext => IContext] = {
    val lit = ml.Expr.uncheckedLiteral[String => ITyp => IContext => IContext](
      """
      (fn name => fn T => fn ctx =>
         let val ([v],ctx') = Proof_Context.add_fixes [(Binding.name name, SOME T, NoSyn)] ctx
             val _ = if v<>name then error("variable v already declared") else ()
        in ctx' end)
      """)
    val eval1 = lit(name)
    val eval2 = eval1(typ)
    eval2
  }


  private def runProg[A](prog:Program[A],thyName:String) : A = Await.result(system.run(prog, thyName), Duration.Inf)
  private def runExpr[A](expr:ml.Expr[A],thyName:String)(implicit codec:Codec[A]) : A = runProg(expr.toProg,thyName)

  private def unitConv[A]: Expr[A => Unit] = ml.Expr.uncheckedLiteral("(fn _ => ())")
  private def getRef[A : ml.Opaque](expr:ml.Expr[A], thyName:String) : ml.Ref[A] = runProg(expr.rawPeek[Unit](unitConv), thyName)._1

  def getContext(thyName : String) =
    new Isabelle.Context(this, thyName, getRef(Isabelle.configureContext(IContext.initGlobal(Theory.get(thyName))),thyName))

}

object Isabelle {
  def tupleT(typs: ITyp*): ITyp = typs match {
    case Nil => IType("Product_Type.unit", Nil) // Unit
    case List(typ) => typ
    case (typ :: rest) => IType("Product_Type.prod", List(typ,tupleT(rest :_*)))
  }

  def freeVars(term: Term): Set[String] = {
    val fv = new mutable.SetBuilder[String,Set[String]](Set.empty)
    def collect(t:Term) : Unit = t match {
      case Free(v,_) => fv += v
      case Const(_,_) | Bound(_) | Var(_,_) =>
      case App(t1,t2) => collect(t1); collect(t2)
      case Abs(_,_,body) => collect(body)
    }
    collect(term)
    fv.result
  }

  private val configureContext: ml.Expr[IContext => IContext] =
    ml.Expr.uncheckedLiteral("(fn ctx => ctx (*|> Config.put show_types true |> Config.put show_sorts true*) )")
  private def simplifyTerm(term: Term) : ml.Expr[IContext => Term] = {
    val lit = ml.Expr.uncheckedLiteral[Term => IContext => Term](
      """
      (fn t => fn ctx =>
       let val ct = Thm.cterm_of ctx t
           val ct_eq = Simplifier.rewrite ctx ct |> Thm.prop_of
           val (lhs,rhs) = Logic.dest_equals ct_eq
           val _ = if lhs<>t then raise TERM("conversion returned wrong lhs\n",[t,lhs,rhs]) else ()
       in
         rhs
       end)
      """)
    lit(term)
  }

  def absfree(varName: String, varTyp: ITyp, term: Term) : ml.Expr[Term] = {
    val lit = ml.Expr.uncheckedLiteral[String => ITyp => Term => Term](
      "(fn name => fn T => fn t => Term.absfree (name,T) t)")
    val eval1 = lit(varName)
    val eval2 = eval1(varTyp)
    eval2(term)
  }

  val (symbols,symbolsInv) = {
    import scala.collection.JavaConverters._

    val lineRegex = """^\\<([a-zA-Z0-9^_]+)>\s+code:\s+0x([0-9a-fA-F]+)\b.*""".r
    val reader = new BufferedReader(new InputStreamReader(this.getClass.getResource("symbols").openStream()))
    val results = new ListBuffer[(String,Int)]
    for (line <- reader.lines().iterator.asScala) {
//      println(line)
      line match {
        case lineRegex(name,codepoint) => results.append((name,Integer.parseInt(codepoint, 16)))
        case _ => assert(!line.startsWith("\\")) // Lines with \ at the beginning should be matched by lineRegex
      }
    }
    reader.close()
//    println(results map { case (n,i) => new String(Character.toChars(i))+" " } mkString)
    val symbols = Map(results : _*)
    val symbolsInv = Map(results map { case (n,i) => (i,n) } : _*)
    (symbols, symbolsInv)
  }

  private val symbolRegex = """\\<([a-zA-Z0-9^_]+)>""".r
  def symbolsToUnicode(str:String) : String = symbolRegex.replaceAllIn(str,
    { m:Regex.Match => symbols.get(m.group(1)) match {
      case Some(i) => new String(Character.toChars(i))
      case None => m.matched
    }})

  // following https://stackoverflow.com/a/1527891/2646248
  private def codepoints(str:String) : Seq[Int] = {
    val len = str.length
    val result = new ArrayBuffer[Int](len)
    var offset = 0
    while (offset < len) {
      val cp = str.codePointAt(offset)
      result.append(cp)
      offset += Character.charCount(cp)
    }
    result
  }

  def unicodeToSymbols(str:String) : String = {
    val sb = new StringBuffer(str.length() * 11 / 10)
    for (cp <- codepoints(str)) {
      if (cp <= 128) sb.append(cp.toChar)
      else symbolsInv.get(cp) match {
        case Some(sym) => sb.append("\\<"); sb.append(sym); sb.append('>')
        case None => sb.appendCodePoint(cp)
      }
    }
    sb.toString
  }



  class Context private[Isabelle](isabelle:Isabelle, thyName: String, context:ml.Ref[IContext]) {

    override protected def finalize(): Unit = {
      println(s"Deleting context ${context.id}")
      isabelle.runExpr(context.delete, thyName)
      super.finalize()
    }

    def declareVariable(name: String, isabelleTyp: ITyp): Context = {
//      val newICtxt = isabelle.declareVariableExpr(name, isabelleTyp)(context)
//      new Context(isabelle,thyName,newICtxt)
      map(isabelle.declareVariableExpr(name, isabelleTyp))
    }

    def map(expr:ml.Expr[IContext => IContext]): Context = {
      val newICtxt = isabelle.getRef(expr(context.read), thyName)
      new Context(isabelle,thyName,newICtxt)
    }

    def runExpr[A](expr:ml.Expr[A])(implicit codec:Codec[A]) : A = isabelle.runExpr(expr,thyName)

    def readTerm(str:String, typ:ITyp): Term = {
      val parsedTerm = runExpr(isabelle.parseTermExpr(context.read)(str))
      val constrainedTerm = parsedTerm.constrain(typ)
      runExpr(isabelle.checkTermExpr(context.read)(constrainedTerm))
    }
    def prettyExpression(term:Term): String = runExpr(term.print(context.read))
    def readTyp(str:String) : ITyp = runExpr(isabelle.readTypeExpr(context.read)(str))
    def prettyTyp(typ:ITyp): String = runExpr(isabelle.printTypExpr(typ)(context.read))
    def simplify(term: Term) : Term = runExpr(Isabelle.simplifyTerm(term)(context.read))
  }
}
