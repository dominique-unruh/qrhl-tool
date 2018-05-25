package qrhl.isabelle

import java.io.{BufferedReader, IOException, InputStreamReader}
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{Files, Path, Paths}

import info.hupel.isabelle.api.{Configuration, Version}
import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.ml.Expr
import info.hupel.isabelle.pure.{Abs, App, Bound, Const, Free, Term, Type, Var, Context => IContext, Typ => ITyp}
import info.hupel.isabelle.setup.Setup.Absent
import info.hupel.isabelle.setup.{Resources, Setup}
import info.hupel.isabelle.{OfficialPlatform, Operation, Platform, System, ml}
import monix.execution.Scheduler.Implicits.global
import org.log4s
import qrhl.UserException
import qrhl.logic.{QVariable, Typ}

import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scala.util.matching.Regex
import scala.util.{Left, Right}

class Isabelle(path:String, build:Boolean=sys.env.contains("QRHL_FORCE_BUILD")) {
  val version = Version.Stable("2017")

  private val auto = path=="auto"

  /** The directory that contains the jar, or, if not loaded from a jar, the current directory. */
  private val localStoragePath = {
    val location = this.getClass.getProtectionDomain.getCodeSource.getLocation.toURI
    assert(location.getScheme=="file")
    val path = Paths.get(location)
    if (path.getFileName.toString.endsWith(".jar")) path.getParent.toAbsolutePath
    else Paths.get("").toAbsolutePath
  }.resolve("isabelle-temp")

  private val platform : Platform = Platform.guess match {
    case None if auto => throw UserException(""""isabelle auto" used, but cannot detect platform. Use "isabelle <path>" with an existing Isabelle install at <path> instead""")
    case None if !auto => Platform.genericPlatform(localStoragePath)
    case Some(p) => p.withLocalStorage(localStoragePath)
  }

  private val setup : Setup = {
    if (auto) {
      //      Setup.default(version,updateIfDevel = false).right.get
      assert(platform.isInstanceOf[OfficialPlatform])
      Setup.detect(platform, version, updateIfDevel=false) match {
        case Right(install) => install
        case Left(Absent) =>
          println(s"*** Downloading Isabelle into ${platform.localStorage}. May take a while...")
          Setup.install(platform.asInstanceOf[OfficialPlatform], version) match {
            case Right(install) => install
            case Left(reason) => throw UserException("Could not install Isabelle: "+reason.explain)
          }
        case Left(reason) => throw UserException("Could not setup Isabelle: "+reason.explain)
      }
    } else {
//      val platformPath = Paths.get("tmp-isabelle")
//      val platform = Platform.genericPlatform(platformPath)
//      Setup(Paths.get(path), Platform.guess.get, version)
      Setup(Paths.get(path), platform, version)
    }
  }

  private val resources = Resources.dumpIsabelleResources() match {
    case Left(error) => throw new IOException(error.explain)
    case Right(r) => r
  }

  private val environment: info.hupel.isabelle.api.Environment = {
//    if (path == "auto") println("Downloading Isabelle if needed (may take a while)")
    try {
      Await.result(setup.makeEnvironment(resources, Nil), Duration.Inf)
    } catch {
      case e: RuntimeException if e.getMessage.startsWith("Generic environment does not support unofficial platform") =>
        throw UserException("Bad Isabelle root directory (probably)")
    }
  }

  private val config: Configuration = Configuration.simple("QRHL")

  private def doBuild() {
    println("*** Building Isabelle (may take a while, especially the first time, e.g., 10-25min)...")
    if (!System.build(environment, config))
      throw qrhl.UserException("Building Isabelle failed")
  }

  private def checkBuilt() : Boolean = {
//    val location = this.getClass.getProtectionDomain.getCodeSource.getLocation.toURI
//    assert(location.getScheme=="file")
//    println("LOC "+Paths.get(location))
//    val comparedTo = Files.getLastModifiedTime(Paths.get(location))
//    println(comparedTo)
    try {
      val files = Files.find(environment.etc.getParent.resolve("heaps"), 10, { (path: Path, attr: BasicFileAttributes) =>
        path.endsWith("QRHL") && !path.getParent.endsWith("log")
//        path.endsWith("QRHL") && !path.endsWith("log")/*&& attr.lastModifiedTime().compareTo(comparedTo) > 0*/
      })
      files.findAny().isPresent
    } catch {
      case _ : IOException => false
    }
  }

  private val system = {
    if (build || !checkBuilt())
      doBuild()

    Await.result(System.create(environment, config), Duration.Inf)
  }


  private def unitConv[A]: Expr[A => Unit] = ml.Expr.uncheckedLiteral("(fn _ => ())")

  def invoke[I,O](op: Operation[I,O], arg: I) : O = Await.result(system.invoke(op)(arg), Duration.Inf).unsafeGet

  def getQRHLContextWithFiles(thys: String*) : Isabelle.Context = {
    getContextWithThys(List("QRHL.QRHL_Operations","QRHL.QRHL"), thys.toList)
  }


  private def getContextWithThys(thys: List[String], files: List[String]): Isabelle.Context = {
    invoke(Operation.UseThys, files)
    val imports = thys ::: files.map("Draft."+_)
    val ctxId = invoke(Isabelle.createContextOp, imports)
    new Isabelle.Context(this, ctxId)
  }

  private var disposed = false

  def dispose(): Unit = this.synchronized {
    if (!disposed) {
      Isabelle.logger.debug("Disposing Isabelle.")
      Await.result(system.dispose, Duration.Inf)
      Isabelle.logger.debug("Disposing Isabelle (done).")
      disposed = true
    }
  }

  override def finalize(): Unit = {
    dispose()
    super.finalize()
  }

  def runJEdit(files:Seq[String]=Nil): Unit = environment.exec("jedit",List("-l","QRHL") ++ files.toList)
}

object Isabelle {

  private val logger = log4s.getLogger
  def mk_conj(t1: Term, t2: Term) : Term = HOLogic.conj $ t1 $ t2
  def mk_conjs(terms: Term*): Term = terms match {
    case t :: ts => ts.foldLeft(t)(mk_conj)
    case Nil => HOLogic.True
  }
  def mk_list(typ:ITyp, terms: List[Term]): Term = {
    val lT = listT(typ)
    val cons = Const("List.list.Cons", typ -->: lT -->: lT)
    val nil = Const("List.list.Nil",lT)
    terms.foldRight[Term](nil)( cons $ _ $ _ )
  }



  val predicateT = Type("Complex_L2.subspace", List(Type("QRHL_Core.mem2",Nil)))
  val programT = Type("Encoding.program")
  val classical_subspace = Const("QRHL_Core.classical_subspace", HOLogic.boolT -->: predicateT)
  val predicate_inf = Const ("Lattices.inf_class.inf", predicateT -->: predicateT -->: predicateT)
  val predicate_bot = Const ("Orderings.bot_class.bot", predicateT)
  val predicate_0 = Const ("Groups.zero_class.zero", predicateT)
  def distrT(typ:ITyp): Type = Type("QRHL_Core.distr", List(typ))
  def boundedT(typ:ITyp): Type = boundedT(typ,typ)
  def boundedT(inT:ITyp, outT:ITyp) = Type("Bounded_Operators.bounded", List(inT,outT))
  def measurementT(resultT:ITyp, qT: ITyp) = Type("QRHL_Core.measurement", List(resultT, qT))
  def listT(typ:ITyp) : Type = Type("List.list", List(typ))
  val block = Const("Encoding.block", listT(programT) -->: programT)
  def vectorT(typ:ITyp) = Type("Complex_L2.vector", List(typ))
  def qvariableT(typ:ITyp) = Type("QRHL_Core.qvariable", List(typ))
  def dest_qvariableT(typ: ITyp): ITyp = typ match {
    case Type("QRHL_Core.qvariable", List(typ2)) => typ2
  }
  def qvariablesT(typ:ITyp) : Type = Type("QRHL_Core.qvariables", List(typ))
  def qvariablesT(typs:List[ITyp]) : Type = qvariablesT(tupleT(typs:_*))
  val cvariableT: ITyp => Type = qvariableT
  def expressionT(typ:ITyp) = Type("Encoding.expression", List(typ))
  val assignName = "Encoding.assign"
  def assign(typ:ITyp) : Const = Const(assignName, qvariableT(typ) -->: expressionT(typ) -->: programT)
  val sampleName = "Encoding.sample"
  def sample(typ:ITyp) : Const = Const(sampleName, qvariableT(typ) -->: expressionT(distrT(typ)) -->: programT)
  val ifthenelseName = "Encoding.ifthenelse"
  val ifthenelse = Const(ifthenelseName, expressionT(HOLogic.boolT) -->: listT(programT) -->: listT(programT) -->: programT)
  val whileName = "Encoding.while"
  val whileProg = Const(whileName, expressionT(HOLogic.boolT) -->: listT(programT) -->: programT)
  val metaImp = Const("Pure.imp", Type("prop") -->: Type("prop") -->: Type("prop"))
  val boolT: ITyp = HOLogic.boolT
  val qrhl = Const("Encoding.qrhl", expressionT(predicateT) -->: listT(programT) -->: listT(programT) -->: expressionT(predicateT) -->: boolT)
  val qinitName = "Encoding.qinit"
  def qinit(typ:ITyp) = Const(qinitName, qvariablesT(typ) -->: expressionT(vectorT(typ)) -->: programT)
  val qapplyName = "Encoding.qapply"
  def qapply(typ:ITyp) = Const(qapplyName, qvariablesT(typ) -->: expressionT(boundedT(typ)) -->: programT)
  val measurementName = "Encoding.measurement"
  def measurement(resultT:ITyp, qT:ITyp) = Const(measurementName, cvariableT(resultT) -->: qvariablesT(qT) -->: expressionT(measurementT(resultT,qT)) -->: programT)
  val unitT = Type("Product_Type.unit")
  def prodT(t1:ITyp, t2:ITyp) = Type("Product_Type.prod", List(t1,t2))
  private def qvarTuple_var0(qvs:List[QVariable]) : (Term,ITyp) = qvs match {
    case Nil => (qvariable_unit, unitT)
    case List(qv) => (qvariable_singleton(qv.typ.isabelleTyp) $ qv.isabelleTerm_var,
                      qv.typ.isabelleTyp)
    case qv::rest => {
      val (qvTuple, qvTyp) = qvarTuple_var0(List(qv))
      val (restTuple, restTyp) = qvarTuple_var0(rest)
      (qvariable_concat(qvTyp, restTyp) $ qvTuple $ restTuple,
       prodT(qvTyp, restTyp))
    }
  }
  def qvarTuple_var(qvs:List[QVariable]) : Term = qvarTuple_var0(qvs)._1
  val qvariable_unit = Const("QRHL_Core.qvariable_unit", qvariablesT(unitT))
  val qvariable_singletonName = "QRHL_Core.qvariable_singleton"
  def qvariable_singleton(typ:ITyp) = Const(qvariable_singletonName, qvariableT(typ) -->: qvariablesT(typ))
  val qvariable_concatName = "QRHL_Core.qvariable_concat"
  def qvariable_concat(t1:ITyp, t2:ITyp) = Const(qvariable_concatName, qvariablesT(t1) -->: qvariablesT(t2) -->: qvariablesT(prodT(t1,t2)))

  val checkTypeOp: Operation[(BigInt, Term), ITyp] = Operation.implicitly[(BigInt,Term), ITyp]("check_type")
  val createContextOp: Operation[List[String], BigInt] = Operation.implicitly[List[String],BigInt]("create_context")
  val deleteContextOp: Operation[BigInt, Unit] = Operation.implicitly[BigInt,Unit]("delete_context")
  val printTermOp: Operation[(BigInt, Term), String] = Operation.implicitly[(BigInt,Term),String]("print_term")
  val printTypOp: Operation[(BigInt, ITyp), String] = Operation.implicitly[(BigInt,ITyp),String]("print_typ")
  val addAssumptionOp: Operation[(String, Term, BigInt), BigInt] = Operation.implicitly[(String,Term,BigInt), BigInt]("add_assumption")
  val readTypOp: Operation[(BigInt, String), ITyp] = Operation.implicitly[(BigInt, String), ITyp]("read_typ")
  val readTermOp: Operation[(BigInt, String, ITyp), Term] = Operation.implicitly[(BigInt, String, ITyp), Term]("read_term")
  val simplifyTermOp: Operation[(Term, List[String], BigInt), Term] = Operation.implicitly[(Term,List[String],BigInt), Term]("simplify_term")
  val declareVariableOp: Operation[(BigInt, String, ITyp), BigInt] = Operation.implicitly[(BigInt,String,ITyp), BigInt]("declare_variable")

  def mk_eq(typ: ITyp, a: Term, b: Term): Term = Const("HOL.eq", typ -->: typ -->: HOLogic.boolT) $ a $ b

  /** Analogous to Isabelle's HOLogic.dest_list. Throws [[MatchError]] if it's not a list */
  def dest_list(term: Term): List[Term] = term match {
    case (Const("List.list.Nil", _)) => Nil
    case App(App(Const("List.list.Cons", _), t), u) => t :: dest_list(u)
    case _ => throw new MatchError(term)
  }

  /** Analogous to Isabelle's HOLogic.dest_numeral. Throws [[MatchError]] if it's not a numeral */
  def dest_numeral(term:Term) : BigInt = term match {
    case (Const("Num.num.One", _)) => 1
    case App(Const("Num.num.Bit0", _), bs) => 2 * dest_numeral(bs)
    case App(Const("Num.num.Bit1", _), bs) => 2 * dest_numeral(bs) + 1
    case _ => throw new MatchError(term)
  }

  /** Analogous to Isabelle's HOLogic.dest_char. Throws [[MatchError]] if it's not a char */
  def dest_char(term:Term) : Char = {
    val (typ, n) = term match {
      case Const("Groups.zero_class.zero", ty) => (ty, 0)
      case App(Const("String.Char", Type("fun", List(_, ty))), t) => (ty, dest_numeral(t).toInt)
      case _ => throw new MatchError(term)
    }
    if (typ == Type ("String.char", Nil)) n.toChar
    else throw new MatchError(term)
  }

  /** Analogous to Isabelle's HOLogic.dest_string. Throws [[MatchError]] if it's not a string */
  def dest_string(term:Term) : String =
    dest_list(term).map(dest_char).mkString

  def tupleT(typs: ITyp*): ITyp = typs match {
    case Nil => unitT
    case List(typ) => typ
    case (typ :: rest) => prodT(typ,tupleT(rest :_*))
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

//  private val configureContext: ml.Expr[IContext => IContext] =
//    ml.Expr.uncheckedLiteral("(fn ctx => ctx (*|> Config.put show_types true |> Config.put show_sorts true*) )")
  private def simplifyTerm(term: Term, facts:List[String]) : ml.Expr[IContext => Term] = {
    val lit = ml.Expr.uncheckedLiteral[Term => List[String] => IContext => Term]("QRHL.simp")
    lit(term)(implicitly)(facts)
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
        case None =>
          if (cp>255) throw UserException(f"""Character "${new String(Character.toChars(cp))}%s" (Ux$cp%04X) not supported by Isabelle""")
          sb.appendCodePoint(cp)
      }
    }
    sb.toString
  }

  private var _theContext : Context = _
  def theContext: Context = _theContext

  class Context private[Isabelle](val isabelle:Isabelle, val contextId: BigInt) {
    _theContext = this

    def checkType(term:Term) : ITyp = {
//      val lit = ml.Expr.uncheckedLiteral[IContext => Term => ITyp]("QRHL.checkType")
//      val mlExpr = lit(context.read)(term)
//      runExpr(mlExpr)
      isabelle.invoke(checkTypeOp, (contextId,term))
    }


    override protected def finalize(): Unit = {
      logger.debug(s"Deleting context $contextId")
      isabelle.invoke(deleteContextOp,contextId)
//      isabelle.runExpr(context.delete, thyName)
      super.finalize()
    }

    def declareVariable(name: String, isabelleTyp: ITyp): Context = {
//      val newICtxt = isabelle.declareVariableExpr(name, isabelleTyp)(context)
//      new Context(isabelle,thyName,newICtxt)
//      map(isabelle.declareVariableExpr(name, isabelleTyp))
      val id = isabelle.invoke(declareVariableOp, (contextId, name, isabelleTyp))
      new Context(isabelle,id)
    }

    def addAssumption(name: String, assumption: Term): Context = {
//      val lit = ml.Expr.uncheckedLiteral[String => Term => IContext => IContext]("QRHL.addAssumption")
//      map(lit(name)(implicitly)(assumption))
      val id = isabelle.invoke(addAssumptionOp, (name,assumption,contextId))
      new Context(isabelle,id)
    }

//    @deprecated("use operations", "now")
//    def map(expr:ml.Expr[IContext => IContext]): Context = {
//      val newICtxt = isabelle.getRef(expr(Ref[IContext](contextId).read), thyName)
//      new Context(isabelle,thyName,newICtxt.id)
//    }

    def map(f:BigInt => BigInt) : Context =
      new Context(isabelle,f(contextId))

//    @deprecated("use operations", "now")
//    val context: Ref[IContext] = Ref[IContext](contextId)

//    @deprecated("use operations", "now")
//    def runExpr[A](expr:ml.Expr[A])(implicit codec:Codec[A]) : A = isabelle.runExpr(expr,thyName)

    def readTerm(str:String, typ:ITyp): Term = {
      isabelle.invoke(readTermOp, (contextId,str,typ))
    }
//    def readTerm(str:String, typ:ITyp): Term = {
//      val parsedTerm = runExpr(isabelle.parseTermExpr(Ref[IContext](contextId).read)(str))
//      val constrainedTerm = parsedTerm.constrain(typ)
//      runExpr(isabelle.checkTermExpr(Ref[IContext](contextId).read)(constrainedTerm))
//    }
    def prettyExpression(term:Term): String = Isabelle.symbolsToUnicode(isabelle.invoke(printTermOp,(contextId,term)))
    def readTyp(str:String) : ITyp = isabelle.invoke(readTypOp, (contextId,str))
    def prettyTyp(typ:ITyp): String = Isabelle.symbolsToUnicode(isabelle.invoke(printTypOp,(contextId,typ)))
    def simplify(term: Term, facts:List[String]) : Term = isabelle.invoke(simplifyTermOp, (term,facts,contextId))
//    @deprecated("use operations","now")
//    def contextExpr: Expr[IContext] = context.read
  }
}
