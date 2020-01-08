package qrhl.isabelle

import java.io.{BufferedReader, IOException, InputStreamReader}
import java.lang
import java.lang.ref.Cleaner
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{Files, Path, Paths}
import java.util.{Timer, TimerTask}

import info.hupel.isabelle.api.{Configuration, Version, XML}
import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.{Abs, App, Bound, Const, Free, Term, Typ, Type, Var}
import info.hupel.isabelle.setup.Setup.Absent
import info.hupel.isabelle.setup.{Resolver, Resources, Setup}
import info.hupel.isabelle.{Codec, Observer, OfficialPlatform, Operation, Platform, System, XMLResult, ml}
import monix.execution.Scheduler.Implicits.global
import org.log4s
import qrhl.{Subgoal, UserException}
import qrhl.logic._

import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scala.util.matching.Regex
import scala.util.{Left, Right}
import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec
import qrhl.isabelle.Isabelle.Thm
import qrhl.isabelle.{IsabelleConsts => c, IsabelleTypes => t}
import scalaz.Applicative

object DistributionDirectory {
  /** Tries to determine the distribution directory. I.e., when running from sources, the source distribution,
    * and when running from installation, the installation directory.
    * Returned as an absolute path.
    */
  lazy val distributionDirectory: Path = {
    val location = this.getClass.getProtectionDomain.getCodeSource.getLocation.toURI
    assert(location.getScheme == "file")
    val path = Paths.get(location)
    val dir =
      if (path.getFileName.toString.endsWith(".jar")) {
        val jarDir = path.getParent.toAbsolutePath
        if (jarDir.endsWith("lib"))
          jarDir.getParent
        else
          jarDir
      }
      else Paths.get("").toAbsolutePath

    assert(Files.exists(dir.resolve("isabelle-thys")))
    logger.debug(s"Distribution directory = $dir")
    dir
  }

  private val logger = log4s.getLogger
}

class Isabelle(path: String, build: Boolean = sys.env.contains("QRHL_FORCE_BUILD")) {
  val version = Version.Stable("2019-RC4")
  private val auto = path == "auto"

  /** In the directory that contains the jar, or, if not loaded from a jar, the current directory. */
  private val localStoragePath = DistributionDirectory.distributionDirectory.resolve("isabelle-temp")

  private val platform: Platform = Platform.guess match {
    case None if auto => throw UserException(""""isabelle auto" used, but cannot detect platform. Use "isabelle <path>" with an existing Isabelle install at <path> instead""")
    case None if !auto => Platform.genericPlatform(localStoragePath)
    case Some(p) => p.withLocalStorage(localStoragePath)
  }

  private val setup: Setup = {
    if (auto) {
      //      Setup.default(version,updateIfDevel = false).right.get
      assert(platform.isInstanceOf[OfficialPlatform])
      Setup.detect(platform, version, updateIfDevel = false) match {
        case Right(install) => install
        case Left(Absent) =>
          println(s"*** Downloading Isabelle into ${platform.localStorage}. May take a while...")
          Setup.install(platform.asInstanceOf[OfficialPlatform], version) match {
            case Right(install) => install
            case Left(reason) => throw UserException("Could not install Isabelle: " + reason.explain)
          }
        case Left(reason) => throw UserException("Could not setup Isabelle: " + reason.explain)
      }
    } else {
      //      val platformPath = Paths.get("tmp-isabelle")
      //      val platform = Platform.genericPlatform(platformPath)
      //      Setup(Paths.get(path), Platform.guess.get, version)
      Setup(Paths.get(path), platform, version)
    }
  }

  //  private val resources = Resources.dumpIsabelleResources() match {
  //    case Left(error) => throw new IOException(error.explain)
  //    case Right(r) => r
  //  }
  //  Files.delete(resources.component.resolve("ROOTS"))

  private val components = List(
    //    resources.component,
    DistributionDirectory.distributionDirectory.resolve("isabelle-afp"),
    //    DistributionDirectory.distributionDirectory.resolve("isabelle-thys/protocol"),
    DistributionDirectory.distributionDirectory.resolve("isabelle-thys")
  )

  private val environment: info.hupel.isabelle.api.Environment = {
    //    if (path == "auto") println("Downloading Isabelle if needed (may take a while)")
    try {
      val env = setup.makeEnvironment(resolver = Resolver.Default,
        user = platform.userStorage(version),
        components = components,
        options = Nil)
      Await.result(env, Duration.Inf)
    } catch {
      case e: RuntimeException if e.getMessage.startsWith("Generic environment does not support unofficial platform") =>
        throw UserException("Bad Isabelle root directory (probably)")
    }
  }

  private val config: Configuration = Configuration.simple("QRHL")

  private def doBuild() {
    println("*** Building Isabelle (may take a while, especially the first time, e.g., 20-60min)...")
    if (!System.build(environment, config))
      throw qrhl.UserException("Building Isabelle failed")
  }

  private def checkBuilt(): Boolean = {
    //    val location = this.getClass.getProtectionDomain.getCodeSource.getLocation.toURI
    //    assert(location.getScheme=="file")
    //    println("LOC "+Paths.get(location))
    //    val comparedTo = Files.getLastModifiedTime(Paths.get(location))
    //    println(comparedTo)

    import scala.collection.JavaConverters._

    val isabelleThys = Files.find(DistributionDirectory.distributionDirectory.resolve("isabelle-thys"),
      10, (path: Path, _: BasicFileAttributes) => true).iterator.asScala.toList
    assert(isabelleThys.nonEmpty)
    val newest = isabelleThys.map {
      Files.getLastModifiedTime(_)
    }.max

    /* TODO: Correct heap dir should be
      environment.isabelleSetting("ISABELLE_HEAPS") + "/" +
      environment.isabelleSetting("ML_SYSTEM") + "/" +
      environment.isabelleSetting("ML_PLATFORM")
      We could just delete this heap file if checkBuilt returns false.
      This makes sure that build is not done each time.
      But: check how this works with Windows paths
     */

    val heaps = try {
      Files.find(environment.etc.getParent.resolve("heaps"), 10, { (path: Path, _: BasicFileAttributes) =>
        path.endsWith("QRHL") && !path.getParent.endsWith("log")
      }).iterator.asScala.toList
    } catch {
      case _: IOException => return false
    }

    if (heaps.isEmpty)
      return false
    val newestHeap = heaps.map {
      Files.getLastModifiedTime(_)
    }.max

    //    println("Newest:      ",newest)
    //    println("Newest heap: ",newestHeap)

    if (newestHeap.compareTo(newest) > 0)
      return true

    false
  }

  //    try {
  //      val files = Files.find(environment.etc.getParent.resolve("heaps"), 10, { (path: Path, _: BasicFileAttributes) =>
  //        path.endsWith("QRHL-Protocol") && !path.getParent.endsWith("log")
  ////        path.endsWith("QRHL") && !path.endsWith("log")/*&& attr.lastModifiedTime().compareTo(comparedTo) > 0*/
  //      })
  //      files.findAny().isPresent
  //    } catch {
  //      case _ : IOException => false
  //    }

  private val system = {
    if (build || !checkBuilt())
      doBuild()

    Await.result(System.create(environment, config), Duration.Inf)
  }

  //  private def unitConv[A]: Expr[A => Unit] = ml.Expr.uncheckedLiteral("(fn _ => ())")

  def invoke[I, O](op: Operation[I, O], arg: I): O = {
    val start = lang.System.nanoTime
    val result = Await.result(system.invoke(op)(arg), Duration.Inf).unsafeGet
    Isabelle.logger.debug(s"Operation ${op.name} ${(lang.System.nanoTime - start) / 1000000}ms")
    result
  }

  //  // TODO remove
  //  new Timer().schedule(new TimerTask {
  //    override def run(): Unit = { invoke(Operation.Hello,"world") }
  //  },100,100)

  /** Creates a new context that imports QRHL.QRHL, QRHL.QRHL_Operations the given theories.
    *
    * @param thys Path pointing to theory files (including the suffix .thy)
    * @return the context
    */
  def getQRHLContextWithFiles(thys: Path*): (Isabelle.Context, List[Path]) = {
    getContextWithThys(List("QRHL.QRHL", "QRHL.QRHL_Operations"), thys.toList)
    // TODO: Do we need to include QRHL.QRHL_Operations?
  }

  /** Creates a new context that imports the given theories.
    *
    * @param thys  Names of theories that have to be contained in the current session
    * @param files Path pointing to theory files (including the suffix .thy)
    * @return the context
    */
  private def getContextWithThys(thys: List[String], files: List[Path]): (Isabelle.Context, List[Path]) = {
    import scala.collection.JavaConverters._
    for (f <- files)
      if (!Files.isRegularFile(f))
        throw UserException(s"Isabelle theory file not found: $f")
    val filesThyPath = files.map { f =>
      //      println("XXX",f,Paths.get(""))
      val relative = Paths.get("").toAbsolutePath.relativize(f.toAbsolutePath)
      val names = relative.iterator().asScala.toList
      names.mkString("/").stripSuffix(".thy")
    }
    val filesThyName = files.map { f => "Draft." + f.getName(f.getNameCount - 1).toString.stripSuffix(".thy") }
    //    println("Isabelle getContextWithThys", files, filesThyPath)
    invoke(Operation.UseThys, filesThyPath)
    val imports = filesThyName ::: thys // Order is important. This way, namespace elements of "files" shadow namespace elements of "thys", not the other way around
    val (ctxId, dependencies) = invoke(Isabelle.createContextOp, imports)
    val ctxt = new Isabelle.Context(this, ctxId)
    val paths = dependencies.map(Paths.get(_))

    for (p <- paths)
      if (!Files.exists(p))
        println(s"*** Theory has non-existing dependency $p. This is a bug. Please report.")

    (ctxt, paths.filter(Files.exists(_)))
  }

  private var disposed = false

  def dispose(): Unit = this.synchronized {
    if (Isabelle.isGlobalIsabelle(this))
      throw new lang.RuntimeException("Trying to dispose Isabelle.globalIsabelle")
    if (!disposed) {
      Isabelle.logger.debug("Disposing Isabelle.")
      Await.result(system.dispose, Duration.Inf)
      Isabelle.logger.debug("Disposing Isabelle (done).")
      disposed = true
    }
  }

  override def finalize(): Unit = {
    dispose()
    //noinspection ScalaDeprecation
    super.finalize()
  }

  def runJEdit(files: Seq[String] = Nil): Unit = environment.exec("jedit", List("-l", "QRHL") ++ files.toList)
}

object Isabelle {
  val not : Const = Const(c.not, HOLogic.boolT -->: HOLogic.boolT)
  def not(t: Term) : Term = not $ t
  def less_eq(typ : Typ) = Const(c.less_eq, typ -->: typ -->: boolT)
  def less_eq(t: Term, u:Term) : Term = less_eq(fastype_of(t)) $ t $ u

  private val cleaner = Cleaner.create()

  def swap_variables_subspace(v: Term, w: Term, pre: Term): Term = {
    val typ = fastype_of(v)
    Const(c.swap_variables_subspace, typ -->: typ -->: predicateT -->: predicateT) $ v $ w $ pre
  }

  def default(t: Typ): Const = Const(c.default, t)
  def ket(t: Typ): Const = Const(c.ket, t -->: ell2T(t))
  def ket(term: Term) : Term = ket(fastype_of(term)) $ term

  def unitary(t: Typ, u: Typ): Const = Const(c.unitary, boundedT(t,u) -->: boolT)
  def unitary(u: Term): Term = Const(c.unitary, fastype_of(u) -->: boolT) $ u

  def tensorOp(a : Term, b : Term): Term = (a,b) match {
    case (OfType(L2BoundedT(ta,tb)), OfType(L2BoundedT(tc,td))) => tensorOp(ta,tb,tc,td) $ a $ b
    case _ => throw new RuntimeException(s"Cannot apply tensorOp to types ${fastype_of(a)}, ${fastype_of(b)}")
  }
  def tensorOp(ta: Typ, tb: Typ, tc: Typ, td: Typ): Const =
    Const(c.tensorOp, l2boundedT(ta,tb) -->: l2boundedT(tc,td) -->: l2boundedT(prodT(ta,tc),prodT(tb,td)))

  def idOp(valueTyp: Typ) = Const(c.idOp, boundedT(valueTyp, valueTyp))

  private var globalIsabellePeek: Isabelle = _
  lazy val globalIsabelle: Isabelle = {
    val isabelle = new Isabelle("auto")
    globalIsabellePeek = isabelle
    isabelle
  }

  def isGlobalIsabelle(isabelle: Isabelle): Boolean =
    (globalIsabellePeek != null) && (globalIsabelle == isabelle)

  @deprecated("use Expression.toString", "now")
  def pretty(t: Term): String = Isabelle.theContext.prettyExpression(t)

  def pretty(t: Typ): String = Isabelle.theContext.prettyTyp(t)

  implicit object applicativeXMLResult extends Applicative[XMLResult] {
    override def point[A](a: => A): XMLResult[A] = Right(a)

    override def ap[A, B](fa: => XMLResult[A])(f: => XMLResult[A => B]): XMLResult[B] = fa match {
      case Left(error) => Left(error)
      case Right(a) => f match {
        case Left(error) => Left(error)
        case Right(ab) => Right(ab(a))
      }
    }
  }


  object Thm {
    private val logger = log4s.getLogger
    val show_oracles_lines_op: Operation[BigInt, List[String]] = Operation.implicitly[BigInt, List[String]]("show_oracles_lines")

    implicit def codec(implicit isabelle: Isabelle): Codec[Isabelle.Thm] =
      new Codec[Isabelle.Thm] {
        override val mlType: String = "thm"

        override def encode(thm: Thm): XML.Tree = XML.elem(("thm", List(("id", thm.thmId.toString))), Nil)

        override def decode(xml: XML.Tree): XMLResult[Thm] = xml match {
          case XML.Elem(("thm", List(("id", id))), Nil) => Right(new Thm(isabelle, BigInt(id)))
        }
      }

    class CleaningAction(isabelle: Isabelle, thmId: BigInt) extends Runnable {
      override def run(): Unit = {
        logger.debug(s"Deleting theorem $thmId")
        isabelle.invoke(deleteThmOp, thmId)
      }
    }

  }

  private val logger = log4s.getLogger

//  def mk_conj(t1: Term, t2: Term): Term = HOLogic.conj $ t1 $ t2

  def conj(terms: Term*): Term = terms match {
    case Seq(t, ts @ _*) => ts.foldLeft(t) { (t1,t2) => HOLogic.conj $ t1 $ t2 }
    case Nil => HOLogic.True
  }

  def disj(terms: Term*): Term = terms match {
    case Seq(t, ts @ _*) => ts.foldLeft(t) { (t1,t2) => HOLogic.disj $ t1 $ t2 }
    case Nil => HOLogic.False
  }

  def mk_list(typ: Typ, terms: List[Term]): Term = {
    val lT = listT(typ)
    val cons = Const(c.Cons, typ -->: lT -->: lT)
    val nil = Const(c.Nil, lT)
    terms.foldRight[Term](nil)(cons $ _ $ _)
  }

  // TODO rename constants
//  val vectorT_name = "Complex_L2.ell2"

  def ell2T(typ: Typ) = Type(t.ell2, List(typ))
  object Ell2T {
    def unapply(typ: Typ) = typ match {
      case Type(t.ell2, List(typ)) => Some(typ)
      case _ => None
    }
  }

  def dest_vectorT(typ: Typ): Typ = typ match {
    case Type(t.ell2, List(t1)) => t1
    case _ => throw new RuntimeException("expected type 'vector', not " + typ)
  }

  val dummyT = Type(t.dummy)
  val natT = Type(t.nat)
  val bitT = Type(t.bit, Nil)
//  val linear_spaceT_name = "Complex_Inner_Product.linear_space"
  val predicateT = Type(t.linear_space, List(ell2T(Type(t.mem2, Nil))))
  val programT = Type(t.program)
  val oracle_programT = Type(t.oracle_program)
  val classical_subspace : Term= Const(c.classical_subspace, HOLogic.boolT -->: predicateT)
  def classical_subspace(t:Term) : Term = classical_subspace $ t

  val predicate_inf = Const(c.inf, predicateT -->: predicateT -->: predicateT)
  val predicate_bot = Const(c.bot, predicateT)
  val predicate_top = Const(c.top, predicateT)
  val predicate_0 = Const(c.zero, predicateT)
//  val distrT_name = "Discrete_Distributions.distr"


  object Inf {
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case App(App(Const(IsabelleConsts.inf,_), a), b) => Some((a,b))
      case _ => None
    }
  }
  def inf(typ: Typ) : Const = Const(c.inf, typ -->: typ -->: typ)
  def inf(term: Term, terms: Term*): Term = {
    val typ = fastype_of(term)
    val inf_ = inf(typ)
    terms.foldLeft(term) { (a,b) => inf_ $ a $ b }
  }

  def distrT(typ: Typ): Type = Type(t.distr, List(typ))

  def dest_distrT(typ: Typ): Typ = typ match {
    case Type(t.distr, List(typ2)) => typ2
    case _ => throw new RuntimeException(s"expected type ${t.distr}, not " + typ)
  }

//  val BoundedT_name: String = "Bounded_Operators.Bounded"
  def boundedT(inT: Typ, outT: Typ) = Type(t.bounded, List(inT, outT))
  object BoundedT {
    def unapply(typ: Typ): Option[(Typ,Typ)] = typ match {
      case Type(t.bounded, List(t1, t2)) => Some((t1, t2))
      case _ => None
    }
  }

  @deprecated("use BoundedT","now")
  def dest_boundedT(typ: Typ): (Typ, Typ) = typ match {
    case Type(t.`bounded`, List(t1, t2)) => (t1, t2)
    case _ => throw new RuntimeException(s"expected type ${t.bounded}, not " + typ)
  }

  def l2boundedT(typ: Typ): Type = l2boundedT(typ, typ)
  def l2boundedT(inT: Typ, outT: Typ): Type = boundedT(ell2T(inT), ell2T(outT))
  object L2BoundedT {
    def unapply(typ: Typ): Option[(Typ,Typ)] = typ match {
      case BoundedT(Ell2T(t1),Ell2T(t2)) => Some((t1,t2))
      case _ => None
    }
  }

  def dest_l2boundedT(typ: Typ): (Typ, Typ) = typ match {
    case Type(t.`bounded`, List(Type(t.ell2, List(t1)), Type(t.ell2, List(t2)))) => (t1, t2)
    case _ => throw new RuntimeException("expected type 'l2bounded', not " + typ)
  }

//  val measurementT_name = "QRHL_Core.measurement"

  def measurementT(resultT: Typ, qT: Typ) = Type(t.measurement, List(resultT, qT))

  def dest_measurementT(typ: Typ): (Typ, Typ) = typ match {
    case Type(t.measurement, List(typ1, typ2)) => (typ1, typ2)
    case _ => throw new RuntimeException(s"expected type ${t.measurement}, not " + typ)
  }

  def listT(typ: Typ): Type = Type(t.list, List(typ))

  val block = Const(c.block, listT(programT) -->: programT)

  def variableT(typ: Typ) = Type(t.variable, List(typ))
  object VariableT {
    def unapply(typ: Typ): Option[Typ] = typ match {
      case Type(t.variable, List(typ)) => Some(typ)
      case _ => None
    }
  }
  @deprecated("use VariableT.unapply instead","now")
  def dest_variableT(typ: Typ): Typ = typ match {
    case Type(t.variable, List(typ2)) => typ2
    case _ => throw new RuntimeException(s"expected type ${t.variable}, not " + typ)
  }

  def variablesT(typ: Typ): Type = Type(t.variables, List(typ))
  object VariablesT {
    def unapply(typ: Typ): Option[Typ] = typ match {
      case Type(t.variables, List(typ)) => Some(typ)
      case _ => None
    }
  }

  def variablesT(typs: List[Typ]): Type = variablesT(tupleT(typs: _*))

  //val cvariableT: Typ => Type = variableT
  def expressionT(typ: Typ) = Type(t.expression, List(typ))

  val instantiateOracles = Const(c.instantiateOracles, oracle_programT -->: listT(programT) -->: programT)
//  val assignName = c.assign

  def assign(typ: Typ): Const = Const(c.assign, variablesT(typ) -->: expressionT(typ) -->: programT)

//  val sampleName = c.sample

  def sample(typ: Typ): Const = Const(c.sample, variablesT(typ) -->: expressionT(distrT(typ)) -->: programT)

  val propT = Type(t.prop)

//  val ifthenelseName = "Programs.ifthenelse"
  val ifthenelse = Const(c.ifthenelse, expressionT(HOLogic.boolT) -->: listT(programT) -->: listT(programT) -->: programT)
//  val whileName = "Programs.while"
  val whileProg = Const(c.`while`, expressionT(HOLogic.boolT) -->: listT(programT) -->: programT)
  val metaImp = Const(c.imp, propT -->: propT -->: propT)
  val boolT: Typ = HOLogic.boolT
  val implies = Const(c.implies, boolT -->: boolT -->: boolT)
  def implies(a: Term, b: Term): Term = implies $ a $ b
  val qrhl = Const(c.qrhl, expressionT(predicateT) -->: listT(programT) -->: listT(programT) -->: expressionT(predicateT) -->: boolT)
//  val qinitName = c.qinit

  def qinit(typ: Typ) = Const(c.qinit, variablesT(typ) -->: expressionT(ell2T(typ)) -->: programT)

//  val qapplyName = "Programs.qapply"

  def qapply(typ: Typ) = Const(c.qapply, variablesT(typ) -->: expressionT(l2boundedT(typ)) -->: programT)

//  val measurementName = c.measurement

  def measurement(resultT: Typ, qT: Typ) = Const(c.measurement, variablesT(resultT) -->: variablesT(qT) -->: expressionT(measurementT(resultT, qT)) -->: programT)

  val unitT = Type(t.unit)
//  val prodT_name = "Product_Type.prod"

  def prodT(t1: Typ, t2: Typ) = Type(t.prod, List(t1, t2))

  def dest_prodT(typ: Typ): (Typ, Typ) = typ match {
    case Type(t.prod, List(t1, t2)) => (t1, t2)
    case _ => throw new RuntimeException(s"expected type ${t.prod}, not " + typ)
  }

  private def qvarTuple_var0(qvs: List[QVariable]): (Term, Typ) = qvs match {
    case Nil => (variable_unit, unitT)
    case List(qv) => (variable_singleton(qv.valueTyp) $ qv.variableTerm,
      qv.valueTyp)
    case qv :: rest =>
      val (qvTuple, qvTyp) = qvarTuple_var0(List(qv))
      val (restTuple, restTyp) = qvarTuple_var0(rest)
      (variable_concat(qvTyp, restTyp) $ qvTuple $ restTuple,
        prodT(qvTyp, restTyp))
  }

  def qvarTuple_var(qvs: List[QVariable]): Term = qvarTuple_var0(qvs)._1

  val variable_unit = Const(c.variable_unit, variablesT(unitT))
//  val variable_singletonName = c.variable_singleton

  def variable_singleton(typ: Typ) = Const(c.variable_singleton, variableT(typ) -->: variablesT(typ))
  def variable_singleton(t: Term): Term = t match {
    case OfType(VariableT(typ)) => variable_singleton(typ) $ t
  }

//  val variable_concatName = c.variable_concat

  def variable_concat(t1: Typ, t2: Typ) = Const(c.variable_concat, variablesT(t1) -->: variablesT(t2) -->: variablesT(prodT(t1, t2)))

  def variable_concat(t1: Term, t2: Term) : Term = (t1,t2) match {
    case (OfType(VariablesT(typ1)), OfType(VariablesT(typ2))) =>
      variable_concat(typ1,typ2) $ t1 $ t2
  }

  object OfType {
    def unapply(t: Term) = Some(fastype_of(t))
  }

  def fastype_of(t: Term, typs: List[Typ] = Nil): Typ = t match {
    case App(f,u) => fastype_of(f, typs) match {
      case Type("fun", List(_,typ)) => typ
    }
    case Const(_, typ) => typ
    case Free(_, typ) => typ
    case Var(_, typ) => typ
    case Bound(i) => typs(i.intValue)
    case Abs(_,typ,u) => typ -->: fastype_of(u, typ::typs)
  }



  val realT = Type(t.real)
  val stringT: Type = listT(Type(t.char))
  val program_stateT = Type(t.program_state)
  val probability = Const(c.probability, expressionT(boolT) -->: programT -->: program_stateT -->: realT)
  //  val probability_old = Const("Encoding.probability_old", stringT -->: programT -->: program_stateT -->: realT)

  val checkTypeOp: Operation[(BigInt, Term), Typ] = Operation.implicitly[(BigInt, Term), Typ]("check_type")
  //  val useThys2Op: Operation[List[String], Unit] = Operation.implicitly[List[String], Unit]("use_thys2")
  val createContextOp: Operation[List[String], (BigInt, List[String])] =
    Operation.implicitly[List[String], (BigInt, List[String])]("create_context")
  val deleteContextOp: Operation[BigInt, Unit] = Operation.implicitly[BigInt, Unit]("delete_context")
  val deleteThmOp: Operation[BigInt, Unit] = Operation.implicitly[BigInt, Unit]("delete_thm")
  val printTermOp: Operation[(BigInt, Term), String] = Operation.implicitly[(BigInt, Term), String]("print_term")
  val printTypOp: Operation[(BigInt, Typ), String] = Operation.implicitly[(BigInt, Typ), String]("print_typ")
  val addAssumptionOp: Operation[(String, Term, BigInt), BigInt] = Operation.implicitly[(String, Term, BigInt), BigInt]("add_assumption")
  val readTypOp: Operation[(BigInt, String), Typ] = Operation.implicitly[(BigInt, String), Typ]("read_typ")
  @deprecated("use readExpression", "now")
  val readTermOp: Operation[(BigInt, String, Typ), Term] = Operation.implicitly[(BigInt, String, Typ), Term]("read_term")
  val simplifyTermOp: Operation[(Term, List[String], BigInt), (RichTerm, BigInt)] = Operation.implicitly[(Term, List[String], BigInt), (RichTerm, BigInt)]("simplify_term")
  val declareVariableOp: Operation[(BigInt, String, Typ), BigInt] = Operation.implicitly[(BigInt, String, Typ), BigInt]("declare_variable")
//  val one_name = "Groups.one_class.one"
  val True_const = Const(c.True, boolT)
  val thms_as_subgoals: Operation[(BigInt, String), List[Subgoal]] = Operation.implicitly[(BigInt,String),List[Subgoal]]("thms_as_subgoals")


  def mk_eq(a: Term, b: Term): Term = {
    val typ = fastype_of(a)
    Const(c.eq, typ -->: typ -->: HOLogic.boolT) $ a $ b
  }

  /** Analogous to Isabelle's HOLogic.dest_list. Throws [[MatchError]] if it's not a list */
  def dest_list(term: Term): List[Term] = term match {
    case Const(c.Nil, _) => Nil
    case App(App(Const(c.Cons, _), t), u) => t :: dest_list(u)
    case _ => throw new MatchError(term)
  }

  /** Analogous to Isabelle's HOLogic.dest_numeral. Throws [[MatchError]] if it's not a numeral */
  def dest_numeral(term: Term): BigInt = term match {
    case Const(c.numOne, _) => 1
    case App(Const(c.numBit0, _), bs) => 2 * dest_numeral(bs)
    case App(Const(c.numBit1, _), bs) => 2 * dest_numeral(bs) + 1
    case _ => throw new MatchError(term)
  }

  /** Analogous to Isabelle's HOLogic.dest_bit. Throws [[MatchError]] if it's not a char */
  def dest_bit(term: Term): Int = term match {
    case HOLogic.True => 1
    case HOLogic.False => 0
    case _ => throw new MatchError(term)
  }

  def dest_bits(bits: Term*): Int = {
    val bits2 = bits.map(dest_bit)
    //    println(bits)
    var value = 1
    var result = 0
    for (b <- bits2) {
      result += b * value
      //      println(b,result)
      value *= 2
    }
    //    println(result.toChar)
    result
  }

  /** Analogous to Isabelle's HOLogic.dest_char. Throws [[MatchError]] if it's not a char */
  def dest_char(term: Term): Char = term match {
    case App(App(App(App(App(App(App(App(Const(c.Char, _), b0), b1), b2), b3), b4), b5), b6), b7) =>
      dest_bits(b0, b1, b2, b3, b4, b5, b6, b7).toChar
    case _ => throw new MatchError(term)
  }

  /** Analogous to Isabelle's HOLogic.dest_string. Throws [[MatchError]] if it's not a string */
  def dest_string(term: Term): String =
    dest_list(term).map(dest_char).mkString

  def tupleT(typs: Typ*): Typ = typs match {
    case Nil => unitT
    case List(typ) => typ
    case typ :: rest => prodT(typ, tupleT(rest: _*))
  }

  def tupleT(typs: VarTerm[Typ]): Typ = typs match {
    case VTUnit => unitT
    case VTCons(a, b) => prodT(tupleT(a), tupleT(b))
    case VTSingle(v) => v
  }

  def freeVars(term: Term): Set[String] = {
    val fv = new mutable.SetBuilder[String, Set[String]](Set.empty)

    def collect(t: Term): Unit = t match {
      case Free(v, _) => fv += v
      case Const(_, _) | Bound(_) | Var(_, _) =>
      case App(t1, t2) => collect(t1); collect(t2)
      case Abs(_, _, body) => collect(body)
    }

    collect(term)
    fv.result
  }

  //  private val configureContext: ml.Expr[IContext => IContext] =
  //    ml.Expr.uncheckedLiteral("(fn ctx => ctx (*|> Config.put show_types true |> Config.put show_sorts true*) )")
  //  private def simplifyTerm(term: Term, facts:List[String]) : ml.Expr[IContext => Term] = {
  //    val lit = ml.Expr.uncheckedLiteral[Term => List[String] => IContext => Term]("QRHL.simp")
  //    lit(term)(implicitly)(facts)
  //  }

/*  def absfree(varName: String, varTyp: Typ, term: Term): ml.Expr[Term] = {
    val lit = ml.Expr.uncheckedLiteral[String => Typ => Term => Term](
      "(fn name => fn T => fn t => Term.absfree (name,T) t)")
    val eval1 = lit(varName)
    val eval2 = eval1(varTyp)
    eval2(term)
  }*/

  val (symbols, symbolsInv) = {
    import scala.collection.JavaConverters._

    val lineRegex = """^\\<([a-zA-Z0-9^_]+)>\s+code:\s+0x([0-9a-fA-F]+)\b.*""".r
    val reader = new BufferedReader(new InputStreamReader(this.getClass.getResource("symbols").openStream()))
    val results = new ListBuffer[(String, Int)]
    for (line <- reader.lines().iterator.asScala) {
      //      println(line)
      line match {
        case lineRegex(name, codepoint) => results.append((name, Integer.parseInt(codepoint, 16)))
        case _ => assert(!line.startsWith("\\")) // Lines with \ at the beginning should be matched by lineRegex
      }
    }
    reader.close()
    //    println(results map { case (n,i) => new String(Character.toChars(i))+" " } mkString)
    val symbols = Map(results: _*)
    val symbolsInv = Map(results map { case (n, i) => (i, n) }: _*)
    (symbols, symbolsInv)
  }

  private val symbolRegex = """\\<([a-zA-Z0-9^_]+)>""".r

  def symbolsToUnicode(str: String): String = symbolRegex.replaceAllIn(str,
    { m: Regex.Match =>
      symbols.get(m.group(1)) match {
        case Some(i) => new String(Character.toChars(i))
        case None => m.matched
      }
    })

  // following https://stackoverflow.com/a/1527891/2646248
  private def codepoints(str: String): Seq[Int] = {
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

  def unicodeToSymbols(str: String): String = {
    val sb = new StringBuffer(str.length() * 11 / 10)
    for (cp <- codepoints(str)) {
      if (cp <= 128) sb.append(cp.toChar)
      else symbolsInv.get(cp) match {
        case Some(sym) => sb.append("\\<"); sb.append(sym); sb.append('>')
        case None =>
          if (cp > 255) throw UserException(f"""Character "${new String(Character.toChars(cp))}%s" (Ux$cp%04X) not supported by Isabelle""")
          sb.appendCodePoint(cp)
      }
    }
    sb.toString
  }

  private var _theContext: Context = _

  def theContext: Context = _theContext

  class Thm(val isabelle: Isabelle, val thmId: BigInt) {
    def show_oracles_lines(): List[String] = isabelle.invoke(Thm.show_oracles_lines_op, thmId).map(Isabelle.symbolsToUnicode)

    Isabelle.cleaner.register(this, new Thm.CleaningAction(isabelle, thmId))

    def show_oracles(): Unit = {
      Thm.logger.debug(show_oracles_lines().mkString("\n"))
    }

//    override protected def finalize(): Unit = {
//      logger.debug(s"Deleting theorem $thmId")
//      isabelle.invoke(deleteThmOp, thmId)
//      //noinspection ScalaDeprecation
//      super.finalize()
//    }
  }

  class Context(val isabelle: Isabelle, val contextId: BigInt) {
    _theContext = this

    def checkType(term: Term): Typ = {
      isabelle.invoke(checkTypeOp, (contextId, term))
    }

    Isabelle.cleaner.register(this, new Context.CleaningAction(isabelle, contextId))

    def declareVariable(name: String, isabelleTyp: Typ): Context = {
      val id = isabelle.invoke(declareVariableOp, (contextId, name, isabelleTyp))
      new Context(isabelle, id)
    }

    def addAssumption(name: String, assumption: Term): Context = {
      val id = isabelle.invoke(addAssumptionOp, (name, assumption, contextId))
      new Context(isabelle, id)
    }

    def map(f: BigInt => BigInt): Context =
      new Context(isabelle, f(contextId))

    @deprecated("Use Expression.read", "now")
    def readTerm(str: String, typ: Typ): Term = {
      isabelle.invoke(readTermOp, (contextId, str, typ))
    }

    @deprecated("Use Expression.toString", "now")
    def prettyExpression(term: Term): String = Isabelle.symbolsToUnicode(isabelle.invoke(printTermOp, (contextId, term)))

    def readTyp(str: String): Typ = isabelle.invoke(readTypOp, (contextId, str))

    def readTypUnicode(str: String): Typ = readTyp(unicodeToSymbols(str))

    def prettyTyp(typ: Typ): String = Isabelle.symbolsToUnicode(isabelle.invoke(printTypOp, (contextId, typ)))

    def simplify(term: Term, facts: List[String]): (RichTerm, Thm) =
      isabelle.invoke(simplifyTermOp, (term, facts.map(Isabelle.unicodeToSymbols), contextId)) match {
        case (t, thmId) => (t, new Thm(isabelle, thmId))
      }
  }

  object Context {

    implicit object codec extends Codec[Context] {
      override val mlType: String = "Proof.context"

      override def encode(ctxt: Context): XML.Tree = XML.elem(("context", List(("id", ctxt.contextId.toString))), Nil)

      def decode(isabelle: Isabelle, xml: XML.Tree): XMLResult[Context] = xml match {
        case XML.Elem(("context", List(("id", id))), Nil) => Right(new Context(isabelle, BigInt(id)))
      }

      // TODO: use an implicit isabelle argument
      override def decode(tree: XML.Tree): XMLResult[Context] = throw new RuntimeException("Use Context.codec.decode(Isabelle,XML.Tree) instead")
    }

    class CleaningAction(isabelle: Isabelle, contextId: BigInt) extends Runnable {
      override def run(): Unit = {
        logger.debug(s"Deleting context $contextId")
        isabelle.invoke(deleteContextOp, contextId)
      }
    }
  }


  def quantum_equality_full(typLeft : Typ, typRight : Typ, typZ : Typ) =
    Const(IsabelleConsts.quantum_equality_full, Isabelle.l2boundedT(typLeft,typZ) -->: Isabelle.variablesT(typLeft) -->: Isabelle.l2boundedT(typRight,typZ) -->: Isabelle.variablesT(typRight) -->: Isabelle.predicateT)
  def quantum_equality_full(u: Term, q: Term, v: Term, r: Term): Term = {
    val OfType(L2BoundedT(typL, typZ)) = u
    val OfType(L2BoundedT(typR, _)) = v
    quantum_equality_full(typL, typR, typZ) $ u $ q $ v $ r
  }
  object QuantumEqualityFull {
    def unapply(term: Term): Option[(Term, Term, Term, Term)] = term match {
      case App(App(App(App(Const(IsabelleConsts.quantum_equality_full,_), u), q), v), r) => Some((u,q,v,r))
      case _ => None
    }
  }

}
