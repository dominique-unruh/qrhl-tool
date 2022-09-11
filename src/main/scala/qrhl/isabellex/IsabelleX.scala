package qrhl.isabellex

import java.io.{FileInputStream, FileReader, IOException, StringReader}
import java.lang
import java.lang.ref.Cleaner
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{Files, Path, Paths}
import java.util.{Properties, Timer, TimerTask}
import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.{MLFunction, MLFunction2, MLValue, Version}
import de.unruh.isabelle.pure.{Abs, App, Bound, Const, Context, Free, Term, Theory, Thm, Typ, Type, Var}

import scala.concurrent.{Await, ExecutionContext, Future}
import org.log4s
import qrhl.{Subgoal, UserException, Utils}
import qrhl.logic._

import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import scala.concurrent.duration.Duration
import scala.util.matching.Regex
import scala.util.{Left, Right}
import de.unruh.isabelle.control
import de.unruh.isabelle.misc.Symbols.ProcessSubSuperMode
import de.unruh.isabelle.misc.{FutureValue, Symbols}
import de.unruh.isabelle.pure.exceptions.Exn
import hashedcomputation.{Hash, HashedValue}
import org.apache.commons.io.FileUtils
import qrhl.Utils.NestedException

//import qrhl.Utils.tryRelativize
import qrhl.isabellex.{IsabelleConsts => c, IsabelleTypes => t}

//import scalaz.Applicative

import scala.concurrent.ExecutionContext.Implicits.global
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import MLValueConverters.Implicits._

object Configuration {
  private val logger = log4s.getLogger

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

  private lazy val config = {
    val config = new Properties()
    val filenames = List(
      distributionDirectory.resolve("qrhl-tool.conf"),
      FileUtils.getUserDirectory.toPath.resolve(".qrhl-tool.conf")/*,
      Paths.get("qrhl-tool.conf")*/)
      .map (_.normalize.toAbsolutePath)
      .distinct
    val filenamesFound = ListBuffer[Path]()

    for (filename <- filenames;
         if Files.exists(filename)) {
      val stream = try {
        new FileInputStream(filename.toFile)
      } catch {
        case e: IOException =>
          throw UserException(s"Could not open $filename. (Reason: ${e.getMessage}) Make sure it is readable.")
      }
      val escaped = new String(stream.readAllBytes()).replace("\\", "\\\\")
      stream.close()
      config.load(new StringReader(escaped))
      filenamesFound += filename
    }

    if (filenamesFound.isEmpty)
      throw UserException(s"No config files found for qrhl-tool. I looked in the following places: ${filenames.mkString(", ")}")

    println(s"Loaded config file${if (filenamesFound.lengthIs == 1) "" else "s"}: ${filenamesFound.mkString(", ")}")

    config
  }

  def isabelleHome : Path = config.getProperty("isabelle-home") match {
    case null => throw UserException("Please set isabelle-home in qrhl-tool.conf")
    case path => distributionDirectory.resolve(path)
  }

/*  def session : String = config.getProperty("session") match {
    case null => "QRHL"
    case session => session
  }

  def sessionDirs : List[Path] = config.getProperty("session-dirs") match {
    case null => Nil
    case dirs => for (str <- dirs.split(raw",\s").toList)
      yield Paths.get(str.trim).normalize.toAbsolutePath
  }*/

/*  def isabelleUserDir : Path = config.getProperty("isabelle-user") match {
    case null => Path.of(lang.System.getProperty("user.home")).resolve(".isabelle")
    case path => distributionDirectory.resolve(path)
  }*/

  if (config.getProperty("isabelle-user") != null)
    throw UserException("Configuration option isabelle-user not supported. Set the environment variable ISABELLE_USER_HOME instead.")

  def afpRoot : Option[Path] = config.getProperty("afp-root") match {
    case null => None
    case path => Some(distributionDirectory.resolve(path))
  }

/*
  def afpThyRoot : Option[Path] = config.getProperty("afp-root") match {
    case null => None
    case path => Some(distributionDirectory.resolve(path).resolve("thys"))
  }
*/
}

class IsabelleX(val setup : Isabelle.Setup) {
  import IsabelleX._
  import Ops._

  /** In the directory that contains the jar, or, if not loaded from a jar, the current directory. */
  private val localStoragePath = Configuration.distributionDirectory.resolve("isabelle-temp")

/*  private def checkBuilt(): Boolean = {
    //    val location = this.getClass.getProtectionDomain.getCodeSource.getLocation.toURI
    //    assert(location.getScheme=="file")
    //    println("LOC "+Paths.get(location))
    //    val comparedTo = Files.getLastModifiedTime(Paths.get(location))
    //    println(comparedTo)

    import scala.collection.JavaConverters._

    val isabelleThys = Files.find(Configuration.distributionDirectory.resolve("isabelle-thys"),
      10, (path: Path, _: BasicFileAttributes) => true).iterator.asScala.toList
    assert(isabelleThys.nonEmpty)
    val newest = isabelleThys.map {
      Files.getLastModifiedTime(_)
    }.max

    val heaps = for (
      // We are guessing here where the home is. Probably not optimal.
      // Maybe the whole heap-removal thing should be skipped?
      isabelleDir <- List(Path.of(System.getProperty("user.home")).resolve(".isabelle").resolve(s"Isabelle${version}"), setup.isabelleHome);
      heapDir = isabelleDir.resolve("heaps");
      heap <- try { Files.find(heapDir, 10, { (_, _) => true }).iterator.asScala }
                  catch { case _ : IOException => Nil };
      if heap.endsWith("QRHL");
      if !heap.getParent.endsWith("log"))
      yield heap

    if (heaps.isEmpty)
      return false
    val newestHeap = heaps.map {
      Files.getLastModifiedTime(_)
    }.max

    if (newestHeap.compareTo(newest) > 0)
      return true

    // We conclude that there is a stale heap. This will trigger a rebuild but Isabelle may decide not to rebuild anyway.
    // Since we want to avoid triggering this every time, we delete the heap to make sure Isabelle rebuild (leading
    // to a fresh time stamp).
    for (heap <- heaps) {
      try
        Files.delete(heap)
      catch {
        case _ : IOException =>
      }
    }

    false
  }*/

  implicit val isabelleControl: control.Isabelle = {
//    val shouldBuild = build || !checkBuilt()
//    if (shouldBuild)
    println("*** Starting Isabelle process. The first time, this also builds Isabelle which can take a very long time (e.g., 20-60min)...")
    new control.Isabelle(setup).force
  }

  /** Creates a new context that imports QRHL.QRHL, QRHL.QRHL_Operations
   * and the given theories.
    *
    * @param thys Path pointing to theory files (including the suffix .thy)
    * @return the context
    */
  def getQRHLContextWithFiles(thys: Path*): (ContextX, List[Path]) = {
    getContextWithThys(List("QRHL.QRHL"), thys.toList)
  }

  /** Creates a new context that imports the given theories.
    *
    * @param thys  Names of theories that have to be contained in the current session
    * @param files Path pointing to theory files (including the suffix .thy)
    * @return the context
    */
  private def getContextWithThys(thys: List[String], files: List[Path]): (ContextX, List[Path]) = {
    import scala.collection.JavaConverters._
    for (f <- files)
      if (!Files.isRegularFile(f))
        throw UserException(s"Isabelle theory file not found: $f")

    val theories = thys.map(Theory.apply) ++ files.map(Theory.apply)
    val jointTheory : Theory = Theory.mergeTheories(mergedName = "QRHL_Session", theories = theories, endTheory=false)
    val ctxt = Context(jointTheory)

/*    val filesThyPath = files.map { f =>
      //      println("XXX",f,Paths.get(""))
      val relative = tryRelativize(setup.workingDirectory.toAbsolutePath, f.toAbsolutePath)
      val names = relative.iterator().asScala.toList /*match {
        case List(name) => List(".", name) // Otherwise Isabelle does not recognise this as a path
        case names => names
      }*/
      names.mkString("/").stripSuffix(".thy")
    }
    val filesThyName = files.map { f => "Draft." + f.getName(f.getNameCount - 1).toString.stripSuffix(".thy") }
    //    println("Isabelle getContextWithThys", files, filesThyPath)

    for (future <- filesThyPath.map(path => use_thy_op(MLValue(path)).retrieve))
      Await.result(future, Duration.Inf)

    val imports = filesThyName ::: thys // Order is important. This way, namespace elements of "files" shadow namespace elements of "thys", not the other way around
    val (ctxt, dependencies) =
      createContextOp(MLValue(imports)).retrieveNow

    val paths = dependencies.map(Paths.get(_)) */

    val paths : List[Path] = dependenciesOfTheory(jointTheory).retrieveNow

    for (p <- paths)
      if (!Files.exists(p))
        println(s"*** Theory has non-existing dependency $p. This is a bug. Please report.")

    (new ContextX(this, ctxt), paths.filter(Files.exists(_)))
  }

  private var disposed = false

  def dispose(): Unit = this.synchronized {
    if (IsabelleX.isGlobalIsabelle(this))
      throw new lang.RuntimeException("Trying to dispose Isabelle.globalIsabelle")
    if (!disposed) {
      IsabelleX.logger.debug("Disposing Isabelle.")
      isabelleControl.destroy()
      disposed = true
    }
  }

  override def finalize(): Unit = {
    dispose()
    //noinspection ScalaDeprecation
    super.finalize()
  }


  val boolT: Typ = Type(t.bool)
  val True_const: Const = Const(c.True, boolT)
  val False_const: Const = Const(c.False, boolT)
  val dummyT: Type = Type(t.dummy)
  val natT: Type = Type(t.nat)
  val intT: Type = Type(t.int)
  val bitT: Type = Type(t.bit)
  //  val linear_spaceT_name = "Complex_Inner_Product.linear_space"
  val predicateT: Type = Type(t.ccsubspace, ell2T(Type(t.mem2)))
  val programT: Type = Type(t.program)
  val oracle_programT: Type = Type(t.oracle_program)
  val classical_subspace : Term= Const(c.classical_subspace, boolT -->: predicateT)
  def classical_subspace(t:Term) : Term = classical_subspace $ t
  def classical_subspace_optimized(t: Term): Term = t match {
    case True_const => predicate_top
    case False_const => predicate_0
    case _ => classical_subspace(t)
  }
  val predicate_inf: Const = Const(c.inf, predicateT -->: predicateT -->: predicateT)
  val predicate_bot: Const = Const(c.bot, predicateT)
  val predicate_top: Const = Const(c.top, predicateT)
  val predicate_0: Const = Const(c.zero, predicateT)

  def undefined(typ: Typ) : Const = Const(c.undefined, typ)

  def liftSpace(typ: Typ) : Const = Const(c.liftSpace, linear_spaceT(ell2T(typ)) -->: variablesT(typ) -->: predicateT)
  def liftSpace(space: Term, vars: Term) : Term = {
    val typ = VariablesT.unapply(vars.fastType).get
    liftSpace(typ) $ space $ vars
  }

  def span(typ: Typ): Const = Const(c.ccspan, setT(typ) -->: linear_spaceT(typ))
  def span(term: Term): Term = term.fastType match {
    case SetT(typ) => span(typ) $ term
  }

  def span1(term: Term): Term = span(singleton_set(term))

  def singleton_set(term: Term): Term = insert(term, empty_set(term.fastType))

  def insert(typ: Typ): Const = Const(c.insert, typ -->: setT(typ) -->: setT(typ))
  def insert(elem: Term, set: Term): Term = insert(elem.fastType) $ elem $ set

  def empty_set(typ: Typ): Const = bot(setT(typ))

  def linear_spaceT(typ: Typ): Type = Type(t.ccsubspace, typ)

  val infiniteT: Typ = Type(t.infinite)

  def setT(typ: Typ): Type = Type(t.set, typ)
  object SetT {
    def unapply(arg: Typ): Option[Typ] = arg match {
      case Type(t.set, typ) => Some(typ)
      case _ => None
    }
  }

  def INF(typ: Typ): Const = Const(c.Inf, setT(typ) -->: typ)

  def image(a: Typ, b:Typ) : Const = Const(c.image, (a -->: b) -->: setT(a) -->: setT(b))

  def INF(varName: String, varTyp: Typ, term: Term): Term = {
    val typ = term.fastType
    INF(typ) $ (image(varTyp,typ) $ absfree(varName, varTyp, term) $ univ(varTyp))
  }

  def univ(typ: Typ): Const = top(setT(typ))

  def absfree(varName: String, varTyp: Typ, term: Term): Term =
    Ops.absfree(varName, varTyp, term).retrieveNow

  val not : Const = Const(c.not, boolT -->: boolT)
  def not(t: Term) : Term = not $ t
  def less_eq(typ : Typ): Const = Const(c.less_eq, typ -->: typ -->: boolT)
  def less_eq(t: Term, u:Term) : Term = less_eq(t.fastType) $ t $ u

  def swap_variables_subspace(v: Term, w: Term, pre: Term): Term = {
    val typ = v.fastType
    Const(c.swap_variables_subspace, typ -->: typ -->: predicateT -->: predicateT) $ v $ w $ pre
  }

  def default(t: Typ): Const = Const(c.default, t)
  def ket(t: Typ): Const = Const(c.ket, t -->: ell2T(t))
  def ket(term: Term) : Term = ket(term.fastType) $ term

  def unitary(t: Typ, u: Typ): Const = Const(c.unitary, boundedT(t,u) -->: boolT)
  def unitary(u: Term): Term = Const(c.unitary, u.fastType -->: boolT) $ u

  def tensorOp(a : Term, b : Term): Term = (a,b) match {
    case (OfType(L2BoundedT(ta,tb)), OfType(L2BoundedT(tc,td))) => tensorOp(ta,tb,tc,td) $ a $ b
    case _ => throw new RuntimeException(s"Cannot apply tensorOp to types ${pretty(a.fastType)}, ${pretty(b.fastType)}")
  }
  def tensorOp(ta: Typ, tb: Typ, tc: Typ, td: Typ): Const =
    Const(c.tensorOp, l2boundedT(ta,tb) -->: l2boundedT(tc,td) -->: l2boundedT(prodT(ta,tc),prodT(tb,td)))

  object IdOp {
    def unapply(arg: Term): Boolean = arg match {
      case Const(IsabelleConsts.idOp, _) => true
      case _ => false
    }
  }
  def idOp(valueTyp: Typ): Const = Const(c.idOp, boundedT(valueTyp, valueTyp))

  def show_oracles_lines(thm: Thm): List[String] = {
    show_oracles_lines_op(thm.mlValue).retrieveNow.map(IsabelleX.symbols.symbolsToUnicode(_))
  }
  def show_oracles(thm: Thm): Unit = {
    logger.debug(show_oracles_lines(thm).mkString("\n"))
  }

  val conj: Const = Const(c.conj, boolT -->: boolT -->: boolT)
  def conj(terms: Term*): Term = terms match {
    case Seq(ts @ _*) =>
      ts.dropRight(1).foldRight(ts.last) { (t1,t2) => conj $ t1 $ t2 }
    //    case Nil => HOLogic.True
  }

  val disj: Const = Const(c.disj, boolT -->: boolT -->: boolT)
  def disj(terms: Term*): Term = terms match {
    case Seq(t, ts @ _*) => ts.foldLeft(t) { (t1,t2) => disj $ t1 $ t2 }
    case Nil => False_const
  }

  def mk_list(typ: Typ, terms: List[Term]): Term = {
    val lT = listT(typ)
    val cons = Const(c.Cons, typ -->: lT -->: lT)
    val nil = Const(c.Nil, lT)
    terms.foldRight[Term](nil)(cons $ _ $ _)
  }

  def ell2T(typ: Typ): Type = Type(t.ell2, typ)
  object Ell2T {
    def unapply(typ: Typ): Option[Typ] = typ match {
      case Type(t.ell2, typ) => Some(typ)
      case _ => None
    }
  }

/*  def dest_vectorT(typ: Typ): Typ = typ match {
    case Type(t.ell2, t1) => t1
    case _ => throw new RuntimeException("expected type 'ell2', not " + typ)
  }*/

  def top(typ: Typ): Const = Const(c.top, typ)
  object Top {
    def unapply(arg: Term): Boolean = arg match {
      case Const(c.top, _) => true
      case _ => false
    }
  }

  def bot(typ: Typ): Const = Const(c.bot, typ)
  object Bot {
    def unapply(arg: Term): Boolean = arg match {
      case Const(c.bot, _) => true
      case _ => false
    }
  }


  def zero(typ: Typ): Const = Const(c.zero, typ)
  object Zero {
    def unapply(arg: Term): Boolean = arg match {
      case Const(c.zero, _) => true
      case _ => false
    }
  }

  object Inf {
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case App(App(Const(IsabelleConsts.inf,_), a), b) => Some((a,b))
      case _ => None
    }
  }
  def inf(typ: Typ) : Const = Const(c.inf, typ -->: typ -->: typ)
  def inf(term: Term, terms: Term*): Term = {
    val typ = term.fastType
    val inf_ = inf(typ)
    terms.foldLeft(term) { (a,b) => inf_ $ a $ b }
  }
  def infOptimized(term: Term, terms: Term*): Term = {
    val typ = term.fastType
    val terms2 = (term :: terms.toList).filterNot(Top.unapply)
    if (terms2.exists(Zero.unapply))
      return zero(typ)
    if (terms2.exists(Bot.unapply))
      return bot(typ)
    if (terms2.isEmpty)
      return top(typ)
    val infConst = inf(typ)
    terms2.tail.foldLeft(terms2.head) { (a,b) => infConst $ a $ b }
  }

  object Sup {
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case App(App(Const(IsabelleConsts.sup,_), a), b) => Some((a,b))
      case _ => None
    }
  }
  def sup(typ: Typ) : Const = Const(c.sup, typ -->: typ -->: typ)
  def sup(term: Term, terms: Term*): Term = {
    val typ = term.fastType
    val sup_ = sup(typ)
    terms.foldLeft(term) { (a,b) => sup_ $ a $ b }
  }

  object Plus {
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case App(App(Const(IsabelleConsts.plus,_), a), b) => Some((a,b))
      case _ => None
    }
  }
  def plus(typ: Typ) : Const = Const(c.plus, typ -->: typ -->: typ)
  def plus(term: Term, terms: Term*): Term = {
    val typ = term.fastType
    val plus_ = plus(typ)
    terms.foldLeft(term) { (a,b) => plus_ $ a $ b }
  }


  def distrT(typ: Typ): Type = Type(t.distr, typ)

  def dest_distrT(typ: Typ): Typ = typ match {
    case Type(t.distr, typ2) => typ2
    case _ => throw new RuntimeException(s"expected type ${t.distr}, not " + typ)
  }


  //  val BoundedT_name: String = "Bounded_Operators.Bounded"
  def boundedT(inT: Typ, outT: Typ): Type = Type(t.bounded, inT, outT)
  object BoundedT {
    def unapply(typ: Typ): Option[(Typ,Typ)] = typ match {
      case Type(t.bounded, t1, t2) => Some((t1, t2))
      case _ => None
    }
  }

  @deprecated("use BoundedT","now")
  def dest_boundedT(typ: Typ): (Typ, Typ) = typ match {
    case Type(t.`bounded`, t1, t2) => (t1, t2)
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
    case Type(t.`bounded`, Type(t.ell2, t1), Type(t.ell2, t2)) => (t1, t2)
    case _ => throw new RuntimeException("expected type 'l2bounded', not " + typ)
  }

  def measurementT(resultT: Typ, qT: Typ): Type = Type(t.measurement, resultT, qT)

  def dest_measurementT(typ: Typ): (Typ, Typ) = typ match {
    case Type(t.measurement, typ1, typ2) => (typ1, typ2)
    case _ => throw new RuntimeException(s"expected type ${t.measurement}, not " + typ)
  }

  def listT(typ: Typ): Type = Type(t.list, typ)

  val block: Const = Const(c.block, listT(programT) -->: programT)

  def variableT(typ: Typ): Type = Type(t.variable, typ)
  object VariableT {
    def unapply(typ: Typ): Option[Typ] = typ match {
      case Type(t.variable, typ) => Some(typ)
      case _ => None
    }
  }
  @deprecated("use VariableT.unapply instead","now")
  def dest_variableT(typ: Typ): Typ = typ match {
    case Type(t.variable, typ2) => typ2
    case _ => throw new RuntimeException(s"expected type ${t.variable}, not " + typ)
  }

  def variablesT(typ: Typ): Type = Type(t.variables, typ)
  object VariablesT {
    def unapply(typ: Typ): Option[Typ] = typ match {
      case Type(t.variables, typ) => Some(typ)
      case _ => None
    }
  }

  def variablesT(typs: List[Typ]): Type = variablesT(tupleT(typs: _*))

  //val cvariableT: Typ => Type = variableT
  def expressionT(typ: Typ): Type = Type(t.expression, typ)

  val instantiateOracles: Const = Const(c.instantiateOracles, oracle_programT -->: listT(programT) -->: programT)
  //  val assignName = c.assign

  def assign(typ: Typ): Const = Const(c.assign, variablesT(typ) -->: expressionT(typ) -->: programT)

  //  val sampleName = c.sample

  def sample(typ: Typ): Const = Const(c.sample, variablesT(typ) -->: expressionT(distrT(typ)) -->: programT)

  val propT: Type = Type(t.prop)

  //  val ifthenelseName = "Programs.ifthenelse"
  val ifthenelse: Const = Const(c.ifthenelse, expressionT(boolT) -->: listT(programT) -->: listT(programT) -->: programT)
  //  val whileName = "Programs.while"
  val whileProg = Const(c.`while`, expressionT(boolT) -->: listT(programT) -->: programT)
  val metaImp = Const(c.imp, propT -->: propT -->: propT)
  val implies = Const(c.implies, boolT -->: boolT -->: boolT)
  def implies(a: Term, b: Term): Term = implies $ a $ b
  val iff = Const(c.eq, boolT -->: boolT -->: boolT)
  val qrhl = Const(c.qrhl, expressionT(predicateT) -->: listT(programT) -->: listT(programT) -->: expressionT(predicateT) -->: boolT)
  //  val qinitName = c.qinit

  def qinit(typ: Typ) = Const(c.qinit, variablesT(typ) -->: expressionT(ell2T(typ)) -->: programT)

  //  val qapplyName = "Programs.qapply"

  def qapply(typ: Typ) = Const(c.qapply, variablesT(typ) -->: expressionT(l2boundedT(typ)) -->: programT)

  //  val measurementName = c.measurement

  def measurement(resultT: Typ, qT: Typ) = Const(c.measurement, variablesT(resultT) -->: variablesT(qT) -->: expressionT(measurementT(resultT, qT)) -->: programT)

  val unitT: Type = Type(t.unit)

  def prodT(t1: Typ, t2: Typ): Type = Type(t.prod, t1, t2)

  def dest_prodT(typ: Typ): (Typ, Typ) = typ match {
    case Type(t.prod, t1, t2) => (t1, t2)
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

  val variable_unit: Const = Const(c.variable_unit, variablesT(unitT))
  object Variable_Unit {
    def unapply(term: Term): Boolean = term match {
      case Const(c.variable_unit, _) => true
      case _ => false
    }
  }

  def variable_singleton(typ: Typ): Const = Const(c.variable_singleton, variableT(typ) -->: variablesT(typ))
  def variable_singleton(t: Term): Term = t match {
    case OfType(VariableT(typ)) => variable_singleton(typ) $ t
  }
  object Variable_Singleton {
    def unapply(term: Term): Option[Term] = term match {
      case App(Const(c.variable_singleton, _), v) => Some(v)
      case _ => None
    }
  }

  def variable_concat(t1: Typ, t2: Typ): Const = Const(c.variable_concat, variablesT(t1) -->: variablesT(t2) -->: variablesT(prodT(t1, t2)))
  def variable_concat(t1: Term, t2: Term) : Term = (t1,t2) match {
    case (OfType(VariablesT(typ1)), OfType(VariablesT(typ2))) =>
      variable_concat(typ1,typ2) $ t1 $ t2
  }
  object Variable_Concat {
    def unapply(term: Term): Option[(Term,Term)] = term match {
      case App(App(Const(c.variable_concat,_), vt1), vt2) => Some((vt1,vt2))
      case _ => None
    }
  }

  def true_expression: Const = Const(c.true_expression, expressionT(boolT) -->: boolT)
  object True_Expression {
    def unapply(term: Term): Option[Term] = term match {
      case App(Const(c.true_expression,_), t) => Some(t)
      case _ => None
    }
  }

  object OfType {
    def unapply(t: Term): Some[Typ] = Some(t.fastType)
  }

  val realT: Type = Type(t.real)
  val stringT: Type = listT(Type(t.char))
  val program_stateT: Type = Type(t.program_state)
  val probability: Const = Const(c.probability, expressionT(boolT) -->: programT -->: program_stateT -->: realT)




  def mk_eq(a: Term, b: Term): Term = {
    val typ = a.fastType
    Const(c.eq, typ -->: typ -->: boolT) $ a $ b
  }

  /** Analogous to Isabelle's HOLogic.dest_list. Throws [[scala.MatchError]] if it's not a list */
  def dest_list(term: Term): List[Term] = term match {
    case Const(c.Nil, _) => Nil
    case App(App(Const(c.Cons, _), t), u) => t :: dest_list(u)
    case _ => throw new MatchError(term)
  }

  /** Analogous to Isabelle's HOLogic.dest_numeral. Throws [[scala.MatchError]] if it's not a numeral */
  def dest_numeral(term: Term): BigInt = term match {
    case Const(c.numOne, _) => 1
    case App(Const(c.numBit0, _), bs) => 2 * dest_numeral(bs)
    case App(Const(c.numBit1, _), bs) => 2 * dest_numeral(bs) + 1
    case _ => throw new MatchError(term)
  }

  /** Analogous to Isabelle's HOLogic.dest_bit. Throws [[scala.MatchError]] if it's not a char */
  def dest_bit(term: Term): Int = term match {
    case True_const => 1
    case False_const => 0
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

  /** Analogous to Isabelle's HOLogic.dest_char. Throws [[scala.MatchError]] if it's not a char */
  def dest_char(term: Term): Char = term match {
    case App(App(App(App(App(App(App(App(Const(c.Char, _), b0), b1), b2), b3), b4), b5), b6), b7) =>
      dest_bits(b0, b1, b2, b3, b4, b5, b6, b7).toChar
    case _ => throw new MatchError(term)
  }

  /** Analogous to Isabelle's HOLogic.dest_string. Throws [[scala.MatchError]] if it's not a string */
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
    val fv = Set.newBuilder[String]

    def collect(t: Term): Unit = t match {
      case Free(v, _) => fv += v
      case Const(_, _) | Bound(_) | Var(_, _, _) =>
      case App(t1, t2) => collect(t1); collect(t2)
      case Abs(_, _, body) => collect(body)
    }

    collect(term)
    fv.result()
  }


  def quantum_equality_full(typLeft : Typ, typRight : Typ, typZ : Typ): Const =
    Const(IsabelleConsts.quantum_equality_full,  l2boundedT(typLeft,typZ) -->: variablesT(typLeft) -->: l2boundedT(typRight,typZ) -->: variablesT(typRight) -->: predicateT)
  def quantum_equality(q: Term, r: Term): Term = {
    val typQ = q.fastType
    assert(typQ == r.fastType)
    val typ = VariablesT.unapply(typQ).get
    val id = idOp(ell2T(typ))
    quantum_equality_full(typ, typ, typ) $ id $ q $ id $ r
  }
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

  def funT(domain: Typ, range: Typ): Type = Type("fun", domain, range)

  //noinspection TypeAnnotation
  object Ops {
    import MLValue.{compileFunction, compileValue, compileValueRaw}
    Thm.init()

    val qrhl_ops = Theory("QRHL.QRHL_Operations").importMLStructureNow("QRHL_Operations")

    val dependenciesOfTheory =
      MLValue.compileFunction[Theory, List[Path]](s"map_filter $qrhl_ops.local_thy_file o Theory.ancestors_of")
    if (Version.versionString != "Isabelle"+version)
      throw UserException(s"Expected Isabelle $version but got ${Version.versionString}")
    val conseq_qrhl_cardinality_condition =
      MLValue.compileFunction[Context, List[(String,Typ)], List[(String,Typ)], Term](s"$qrhl_ops.conseq_qrhl_cardinality_condition")
    val conseq_qrhl_replace_in_predicate =
      MLValue.compileFunction[Term, List[(String,Typ)], List[(String,Typ)], List[(String,Typ)], List[(String,Typ)], (Term, Term)](
        s"$qrhl_ops.conseq_qrhl_replace_in_predicate")
    val declare_abstract_program_op =
      compileFunction[Context,String,List[(String,Typ)],List[(String,Typ)],List[(String,Typ)],Int, Context](
        s"$qrhl_ops.declare_abstract_program")
    val decodeFromExpressionOp =
      MLValue.compileFunction[Context,Term, Term](s"$qrhl_ops.expression_to_term")
    val termToExpressionOp =
      MLValue.compileFunction[Context, Term, Term](s"$qrhl_ops.term_to_expression")
    val byQRHLPreOp =
      MLValue.compileFunction[List[(String, String, Typ)], List[(String, String, Typ)], Term](s"$qrhl_ops.byQRHLPre")
    val addIndexToExpressionOp =
      MLValue.compileFunction[Term, Boolean, Term](s"$qrhl_ops.add_index_to_expression")
    val fixTacOp =
      MLValue.compileFunction[Term, String, (Term, Typ)](s"$qrhl_ops.fixTac")
    val debugOp =
      MLValue.compileFunction[Context, String](s"$qrhl_ops.debug")

    lazy val makeQrhlSubgoal =
      MLValue.compileFunction[List[Statement], List[Statement], Term, Term, List[Term], Subgoal](s"$qrhl_ops.makeQrhlSubgoal")
    lazy val makeAmbientSubgoal =
      MLValue.compileFunction[Term, Subgoal](s"$qrhl_ops.Subgoal_Ambient")
    lazy val isQrhlSubgoal =
      MLValue.compileFunction[Subgoal, Boolean](s"fn $qrhl_ops.Subgoal_QRHL _ => true | _ => false")
    lazy val destQrhlSubgoal =
      MLValue.compileFunction[Subgoal, (List[Statement], List[Statement], Term, Term, List[Term])](s"$qrhl_ops.destQrhlSubgoal")
    lazy val destAmbientSubgoal =
      compileFunction[Subgoal, Term](s"fn $qrhl_ops.Subgoal_Ambient t => t")

    val swapOp =
      MLValue.compileFunction[Context, Term, Term](s"$qrhl_ops.swap_variables_conv")
    val colocalityOp =
      MLValue.compileFunction[Term, List[(String, Typ)], Term](s"$qrhl_ops.colocal_pred_qvars")
    val isInfinite_op =
      MLValue.compileFunction[Context, Typ, Boolean](s"$qrhl_ops.is_finite")
    val declare_quantum_variable =
      MLValue.compileFunction[String, Typ, Context, Context](s"$qrhl_ops.declare_quantum_variable")
    val declare_classical_variable =
      MLValue.compileFunction[String, Typ, Context, Context](s"$qrhl_ops.declare_classical_variable")
    // left:Block, right:Block, pre:RichTerm, post:RichTerm, assumptions:List[RichTerm]
    lazy val qrhl_subgoal_to_term_op =
      MLValue.compileFunction[Context, List[Statement], List[Statement], Term, Term, List[Term], Term](s"$qrhl_ops.qrhl_subgoal_to_term")

    lazy val declare_concrete_program_op =
      MLValue.compileFunction[Context, String, List[(String,Typ)], List[(String,Typ)], List[(String,Typ)], List[String], Statement, Context](
        s"$qrhl_ops.declare_concrete_program")

    val show_oracles_lines_op =
      MLValue.compileFunction[Thm, List[String]](s"$qrhl_ops.show_oracles_lines")

    lazy val statement_to_term_op =
      MLValue.compileFunction[Context, Statement, Term](s"fn (ctxt,st) => $qrhl_ops.statement_to_term ctxt st")
    lazy val statements_to_term_op =
      MLValue.compileFunction[Context, List[Statement], Term](s"fn (ctxt,st) => $qrhl_ops.statements_to_term ctxt st")
    lazy val listToBlock =
      MLValue.compileFunction[List[Statement], Statement](s"$qrhl_ops.Block")
    lazy val makeLocal =
      MLValue.compileFunction[VarTerm[(String,Typ)], VarTerm[(String,Typ)], List[Statement], Statement](s"$qrhl_ops.Local")
    lazy val makeAssign =
      MLValue.compileFunction[VarTerm[(String,Typ)], Term, Statement](s"$qrhl_ops.Assign")
    lazy val makeSample =
      MLValue.compileFunction[VarTerm[(String,Typ)], Term, Statement](s"$qrhl_ops.Sample")
    lazy val makeIfThenElse =
      MLValue.compileFunction[Term, List[Statement], List[Statement], Statement](s"$qrhl_ops.IfThenElse")
    lazy val makeQApply =
      MLValue.compileFunction[VarTerm[(String,Typ)], Term, Statement](s"$qrhl_ops.QApply")
    lazy val makeQInit =
      MLValue.compileFunction[VarTerm[(String,Typ)], Term, Statement](s"$qrhl_ops.QInit")
    lazy val makeWhile =
      MLValue.compileFunction[Term, List[Statement], Statement](s"$qrhl_ops.While")
    lazy val makeCALL =
      MLValue.compileFunction[String, List[Call], Call](s"$qrhl_ops.CALL")
    lazy val destCALL =
      MLValue.compileFunction[Call, (String, List[Call])](s"fn $qrhl_ops.CALL x => x")
    lazy val makeCall =
      MLValue.compileFunction[Call, Statement](s"$qrhl_ops.Call")
    lazy val makeMeasurement =
      MLValue.compileFunction[VarTerm[(String,Typ)], VarTerm[(String,Typ)], Term, Statement](s"$qrhl_ops.Measurement")
    lazy val whatStatementOp =
      MLValue.compileFunction[Statement, String](s"$qrhl_ops.whatStatement")
    lazy val destMeasurement =
      MLValue.compileFunction[Statement, (VarTerm[(String,Typ)], VarTerm[(String,Typ)], Term)](s"fn $qrhl_ops.Measurement x => x")
    lazy val destBlock =
      MLValue.compileFunction[Statement, List[Statement]](s"fn $qrhl_ops.Block x => x")
    lazy val destLocal =
      MLValue.compileFunction[Statement, (VarTerm[(String,Typ)], VarTerm[(String,Typ)],List[Statement])](
        s"fn $qrhl_ops.Local x => x")
    lazy val destAssign =
      MLValue.compileFunction[Statement, (VarTerm[(String,Typ)],Term)](s"fn $qrhl_ops.Assign x => x")
    lazy val destSample =
      MLValue.compileFunction[Statement, (VarTerm[(String,Typ)],Term)](s"fn $qrhl_ops.Sample x => x")
    lazy val destIfThenElse =
      MLValue.compileFunction[Statement, (Term,List[Statement],List[Statement])](s"fn $qrhl_ops.IfThenElse x => x")
    lazy val destQApply =
      MLValue.compileFunction[Statement, (VarTerm[(String,Typ)],Term)](s"fn $qrhl_ops.QApply x => x")
    lazy val destQInit =
      MLValue.compileFunction[Statement, (VarTerm[(String,Typ)],Term)](s"fn $qrhl_ops.QInit x => x")
    lazy val destWhile =
      MLValue.compileFunction[Statement, (Term,List[Statement])](s"fn $qrhl_ops.While x => x")
    lazy val destCall =
      MLValue.compileFunction[Statement, Call](s"fn $qrhl_ops.Call x => x")

    lazy private val whatVartermOp_ =
      MLValue.compileFunction[VarTerm[MLValue[Nothing]], String](s"$qrhl_ops.whatVarterm")
    def whatVartermOp[A] = whatVartermOp_.asInstanceOf[MLFunction[VarTerm[MLValue[A]], String]]
    private lazy val destVartermCons_ =
      MLValue.compileFunction[VarTerm[MLValue[Nothing]], (VarTerm[MLValue[Nothing]], VarTerm[MLValue[Nothing]])](s"fn $qrhl_ops.VTCons x => x")
    def destVartermCons[A] = destVartermCons_.asInstanceOf[MLFunction[VarTerm[MLValue[A]], (VarTerm[MLValue[A]], VarTerm[MLValue[A]])]]
    private lazy val destVartermSingle_ =
      MLValue.compileFunction[VarTerm[MLValue[Nothing]], MLValue[Nothing]](s"fn $qrhl_ops.VTSingle x => x")
    def destVartermSingle[A] = destVartermSingle_.asInstanceOf[MLFunction[VarTerm[MLValue[A]], MLValue[A]]]
    private lazy val vartermUnit_ =
      MLValue.compileValueRaw[VarTerm[Nothing]](s"$qrhl_ops.E_Varterm $qrhl_ops.VTUnit")
    def vartermUnit[A] = vartermUnit_.asInstanceOf[MLValue[VarTerm[A]]]
    private lazy val vartermCons_ =
      MLValue.compileFunction[VarTerm[MLValue[Nothing]], VarTerm[MLValue[Nothing]], VarTerm[MLValue[Nothing]]](s"$qrhl_ops.VTCons")
    def vartermCons[A] = vartermCons_.asInstanceOf[MLFunction2[VarTerm[MLValue[A]],VarTerm[MLValue[A]], VarTerm[MLValue[A]]]]
    private lazy val vartermSingle_ =
      MLValue.compileFunction[MLValue[Nothing], VarTerm[MLValue[Nothing]]](s"$qrhl_ops.VTSingle")
    def vartermSingle[A] = vartermSingle_.asInstanceOf[MLFunction[MLValue[A], VarTerm[MLValue[A]]]]

    val checkTypeOp =
      MLValue.compileFunction[(Context, Term), Typ](s"fn (ctxt,t) => $qrhl_ops.checkType ctxt t")
//    val createContextOp =
//      MLValue.compileFunction[List[String], (Context, List[String])]("QRHL_Operations.create_context")
    val addAssumptionOp =
      MLValue.compileFunction[(String, Term, Context), Context](s"$qrhl_ops.addAssumption")
    val simplifyTermOp =
      MLValue.compileFunction[(Term, List[String], Context), (Term, Thm)](s"$qrhl_ops.simp")
    val declareVariableOp =
      MLValue.compileFunction[(Context, String, Typ), Context](s"$qrhl_ops.declare_variable")
    lazy val thms_as_subgoals =
      MLValue.compileFunction[(Context, String), List[Subgoal]](s"$qrhl_ops.thms_as_subgoals")
//    val use_thy_op =
//      MLValue.compileFunction[String, Unit]("Thy_Info.use_thy")
    lazy val applyToplevelCommand = MLValue.compileFunction[Context, String, Context](s"$qrhl_ops.applyToplevelCommand")
    val absfree = MLValue.compileFunction[String, Typ, Term, Term]("fn (name,typ,term) => absfree (name, typ) term")

    val compareTyps = MLValue.compileFunction[Typ, Typ, Int](s"fn (t,u) => case Term_Ord.typ_ord (t,u) of LESS => ~1 | GREATER => 1 | EQUALS => 0")
  }
}

object IsabelleX {
  val version = "2022-RC0"

  private var globalIsabellePeek: IsabelleX = _
  lazy val globalIsabelle: IsabelleX = {
    if (globalIsabellePeek==null) {
      // To avoid this error, make sure globalIsabelleWith is invoked first. This, in turn is invoked by
      // State.loadIsabelle, this when Toplevel processes an IsabelleCommand ("isabelle.")
      throw new IllegalStateException("Internal error: Accessed the Isabelle instance before it was initialized.")
    }
    globalIsabellePeek
  }
  def globalIsabelleWith(sessionDir : Option[Path], session: Option[String]): IsabelleX = synchronized {
    var setup = defaultSetup
    logger.debug(s"Initializing IsabelleX with sessionDir=$sessionDir, session=$session")
    sessionDir.foreach { dir => setup = setup.copy(sessionRoots = setup.sessionRoots.appended(dir)) }
    session.foreach { l => setup = setup.copy(logic = l) }
    if (globalIsabellePeek != null) {
      if (globalIsabellePeek.setup != setup)
        throw UserException(
          """Cannot reinitialize the Isabelle process.
            |(This happens when the 'isabelle` command is is invoked with a different session name or in a different directory without restarting the qrhl-tool.
            |Restart the qrhl-tool to get rid of this (C-c C-x in ProofGeneral.)""".stripMargin)
      globalIsabellePeek
    } else {
      globalIsabellePeek = new IsabelleX(setup)
      globalIsabellePeek
    }
  }

  def isGlobalIsabelle(isabelle: IsabelleX): Boolean =
    (globalIsabellePeek != null) && (globalIsabelle == isabelle)

  @deprecated("use RichTerm.toString", "now")
  def pretty(t: Term): String = IsabelleX.theContext.prettyExpression(t)

  def pretty(t: Typ): String = IsabelleX.theContext.prettyTyp(t)

  private val logger = log4s.getLogger

  val symbols = new Symbols(
    processSubSuper = ProcessSubSuperMode.ToIsabelle,
    extraSymbolsLowPri = List(
      // Own additions (because Emacs's TeX input method produces these chars):
      "lbrakk" -> 0x301A, "rbrakk" -> 0x301B)
      // We do not include "cdot" -> 0xB7, because Isabelle maps 0xB7 to sqdot, and we do not want to conflict with that
  )

  private var _theContext: ContextX = _
  def theContext: ContextX = _theContext

  class ContextX(val isabelle: IsabelleX, val context: Context) extends FutureValue {
    override def await: Unit = context.await
    // We initialize the global _theContext with this context inside this future.
    // This guarantees that the present context will only be used if it succeeds.
    // (Meaning, if the future inside `context` succeeds.
    override val someFuture: Future[Any] = context.someFuture.map { _ =>
      _theContext = this;
      isabelleControl.exceptionManager.asInstanceOf[Exn.ExceptionManager].setContext(context)
    }

    private implicit val isabelleControl: Isabelle = isabelle.isabelleControl
    import isabelle.Ops._

    // Make sure not to return from the constructor unless _theContext is initialized (or until this context is known to have failed)
    if (_theContext == null)
      Await.ready(someFuture, Duration.Inf)

    def checkType(term: Term): Typ =
      checkTypeOp(MLValue(context,term)).retrieveNow

    def declareVariable(name: String, isabelleTyp: Typ): ContextX = {
      val ctxt = declareVariableOp(MLValue((context, name, isabelleTyp))).retrieveNow
      new ContextX(isabelle, ctxt)
    }

    def addAssumption(name: String, assumption: Term): ContextX = {
      val ctxt = addAssumptionOp(
        MLValue((name, assumption, context))).retrieveNow
      new ContextX(isabelle, ctxt)
    }

    def map(f: Context => Context): ContextX =
      new ContextX(isabelle, f(context))

    @deprecated("Use Expression.read", "now")
    def readTerm(str: String, typ: Typ): Term =
      Term(context, str, typ)

    @deprecated("Use Expression.toString", "now")
    def prettyExpression(term: Term): String =
      symbols.symbolsToUnicode(term.prettyRaw(context))

    def readTyp(str: String): Typ = Typ(context, str).force

    def readTypUnicode(str: String): Typ =
      try readTyp(symbols.unicodeToSymbols(str))
      catch {
        case NestedException(e : Exn)
          if (e.message.startsWith("Undefined type name:")
            || e.message.startsWith("Inner syntax error")) =>
          throw UserException(s"""While parsing type "$str": ${e.message}""")
      }


  def prettyTyp(typ: Typ): String = symbols.symbolsToUnicode(typ.prettyRaw(context))

    def simplify(term: Term, facts: List[String])(implicit executionContext: ExecutionContext): (RichTerm, Thm) = {
      val global = null
      val (t,thm) = simplifyTermOp(MLValue((term, facts.map(symbols.unicodeToSymbols(_)), context))).retrieveNow
      (RichTerm(t), thm)
    }
  }

  lazy val defaultSetup: Isabelle.Setup = Isabelle.Setup(
    workingDirectory = Configuration.distributionDirectory,
    isabelleHome = Configuration.isabelleHome,
    logic = "QRHL",
    sessionRoots = List(Paths.get("isabelle-thys")) ++ Configuration.afpRoot.map(_.resolve("thys")),
    verbose = true,
    exceptionManager = new Exn.ExceptionManager(_)
//    /** Must end in .isabelle if provided */
//    userDir = Some(Configuration.isabelleUserDir)
  )
}
