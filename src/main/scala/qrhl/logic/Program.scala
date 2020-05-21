package qrhl.logic

import info.hupel.isabelle.api.XML
import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.Typ
import info.hupel.isabelle.{Codec, Operation, XMLResult, pure}
import qrhl.isabelle.Isabelle.Thm
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.{AllSet, MaybeAllSet, UserException, Utils}

import scala.annotation.tailrec
import scala.collection.immutable.ListSet
import scala.collection.mutable.ListBuffer
import scala.collection.{AbstractIterator, GenSet, mutable}
import scala.language.higherKinds

// Implicits
import qrhl.isabelle.RichTerm.{term_tight_codec, typ_tight_codec}
import qrhl.logic.Statement.codec
import qrhl.Utils.listSetUpcast
import qrhl.Utils.ListSetUtils

sealed trait VarTerm[+A] {
  def replace[A1 >: A, A2 >: A](from: A1, to: A2): VarTerm[A2]

  def contains[A1 >: A](v: A1): Boolean

  def areDistinct: Boolean = Utils.areDistinct(this.iterator)

  def toList: List[A] = iterator.toList
  def toSeq: Seq[A] = iterator.toSeq
  def map[B](f:A=>B) : VarTerm[B]
  /** Not thread safe */
  def iterator: Iterator[A] = new AbstractIterator[A] {
    private var stack : List[VarTerm[A]] = List(VarTerm.this)
    /** Has the additional side effect of making sure that [stack.head] is a VTSingle if it exists */
    @tailrec override def hasNext: Boolean = stack match {
      case Nil => false
      case (_:VTUnit.type)::_ => // pattern VTUnit::_ leads to an implicit equality check, which calls the iterator!?
        stack = stack.tail
        hasNext
      case VTCons(a,b)::_ =>
        stack = a::b::stack.tail
        hasNext
      case VTSingle(_)::_ => true
    }

    override def next(): A =
      if (hasNext) { val result = stack.head.asInstanceOf[VTSingle[A]].v; stack = stack.tail; result }
      else throw new RuntimeException("Iterator.next called on empty iterator")
  }
}
object VarTerm {
  def varlist[A](elems: A*) : VarTerm[A] = {
    var result : VarTerm[A] = VTUnit
    for (e <- elems.reverseIterator) {
      result = result match {
        case VTUnit => VTSingle(e)
        case _ => VTCons(VTSingle(e),result)
      }
    }
    result
  }


  val codecString = new codec[String](new Codec[String] {
    override val mlType: String = "string"
    override def encode(t: String): XML.Tree = XML.Text(t)
    override def decode(tree: XML.Tree): XMLResult[String] = tree match {
      case XML.Text(s) => Right(s)
      case _ => Left(("Expected XML.Text",List(tree)))
    }
  })

  val codecC = new codec[CVariable](CVariable.codec)
  val codecQ = new codec[QVariable](QVariable.codec)

  class codec[A](vCodec : Codec[A]) extends Codec[VarTerm[A]] {
    override lazy val mlType: String = vCodec.mlType + " tree"
    override def encode(t: VarTerm[A]): XML.Tree = t match {
      case VTUnit => XML.Elem(("u",Nil),Nil)
      case VTCons(a,b) => XML.Elem(("c",Nil),List(encode(a),encode(b)))
      case VTSingle(v) => XML.Elem(("s",Nil),List(vCodec.encode(v)))
    }

    override def decode(xml: XML.Tree): XMLResult[VarTerm[A]] = xml match {
      case XML.Elem(("c",Nil),List(aXml,bXml)) =>
        for (a <- decode(aXml);
             b <- decode(bXml))
          yield VTCons(a,b)
      case XML.Elem(("s",Nil),List(v)) =>
        for (vv <- vCodec.decode(v))
          yield VTSingle(vv)
      case XML.Elem(("u",Nil),Nil) => Right(VTUnit)
      case _ => Left(("No a valid varterm",List(xml)))
    }
  }
}

case class ExprVariableUse
(
  program : ListSet[Variable],
  ambient : ListSet[String]
) {
  @deprecated def classical : ListSet[CVariable] = Variable.classical(program)
  @deprecated def quantum : ListSet[QVariable] = Variable.quantum(program)
}

case class VariableUse
(
  /** Free variables (upper bound) */
  freeVariables : ListSet[Variable],
  /** All written variables (upper bound) */
  written : ListSet[Variable],
  /** All ambient variables (upper bound) */
  ambient : ListSet[String],
  /** All included programs */
  programs : ListSet[ProgramDecl],
  /** All variables that are overwritten (lower bound).
    * That is, their initial value is never used, and they will be overwritten with a value
    * independent of their initial value. */
  overwritten : ListSet[Variable],
  /** All oracles used by this program (upper bound) */
  oracles : ListSet[String],
  /** Local variables that have an oracle call in their scope (upper bound). */
  inner: ListSet[Variable],
  /** Covered variables: A variable is covered if it is declared local above every hole (lower bound) */
  covered: MaybeAllSet[Variable]
) {
  assert(oracles.isEmpty == covered.isAll, (oracles, covered))

  def isProgram: Boolean = oracles.isEmpty

  @deprecated def classical: ListSet[CVariable] = freeVariables collect { case v : CVariable => v }
  @deprecated def quantum: ListSet[QVariable] = freeVariables collect { case v : QVariable => v }
  @deprecated def overwrittenClassical : ListSet[CVariable] = overwritten collect { case v : CVariable => v }
  @deprecated def overwrittenQuantum : ListSet[QVariable] = overwritten collect { case v : QVariable => v }
  @deprecated def innerClassical : ListSet[CVariable] = inner collect { case v : CVariable => v }
  @deprecated def innerQuantum : ListSet[QVariable] = inner collect { case v : QVariable => v }
  @deprecated def writtenClassical : ListSet[CVariable] = written collect { case v : CVariable => v }

  override def toString: String = s"""
      | Free        ⊆ ${freeVariables.map(_.name).mkString(", ")}
      | Ambient     ⊆ ${ambient.mkString(", ")}
      | Programs    = ${programs.map(_.name).mkString(", ")}
      | Written     ⊆ ${written.map(_.name).mkString(", ")}
      | Overwritten ⊇ ${overwritten.map(_.name).mkString(", ")}
      | Inner       ⊆ ${inner.map(_.name).mkString(", ")}
      | Covered     ⊇ ${if (covered.isAll) "all variables" else covered.map(_.name).mkString(", ")}
      | Oracles     ⊆ ${oracles.mkString(", ")}
    """.stripMargin

//  def addFreeVariable(variables: Variable*): VariableUse = copy(freeVariables +++ variables)
//  def addAmbientVar(variables: String*): VariableUse = copy(ambient=ambient +++ variables)
//  def addProgramVar(p: ProgramDecl*): VariableUse = copy(programs=programs +++ p)

/*  def +++(other: VariableUse): VariableUse = VariableUse(
    freeVariables=freeVariables+++other.freeVariables,
    written=written+++other.written,
    ambient=ambient+++other.ambient,
    programs=programs+++other.programs,
    overwritten = overwritten+++other.overwritten,
    oracles = oracles+++other.oracles,
    inner = inner+++other.inner)*/

  //noinspection MutatorLikeMethodIsParameterless
//  def removeOverwritten: VariableUse = copy(overwritten=ListSet.empty)
//  def removeOverwrittenClassical(vars: CVariable*): VariableUse = copy(overwritten=overwritten -- vars)
//  def removeOverwrittenQuantum(vars: QVariable*): VariableUse = copy(overwritten=overwritten -- vars)

}
object VariableUse {
  // TODO get rid of most (all?) of the helper functions

/*  def oracle(oracles: String*): VariableUse =
    new VariableUse(freeVariables=emptySet, ambient=emptySet, programs=emptySet, written=emptySet,
      overwritten = emptySet, oracles=ListSet(oracles:_*),
      inner = emptySet)*/


  private val emptySet = ListSet.empty[Nothing]

/*  def overwrittenClassicalVariables(variables: CVariable*): VariableUse = {
    val vars = ListSet(variables: _*)
    new VariableUse(freeVariables = vars, written = vars,
      ambient = emptySet, programs = emptySet,
      overwritten = vars, oracles=emptySet,
      inner = emptySet)
  }*/

/*  def quantumVariables(vs: QVariable*): VariableUse =
    new VariableUse(freeVariables=ListSet(vs:_*), ambient=emptySet, programs=emptySet, written=emptySet,
      overwritten = emptySet, oracles=emptySet,
      inner = emptySet)*/

/*
  def overwrittenQuantumVariables(vs: QVariable*): VariableUse = {
    val vars = ListSet(vs:_*)
    new VariableUse(freeVariables=vars, ambient=emptySet, programs=emptySet, written=emptySet,
      overwritten = vars, oracles=emptySet,
      inner = emptySet)
  }
*/

  val empty = new VariableUse(freeVariables=emptySet, written=emptySet, ambient=emptySet, programs=emptySet,
    overwritten = emptySet, oracles=emptySet,
    inner = emptySet, covered = MaybeAllSet.empty)
}

case object VTUnit extends VarTerm[Nothing] {
  override def map[B](f: Nothing => B): VTUnit.type = VTUnit
  override def iterator: Iterator[Nothing] = Iterator.empty
  override def toString: String = "()"
  override def replace[A1 >: Nothing, A2 >: Nothing](from: A1, to: A2): VarTerm[A2] = this
  override def contains[A1 >: Nothing](v: A1): Boolean = false
}

case class VTSingle[+A](v:A) extends VarTerm[A] {
  override def map[B](f: A => B): VarTerm[B] = VTSingle(f(v))
  override def iterator: Iterator[A] = Iterator.single(v)
  override def toString: String = v.toString

  override def replace[A1 >: A, A2 >: A](from: A1, to: A2): VarTerm[A2] =
    if (this.v == from)
      VTSingle(to)
    else if (this.v == to)
      throw UserException(s"Trying to replace $from to $to, but $to is already in use")
    else
      this

  override def contains[A1 >: A](v: A1): Boolean = this.v == v
}
case class VTCons[+A](a:VarTerm[A], b:VarTerm[A]) extends VarTerm[A] {
  assert(a!=null)
  assert(b!=null)
  override def map[B](f: A => B): VarTerm[B] = VTCons(a.map(f),b.map(f))
  override def toString: String = s"(${a.toString},${b.toString})"

  override def replace[A1 >: A, A2 >: A](from: A1, to: A2): VarTerm[A2] =
    VTCons(a.replace(from, to), b.replace(from, to))

  override def contains[A1 >: A](v: A1): Boolean =
    a.contains(v) || b.contains(v)
}

// Programs
sealed trait Statement {
  def toSeq: Seq[Statement] = this match {
    case Block(statements @ _*) => statements
    case _ => List(this)
  }

  def renameQVariable(env: Environment, from: QVariable, to: QVariable) : Statement
  def renameCVariable(env: Environment, from: CVariable, to: CVariable) : Statement

  def substituteOracles(subst: Map[String, Call]) : Statement

  def simplify(isabelle: Isabelle.Context, facts: List[String], thms:ListBuffer[Thm]): Statement

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  def markOracles(oracles: List[String]): Statement

  /** Converts this statement into a block by wrapping it in Block() if necessary */
  def toBlock: Block = Block(this)

//  @deprecated("too slow, use programTerm instead","now")
//  def programTermOLD(context: Isabelle.Context) : Term

  def programTerm(context: Isabelle.Context): RichTerm = {
    context.isabelle.invoke(Statement.statement_to_term_op, (context.contextId, this))
  }

//  private def mergeSequential(a: VariableUse, b: VariableUse) : VariableUse = {
//    val result =
//      if (a.oracles.isEmpty)
//        a +++ b.removeOverwrittenClassical(a.classical.toSeq:_*).removeOverwrittenQuantum(a.quantum.toSeq:_*)
//      else
//        a +++ b.removeOverwritten
//    result
//  }
//  private def mergeAlternative(a: VariableUse, b: VariableUse) : VariableUse = {
//    val ab = a +++ b
//    ab.copy(overwritten = a.overwritten.intersect(b.overwritten))
//  }

  private val emptySet = ListSet.empty
  val variableUse : Environment => VariableUse = Utils.singleMemo { env =>
    this match {
      case Local(vars, body) =>
        val bodyVars = body.variableUse(env)
        val isProgram = bodyVars.oracles.isEmpty
        new VariableUse(
          freeVariables = bodyVars.freeVariables -- vars,
          written = bodyVars.written -- vars,
          ambient = bodyVars.ambient,
          programs = bodyVars.programs,
          overwritten = bodyVars.overwritten -- vars,
          oracles = bodyVars.oracles,
          inner = if (isProgram) emptySet; else ListSet(vars:_*) +++ bodyVars.inner,
          covered = bodyVars.covered ++ vars
        )
      case Block() =>
        // This is "skip"
        new VariableUse(
          freeVariables = emptySet,
          written = emptySet,
          ambient = emptySet,
          programs = emptySet,
          overwritten = emptySet,
          oracles = emptySet,
          inner = emptySet,
          covered = MaybeAllSet.all
        )
      case Block(s, ss@_*) =>
        val sVars = s.variableUse(env)
        val ssVars = Block(ss:_*).variableUse(env)
        new VariableUse(
          freeVariables = sVars.freeVariables +++ ssVars.freeVariables,
          written = sVars.written +++ ssVars.written,
          ambient = sVars.ambient +++ ssVars.ambient,
          programs = sVars.programs +++ ssVars.programs,
          overwritten = sVars.overwritten +++ ((ssVars.overwritten -- sVars.freeVariables).intersect(sVars.covered)),
          oracles = sVars.oracles +++ ssVars.oracles,
          inner = sVars.inner +++ ssVars.inner,
          covered = sVars.covered.intersect(ssVars.covered)
        )
      case Sample(v, e) =>
        // Hack for simply doing the same as in Assign case
        Assign(v, e).variableUse(env)
      case Assign(v, e) =>
        // Also handling Sample(v,e)
        val vSet = ListSet(v.toSeq :_*)
        val fvE = e.caVariables(env)
        new VariableUse(
          freeVariables = vSet +++ fvE.classical,
          written = vSet,
          ambient = fvE.ambient,
          programs = emptySet,
          overwritten = vSet -- fvE.classical,
          oracles = emptySet,
          inner = emptySet,
          covered = MaybeAllSet.all
        )
      case Call(name, args@_*) =>
        if (name.head != '@') {
          // Call(name, args@_*) is an application C[a1,...,an] where C is referenced by name, and args=(a1,...,an)
          // TODO: As an alternative to the stuff below, we instantiate this call and then compute the variables
          // that would give a tighter estimate
          val progDecl = env.programs(name)
          val progVars = progDecl.variablesRecursive
          val argVars = args map ( _.variableUse(env) )
          val oracles = argVars.foldLeft(emptySet : ListSet[String]) { _ +++ _.oracles }
          val isProgram = oracles.isEmpty
          new VariableUse(
            // By Helping_Lemmas.fv_subst' (note that freeVariables is an upper bound)
            freeVariables = progVars.freeVariables ++
              MaybeAllSet.subtract(argVars.foldLeft[ListSet[Variable]](emptySet) { _ +++ _.freeVariables }, progVars.covered),
            // By Helping_Lemmas.fv_written' (note that freeVariables is an upper bound)
            written = argVars.foldLeft(progVars.written) { _ +++ _.written },
            ambient = argVars.foldLeft(progVars.ambient) { _ +++ _.ambient },
            programs = argVars.foldLeft(progVars.programs + progDecl) { _ +++ _.programs },
            // By Helping_Lemmas.overwr_subst (note that overwritten is a lower bound)
            overwritten = progVars.overwritten,
            oracles = oracles,
            // By Helping_Lemmas.program_inner and .inner_subst (note that inner is an upper bound)
            inner = if (isProgram) emptySet else
                    argVars.foldLeft(progVars.inner) { _ +++ _.inner },
            // By Helping_Lemmas.program_covered and .covered_subst (note that covered is a lower bound)
            covered = if (isProgram) MaybeAllSet.all[Variable]
            else if (progVars.covered.isAll) MaybeAllSet.all // shortcut for the next line
            else progVars.covered ++ argVars.foldLeft[MaybeAllSet[Variable]]
              (MaybeAllSet.all) { (cov,a) => cov.intersect(a.covered) }
          )
        } else {
          assert(args.isEmpty)
          // The current program is a hole
          new VariableUse(
            freeVariables = emptySet,
            written = emptySet,
            ambient = emptySet,
            programs = emptySet,
            overwritten = emptySet,
            oracles = ListSet(name.tail),
            inner = emptySet,
            covered = MaybeAllSet.empty
          )
        }
      case While(e, body) =>
        val fvE = e.caVariables(env)
        val bodyVars = body.variableUse(env)
        new VariableUse(
          freeVariables = fvE.classical +++ bodyVars.freeVariables,
          written = bodyVars.written,
          ambient = fvE.ambient +++ bodyVars.ambient,
          programs = bodyVars.programs,
          overwritten = emptySet,
          oracles = bodyVars.oracles,
          inner = bodyVars.inner,
          covered = bodyVars.covered
        )
      case IfThenElse(e, p1, p2) =>
        val fvE = e.caVariables(env)
        val p1Vars = p1.variableUse(env)
        val p2Vars = p2.variableUse(env)
        new VariableUse(
          freeVariables = fvE.classical +++ p1Vars.freeVariables +++ p2Vars.freeVariables,
          written = p1Vars.written +++ p2Vars.written,
          ambient = fvE.ambient +++ p1Vars.ambient +++ p2Vars.ambient,
          programs = p1Vars.programs +++ p2Vars.programs,
          overwritten = p1Vars.overwritten.intersect(p2Vars.overwritten) -- fvE.classical,
          oracles = p1Vars.oracles +++ p2Vars.oracles,
          inner = p1Vars.inner +++ p2Vars.inner,
          covered = p1Vars.covered.intersect(p2Vars.covered)
        )
      case QInit(q, e) =>
        val qSet = ListSet(q.toSeq :_*)
        val fvE = e.caVariables(env)
        new VariableUse(
          freeVariables = qSet +++ fvE.classical,
          written = qSet,
          ambient = fvE.ambient,
          programs = emptySet,
          overwritten = qSet,
          oracles = emptySet,
          inner = emptySet,
          covered = MaybeAllSet.all
        )
      case QApply(q, e) =>
        val qSet = ListSet(q.toSeq :_*)
        val fvE = e.caVariables(env)
        new VariableUse(
          freeVariables = qSet +++ fvE.classical,
          written = qSet,
          ambient = fvE.ambient,
          programs = emptySet,
          overwritten = emptySet,
          oracles = emptySet,
          inner = emptySet,
          covered = MaybeAllSet.all)
      case Measurement(x, q, e) =>
        val xSet = ListSet[Variable](x.toSeq :_*)
        val qSet = ListSet[Variable](q.toSeq :_*)
        val fvE = e.caVariables(env)
        new VariableUse(
          freeVariables = xSet +++ qSet +++ fvE.classical,
          written = xSet +++ qSet,
          ambient = fvE.ambient,
          programs = emptySet,
          overwritten = xSet -- fvE.classical,
          oracles = emptySet,
          inner = emptySet,
          covered = MaybeAllSet.all)
    }
  }

//  /** Returns all variables used in the statement.
//    * @param recurse Recurse into programs embedded via Call
//    * @return (cvars,wcvars,qvars,avars,pnames) Classical, quantum, ambient variables, program declarations.
//    * Oracle names (starting with @) are not included or recursed into
//    * wcvars = written classical vars
//    * */





  //  @deprecated
//  def cwqapVariables(environment: Environment, recurse: Boolean) : VariableUse[List] = {
//    val vars = VariableUse.make(PolymorphicConstant.linkedHashSet)
//    cwqapVariables(environment,vars=vars,recurse=recurse)
//    vars.map(PolymorphicFunction.linkedHashSetToList)
//  }
//
//  @deprecated
//  def cwqapVariables(environment : Environment, vars : VariableUse[mutable.Set], recurse:Boolean): Unit = {
//    def collectExpr(e:RichTerm):Unit = e.caVariables(environment,vars)
//    def collect(s:Statement) : Unit = s match {
//      case Block(ss @ _*) => ss.foreach(collect)
//      case Assign(v,e) => vars.cvars ++= v.iterator; vars.wcvars ++= v.iterator; collectExpr(e)
//      case Sample(v,e) => vars.cvars ++= v.iterator; vars.wcvars ++= v.iterator; collectExpr(e)
//      case Call(name, args @ _*) =>
//        if (name.head!='@') {
//          val p = environment.programs(name)
//          vars.progs += p
//          if (recurse) {
//            val pvars = p.variablesRecursive
//            vars.cvars ++= pvars.cvars; vars.wcvars ++= pvars.wcvars;
//            vars.qvars ++= pvars.qvars; vars.avars ++= pvars.avars; vars.progs ++= pvars.progs
//          }
//        }
//        args.foreach(collect)
//      case While(e,body) => collectExpr(e); collect(body)
//      case IfThenElse(e,p1,p2) => collectExpr(e); collect(p1); collect(p2)
//      case QInit(vs,e) => vars.qvars ++= vs.iterator; collectExpr(e)
//      case Measurement(v,vs,e) => vars.cvars ++= v.iterator; vars.wcvars ++= v.iterator; collectExpr(e); vars.qvars ++= vs.iterator
//      case QApply(vs,e) => vars.qvars ++= vs.iterator; collectExpr(e)
//    }
//    collect(this)
//  }

  @deprecated
  private def expr2VariableUse(eVars: ExprVariableUse) = {
    VariableUse.empty.copy(freeVariables = eVars.classical,
      ambient = eVars.ambient)
  }

  def checkWelltyped(context: Isabelle.Context): Unit

  /** All ambient and program variables.
    * Not including nested programs (via Call).
    * Includes local variables.
    * */
  def variablesDirect : Set[String] = {
    val vars = new mutable.SetBuilder[String,Set[String]](Set.empty)
    def collect(s:Statement) : Unit = s match {
      case Local(vars2, body) =>
        vars ++= vars2 map { _.name }
        collect(body)
      case Block(ss @ _*) => ss.foreach(collect)
      case Assign(v,e) => vars ++= v.iterator.map(_.name); vars ++= e.variables
      case Sample(v,e) => vars ++= v.iterator.map[String](_.name); vars ++= e.variables
      case Call(_, _*) =>
      case While(e,body) => vars ++= e.variables; collect(body)
      case IfThenElse(e,p1,p2) => vars ++= e.variables; collect(p1); collect(p2)
      case QInit(vs,e) => vars ++= vs.iterator.map[String](_.name); vars ++= e.variables
      case Measurement(v,vs,e) => vars ++= v.iterator.map[String](_.name); vars ++= vs.iterator.map[String](_.name); vars ++= e.variables
      case QApply(vs,e) => vars ++= vs.iterator.map[String](_.name); vars ++= e.variables
    }
    collect(this)
    vars.result
  }

  /*  /** Including nested programs (via Call). (Missing ambient variables from nested calls.) */
    def variablesAll(env:Environment) : Set[String] = {
      val vars = new mutable.SetBuilder[String,Set[String]](Set.empty)
      def collect(s:Statement) : Unit = s match {
        case Block(ss @ _*) => ss.foreach(collect)
        case Assign(v,e) => vars ++= v.iterator.map[String](_.name); vars ++= e.variables
        case Sample(v,e) => vars ++= v.iterator.map[String](_.name); vars ++= e.variables
        case Call(name, args @ _*) =>
          val (cvars,_,qvars,_,_) = env.programs(name).variablesRecursive
          vars ++= cvars.map(_.name)
          vars ++= qvars.map(_.name)
          args.foreach(collect)
        case While(e,body) => vars ++= e.variables; collect(body)
        case IfThenElse(e,p1,p2) => vars ++= e.variables; collect(p1); collect(p2)
        case QInit(vs,e) => vars ++= vs.iterator.map[String](_.name); vars ++= e.variables
        case Measurement(v,vs,e) => vars ++= v.iterator.map[String](_.name); vars ++= vs.iterator.map[String](_.name); vars ++= e.variables
        case QApply(vs,e) => vars ++= vs.iterator.map[String](_.name); vars ++= e.variables
      }
      collect(this)
      vars.result
    }*/

  def inline(name: String, oracles: List[String], program: Statement): Statement

  def unwrapBlock : Seq[Statement] = this  match {
    case Block(st @_*) => st
    case _ => List(this)
  }

}

object Statement {
/*
  def decodeFromListTerm(context: Isabelle.Context, t:Term) : Block = {
    val statements = Isabelle.dest_list(t).map(decodeFromTerm(context,_))
    Block(statements:_*)
  }
*/

/*  def decodeFromTerm(context: Isabelle.Context, t:Term) : Statement = t match {
    case App(Const(Isabelle.block.name,_), statements) => decodeFromListTerm(context, statements)
    case App(App(Const(Isabelle.assignName,_),x),e) =>
      Assign(CVariable.fromCVarList(context, x), RichTerm.decodeFromExpression(context, e))
    case App(App(Const(Isabelle.sampleName,_),x),e) =>
      Sample(CVariable.fromCVarList(context, x),RichTerm.decodeFromExpression(context, e))
    case Free(name,_) => Call(name)
    case App(App(Const(Isabelle.instantiateOracles.name,_), Free(name,_)), args) =>
      val args2 = Isabelle.dest_list(args).map(decodeFromTerm(context,_).asInstanceOf[Call])
      Call(name,args2 : _*)
    case App(App(Const(Isabelle.whileName,_),e),body) =>
      While(RichTerm.decodeFromExpression(context,e), decodeFromListTerm(context, body))
    case App(App(App(Const(Isabelle.ifthenelseName,_),e),thenBody),elseBody) =>
      IfThenElse(RichTerm.decodeFromExpression(context,e),
        decodeFromListTerm(context, thenBody), decodeFromListTerm(context, elseBody))
    case App(App(Const(Isabelle.qinitName, _), vs), e) =>
      QInit(QVariable.fromQVarList(context, vs), RichTerm.decodeFromExpression(context,e))
    case App(App(Const(Isabelle.qapplyName, _), vs), e) =>
      QApply(QVariable.fromQVarList(context, vs), RichTerm.decodeFromExpression(context,e))
    case App(App(App(Const(Isabelle.measurementName, _), x), vs), e) =>
      Measurement(CVariable.fromCVarList(context, x), QVariable.fromQVarList(context, vs),
        RichTerm.decodeFromExpression(context,e))
    case _ => throw new RuntimeException(s"term $t cannot be decoded as a statement")
  }*/

  implicit object codec extends Codec[Statement] {
    override val mlType: String = "Programs.statement"

    def encode_call(c : Call): XML.Tree = c match {
      case Call(name,args@_*) => XML.Elem(("call",List(("name",name))), args.map(encode_call).toList)
    }


    import Isabelle.applicativeXMLResult
    import scalaz._
    import std.list._
    import syntax.traverse._

    def decode_call(xml : XML.Tree): XMLResult[Call] = xml match {
      case XML.Elem(("call",List(("name",name))), argsXml) =>
        for (args <- argsXml.traverse(decode_call))
          yield Call(name, args : _*)
    }

//    def string_list_encode(l:List[String]) = XML.Elem(("l",Nil), l.map( s => Codec.string.encode(s)))
//    def string_list_decode(xml:XML.Tree): XMLResult[List[String]] = xml match {
//      case XML.Elem(("l",Nil), l) => l.traverse(Codec.string.decode)
//    }

    override def encode(t: Statement): XML.Tree = t match {
      case Local(vars, body) =>
        val qvars = vars collect { case v : QVariable => v }
        val cvars = vars collect { case v : CVariable => v }
        XML.Elem(("local", Nil),
        List(VarTerm.codecC.encode(VarTerm.varlist(cvars:_*)),
          VarTerm.codecQ.encode(VarTerm.varlist(qvars:_*)),
          encode(body)))
      case Block(stmts@_*) => XML.Elem(("block", Nil), stmts.map(encode).toList)
      case Assign(v, rhs) => XML.Elem(("assign", Nil), List(VarTerm.codecString.encode(v.map[String](_.name)), RichTerm.codec.encode(rhs)))
      case Sample(v, rhs) => XML.Elem(("sample", Nil), List(VarTerm.codecString.encode(v.map[String](_.name)), RichTerm.codec.encode(rhs)))
      case call: Call => encode_call(call)
      case Measurement(v, loc, exp) => XML.Elem(("measurement", Nil),
        List(VarTerm.codecString.encode(v.map[String](_.name)), VarTerm.codecString.encode(loc.map[String](_.name)), RichTerm.codec.encode(exp)))
      case QInit(loc, exp) => XML.Elem(("qinit", Nil),
        List(VarTerm.codecString.encode(loc.map[String](_.name)), RichTerm.codec.encode(exp)))
      case QApply(loc, exp) => XML.Elem(("qapply", Nil),
        List(VarTerm.codecString.encode(loc.map[String](_.name)), RichTerm.codec.encode(exp)))
      case IfThenElse(e, p1, p2) => XML.Elem(("ifte", Nil),
        List(RichTerm.codec.encode(e), encode(p1), encode(p2)))
      case While(e, p1) => XML.Elem(("while", Nil),
        List(RichTerm.codec.encode(e), encode(p1)))
    }

//    def mk_cvar_list(names : List[String], typ : Typ) : List[CVariable] = names match {
//      case Nil =>
//        assert(typ == Isabelle.unitT)
//        Nil
//      case List(x) =>
//        List(CVariable(x,typ))
//      case x::xs =>
//        val (xT,xsT) = Isabelle.dest_prodT(typ)
//        CVariable(x,xT) :: mk_cvar_list(xs, xsT)
//    }

    def mk_cvar_term(names : VarTerm[String], typ : Typ) : VarTerm[CVariable] = names match {
      case VTUnit =>
        assert(typ == Isabelle.unitT)
        VTUnit
      case VTSingle(x) =>
        VTSingle(CVariable(x,typ))
      case VTCons(a,b) =>
        val (aT,bT) = Isabelle.dest_prodT(typ)
        VTCons(mk_cvar_term(a,aT), mk_cvar_term(b,bT))
    }

//    def mk_qvar_list(names : List[String], typ : Typ) : List[QVariable] = names match {
//      case Nil =>
//        assert(typ == Isabelle.unitT)
//        Nil
//      case List(x) =>
//        List(QVariable(x,typ))
//      case x::xs =>
//        val (xT,xsT) = Isabelle.dest_prodT(typ)
//        QVariable(x,xT) :: mk_qvar_list(xs, xsT)
//    }

    def mk_qvar_term(names : VarTerm[String], typ : Typ) : VarTerm[QVariable] = names match {
      case VTUnit =>
        assert(typ == Isabelle.unitT)
        VTUnit
      case VTSingle(x) =>
        VTSingle(QVariable(x,typ))
      case VTCons(a,b) =>
        val (aT,bT) = Isabelle.dest_prodT(typ)
        VTCons(mk_qvar_term(a,aT), mk_qvar_term(b,bT))
    }


    override def decode(xml: XML.Tree): XMLResult[Statement] = xml match {
      case XML.Elem(("local",Nil), List(cvarsXml, qvarsXml, bodyXml)) =>
        for (cvarsVt <- VarTerm.codecC.decode(cvarsXml);
             cvars = cvarsVt.toList;
             qvarsVt <- VarTerm.codecQ.decode(qvarsXml);
             qvars = qvarsVt.toList;
             body <- decode(bodyXml))
          yield Local(cvars, qvars, body.toBlock)
      case XML.Elem(("block", Nil), stmtsXml) =>
        for (stmts <- stmtsXml.traverse(decode))
          yield Block(stmts : _*)
      case XML.Elem(("assign", Nil), List(lhsXml,rhsXml)) =>
        for (lhs <- VarTerm.codecString.decode(lhsXml);
             rhs <- RichTerm.codec.decode(rhsXml))
          yield Assign(mk_cvar_term(lhs, rhs.typ), rhs)
      case XML.Elem(("sample", Nil), List(lhsXml,rhsXml)) =>
        for (lhs <- VarTerm.codecString.decode(lhsXml);
             rhs <- RichTerm.codec.decode(rhsXml))
          yield Sample(mk_cvar_term(lhs, Isabelle.dest_distrT(rhs.typ)), rhs)
      case call @ XML.Elem(("call",_),_) => decode_call(call)
      case XML.Elem(("measurement", Nil), List(lhsXml,locXml,expXml)) =>
        for (lhs <- VarTerm.codecString.decode(lhsXml);
             loc <- VarTerm.codecString.decode(locXml);
             exp <- RichTerm.codec.decode(expXml);
             (vT,locT) = Isabelle.dest_measurementT(exp.typ))
          yield Measurement(mk_cvar_term(lhs,vT), mk_qvar_term(loc,locT), exp)
      case XML.Elem(("qinit", Nil), List(locXML,expXML)) =>
        for (loc <- VarTerm.codecString.decode(locXML);
             exp <- RichTerm.codec.decode(expXML))
          yield QInit(mk_qvar_term(loc, Isabelle.dest_vectorT(exp.typ)), exp)
      case XML.Elem(("qapply", Nil), List(locXML,expXML)) =>
        for (loc <- VarTerm.codecString.decode(locXML);
             exp <- RichTerm.codec.decode(expXML))
          yield QApply(mk_qvar_term(loc, Isabelle.dest_l2boundedT(exp.typ)._1), exp)
      case XML.Elem(("ifte", Nil), List(eXml,p1Xml,p2Xml)) =>
        for (e <- RichTerm.codec.decode(eXml);
             p1 <- decode(p1Xml);
             p2 <- decode(p2Xml))
          yield IfThenElse(e, p1.asInstanceOf[Block], p2.asInstanceOf[Block])
      case XML.Elem(("while", Nil), List(eXml,p1Xml)) =>
        for (e <- RichTerm.codec.decode(eXml);
             p1 <- decode(p1Xml))
          yield While(e, p1.asInstanceOf[Block])
    }
  }

  val statement_to_term_op: Operation[(BigInt, Statement), RichTerm] =
    Operation.implicitly[(BigInt, Statement), RichTerm]("statement_to_term")

  val statements_to_term_op: Operation[(BigInt, List[Statement]), RichTerm] =
    Operation.implicitly[(BigInt, List[Statement]), RichTerm]("statements_to_term")
}

class Local(val vars: List[Variable], val body : Block) extends Statement {
  assert(vars.nonEmpty)

  override def equals(obj: Any): Boolean = obj match {
    case o : Local =>
      (vars == o.vars) && (body == o.body)
    case _ => false
  }

  override def substituteOracles(subst: Map[String, Call]): Statement =
    new Local(vars=vars, body=body.substituteOracles(subst))

  override def simplify(isabelle: Isabelle.Context, facts: List[String], thms: ListBuffer[Thm]): Statement =
    new Local(vars=vars, body=body.simplify(isabelle, facts, thms))

  override def markOracles(oracles: List[String]): Statement =
    new Local(vars=vars, body=body.markOracles(oracles))

  override def checkWelltyped(context: Isabelle.Context): Unit =
    body.checkWelltyped(context)

  override def inline(name: String, oracles: List[String], program: Statement): Statement =
    body.inline(name, oracles, program) match {
      case Block(Local(vars2, body)) =>
        new Local(vars ++ vars2, body)
      case stmt => new Local(vars, stmt)
  }

  override def toString: String = body.statements match {
    case Nil => "{ local " + vars.map(_.name).mkString(", ") + "; skip; }"
    case stmts => "{ local " + vars.map(_.name).mkString(", ") + "; " + stmts.map {_.toString}.mkString(" ") + " }"
  }

  override def renameQVariable(env: Environment, from: QVariable, to: QVariable): Local = {
    if (vars.contains(from)) {
      if (this.variableUse(env).quantum.contains(to))
        throw UserException(s"Cannot rename ${from.name} -> ${to.name}: ${to.name} is free variable in $this.")
      else
        this
    } else if (vars.contains(to))
      throw UserException(s"Cannot rename ${from.name} -> ${to.name} in ${this}: ${to.name} is a local variable")
    else
      new Local(vars, body.renameQVariable(env, from, to))
  }

  override def renameCVariable(env: Environment, from: CVariable, to: CVariable): Local = {
    if (vars.contains(from)) {
      if (this.variableUse(env).classical.contains(to))
        throw UserException(s"Cannot rename ${from.name} -> ${to.name}: ${to.name} is free variable in $this.")
      else
        this
    } else if (vars.contains(to))
      throw UserException(s"Cannot rename ${from.name} -> ${to.name} in ${this}: ${to.name} is a local variable")
    else
      new Local(vars, body.renameCVariable(env, from, to))
  }

  def simplifyEmpty: Statement =
    if (vars.isEmpty) body
    else this
}

object Local {
  def apply(cvars: Seq[CVariable], qvars: Seq[QVariable], body : Block): Local = {
    new Local(cvars.toList ++ qvars.toList, body)
  }

  def apply(vars: Seq[Variable], body : Block): Local = {
    new Local(vars.toList, body)
  }

  def makeIfNeeded(cvars: Seq[CVariable], qvars: Seq[QVariable], body : Statement): Statement =
    makeIfNeeded(cvars ++ qvars, body)

  def makeIfNeeded(vars: Seq[Variable], body : Statement): Statement =
    if (vars.nonEmpty)
      body match {
        case Local(vars0, body0) =>
          new Local(ListSet(vars++vars0 :_*).toList, body0)
        case _ =>
          new Local(vars.toList, body.toBlock)
      }
    else
      body

  def apply(env : Environment, vars : Seq[String], body : Block): Local = {
    val vars2 = vars map env.getProgVariable
    new Local(vars2.toList, body)
  }
  def unapply(x : Local): Some[(List[Variable], Block)] = Some((x.vars, x.body))
}

class Block(val statements:List[Statement]) extends Statement {
  def unwrapTrivialBlock: Statement = statements match {
    case List(s) => s
    case _ => this
  }

  def ++(other: Block) = new Block(statements ::: other.statements)


  override def simplify(isabelle: Isabelle.Context, facts: List[String], thms: ListBuffer[Thm]): Block =
    Block(statements.map(_.simplify(isabelle,facts,thms)):_*)

  //  @deprecated("too slow", "now")
//  def programListTermOld(context: Isabelle.Context): Term = Isabelle.mk_list(Isabelle.programT, statements.map(_.programTermOLD(context)))

  def programListTerm(context: Isabelle.Context): RichTerm =
    context.isabelle.invoke(Statement.statements_to_term_op, (context.contextId, this.statements))


//  override def programTermOLD(context: Isabelle.Context) : Term = Isabelle.block $ programListTermOld(context)

  override def toBlock: Block = this

  override def equals(o: Any): Boolean = o match {
    case Block(st @ _*) => statements==st
    case _ => false
  }

  override def toString: String = statements match {
    case Nil => "{}"
    case List(s) => s.toString
    case _ => "{ " + statements.map{ _.toString}.mkString(" ") + " }"
  }

  def toStringNoParens: String = statements match {
    case Nil => "skip;"
    case _ => statements.map{ _.toString }.mkString(" ")
  }

  def toStringMultiline(header: String): String = statements match {
    case Nil => header+"skip;"
    case _ =>
      val blanks = "\n" + " " * header.length
      statements.mkString(header,blanks,"")
  }




  def length : Int = statements.size

  def inline(environment: Environment, name: String): Block = {
    environment.programs(name) match {
      case decl : ConcreteProgramDecl =>
        inline(name: String, decl.oracles, decl.program)
      case _ : AbstractProgramDecl =>
        throw UserException(s"Cannot inline '$name'. It is an abstract program (declared with 'adversary').")
    }
//    inline(name: String, environment.programs(name).asInstanceOf[ConcreteProgramDecl].program)
  }

  override def inline(name:String, oracles:List[String], program:Statement): Block = {
//    val programStatements = program match {
//      case Block(st @_*) => st
//      case _ => List(program)
//    }
    val newStatements = for (s <- statements;
                             s2 <- s match {
                               case Call(name2, args @ _*) if name==name2 =>
                                 assert(args.length==oracles.length)
                                 val subst = Map(oracles.zip(args) : _*)
//                                 assert(args.isEmpty, s"""Cannot inline "$s", oracles not supported.""")
                                 program.substituteOracles(subst).unwrapBlock
                               case _ => List(s.inline(name,oracles,program))
                             }) yield s2
    Block(newStatements : _*)
  }

  override def checkWelltyped(context: Isabelle.Context): Unit =
    for (s <- statements) s.checkWelltyped(context)

  override def markOracles(oracles: List[String]): Block = new Block(statements.map(_.markOracles(oracles)))

  override def substituteOracles(subst: Map[String, Call]): Block = Block(statements.map(_.substituteOracles(subst)):_*)

  override def renameQVariable(env: Environment, from: QVariable, to: QVariable): Block =
    new Block(statements map { _.renameQVariable(env,from,to) })
  override def renameCVariable(env: Environment, from: CVariable, to: CVariable): Block =
    new Block(statements map { _.renameCVariable(env,from,to) })
}

object Block {
  def makeBlockIfNeeded(statements: Seq[Statement]): Statement = statements match {
    case Seq(s) => s
    case _ => Block(statements:_*)
  }

  def apply(statements: Statement*) : Block = new Block(statements.toList)
  val empty = Block()
  def unapplySeq(block: Block): Some[Seq[Statement]] = Some(block.statements)
}


final case class Assign(variable:VarTerm[CVariable], expression:RichTerm) extends Statement {
  override def toString: String = s"""${Variable.vartermToString(variable)} <- $expression;"""
  override def inline(name: String, oracles: List[String], statement: Statement): Statement = this

  override def checkWelltyped(context: Isabelle.Context): Unit =
    expression.checkWelltyped(context, Isabelle.tupleT(variable.map[Typ](_.valueTyp)))

  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.assign(variable.valueTyp) $ variable.variableTerm $ expression.encodeAsExpression(context).isabelleTerm
  override def simplify(isabelle: Isabelle.Context, facts: List[String], thms:ListBuffer[Thm]): Assign =
    Assign(variable, expression.simplify(isabelle, facts, thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): Assign = this

  override def substituteOracles(subst: Map[String, Call]): Statement = this

  override def renameQVariable(env: Environment, from: QVariable, to: QVariable): Assign = this

  override def renameCVariable(env: Environment, from: CVariable, to: CVariable): Assign =
    Assign(variable.replace(from, to), expression.renameCVariable(from, to))
}
final case class Sample(variable:VarTerm[CVariable], expression:RichTerm) extends Statement {
  override def toString: String = s"""${Variable.vartermToString(variable)} <$$ $expression;"""
  override def inline(name: String, oracles: List[String], statement: Statement): Statement = this

  override def checkWelltyped(context: Isabelle.Context): Unit =
    expression.checkWelltyped(context, Isabelle.distrT(Isabelle.tupleT(variable.map[Typ](_.valueTyp))))

  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.sample(variable.valueTyp) $ variable.variableTerm $ expression.encodeAsExpression(context).isabelleTerm
  override def simplify(isabelle: Isabelle.Context, facts: List[String], thms: ListBuffer[Thm]): Sample =
    Sample(variable, expression.simplify(isabelle,facts,thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): Sample = this

  override def substituteOracles(subst: Map[String, Call]): Statement = this

  override def renameQVariable(env: Environment, from: QVariable, to: QVariable): Sample = this

  override def renameCVariable(env: Environment, from: CVariable, to: CVariable): Sample =
    Sample(variable.replace(from,to), expression.renameCVariable(from, to))
}
final case class IfThenElse(condition:RichTerm, thenBranch: Block, elseBranch: Block) extends Statement {
  override def inline(name: String, oracles: List[String], program: Statement): Statement =
    IfThenElse(condition,thenBranch.inline(name,oracles,program),elseBranch.inline(name,oracles,program))
  override def toString: String = s"if ($condition) $thenBranch else $elseBranch;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    condition.checkWelltyped(context, HOLogic.boolT)
    thenBranch.checkWelltyped(context)
    elseBranch.checkWelltyped(context)
  }
  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.ifthenelse $ condition.encodeAsExpression(context).isabelleTerm $ thenBranch.programListTermOld(context) $ elseBranch.programListTermOld(context)
  override def simplify(isabelle: Isabelle.Context, facts: List[String], thms: ListBuffer[Thm]): IfThenElse =
    IfThenElse(condition.simplify(isabelle,facts,thms),
      thenBranch.simplify(isabelle,facts,thms),
      elseBranch.simplify(isabelle,facts,thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): IfThenElse = IfThenElse(condition,thenBranch.markOracles(oracles),elseBranch.markOracles(oracles))

  override def substituteOracles(subst: Map[String, Call]): Statement = IfThenElse(condition,thenBranch.substituteOracles(subst),elseBranch.substituteOracles(subst))

  override def renameQVariable(env: Environment, from: QVariable, to: QVariable): IfThenElse =
    IfThenElse(condition, thenBranch.renameQVariable(env,from,to), elseBranch.renameQVariable(env,from,to))

  override def renameCVariable(env: Environment, from: CVariable, to: CVariable): IfThenElse =
    IfThenElse(condition.renameCVariable(from,to), thenBranch.renameCVariable(env,from,to), elseBranch.renameCVariable(env,from,to))
}

final case class While(condition:RichTerm, body: Block) extends Statement {
  override def inline(name: String, oracles: List[String], program: Statement): Statement =
    While(condition,body.inline(name,oracles,program))
  override def toString: String = s"while ($condition) $body"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    condition.checkWelltyped(context, HOLogic.boolT)
    body.checkWelltyped(context)
  }
  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.whileProg $ condition.encodeAsExpression(context).isabelleTerm $ body.programListTermOld(context)
  override def simplify(isabelle: Isabelle.Context, facts: List[String], thms: ListBuffer[Thm]): While =
    While(condition.simplify(isabelle,facts,thms),
      body.simplify(isabelle,facts,thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): While = While(condition, body.markOracles(oracles))

  override def substituteOracles(subst: Map[String, Call]): Statement = While(condition,body.substituteOracles(subst))

  override def renameQVariable(env: Environment, from: QVariable, to: QVariable): While =
    While(condition, body.renameQVariable(env, from, to))

  override def renameCVariable(env: Environment, from: CVariable, to: CVariable): While =
    While(condition.renameCVariable(from, to), body.renameCVariable(env, from, to))
}

final case class QInit(location:VarTerm[QVariable], expression:RichTerm) extends Statement {
  override def inline(name: String, oracles: List[String], program: Statement): Statement = this
  override def toString: String = s"${Variable.vartermToString(location)} <q $expression;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    val expected = Isabelle.ell2T(Isabelle.tupleT(location.map[Typ](_.valueTyp)))
    expression.checkWelltyped(context, expected)
  }
  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.qinit(Isabelle.tupleT(location.map(_.valueTyp):_*)) $ Isabelle.qvarTuple_var(location) $ expression.encodeAsExpression(context).isabelleTerm
  override def simplify(isabelle: Isabelle.Context, facts: List[String], thms: ListBuffer[Thm]): QInit =
    QInit(location, expression.simplify(isabelle,facts,thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): QInit = this

  override def substituteOracles(subst: Map[String, Call]): Statement = this

  override def renameQVariable(env: Environment, from: QVariable, to: QVariable): QInit = {
    if (this.location.contains(to))
      throw UserException(s"Cannot rename ${from.name} -> ${to.name} in $this: ${to.name} is already in use")
    QInit(location.replace(from, to), expression)
  }

  override def renameCVariable(env: Environment, from: CVariable, to: CVariable): QInit =
    QInit(location, expression.renameCVariable(from, to))
}

final case class QApply(location:VarTerm[QVariable], expression:RichTerm) extends Statement {
  override def inline(name: String, oracles: List[String], program: Statement): Statement = this
  override def toString: String = s"on ${Variable.vartermToString(location)} apply $expression;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    val varType = Isabelle.tupleT(location.map[Typ](_.valueTyp))
    val expected = pure.Type("Bounded_Operators.bounded",List(varType,varType))
    expression.checkWelltyped(context, expected)
  }
  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.qapply(Isabelle.tupleT(location.map(_.valueTyp):_*)) $ Isabelle.qvarTuple_var(location) $ expression.encodeAsExpression(context).isabelleTerm
  override def simplify(isabelle: Isabelle.Context, facts: List[String], thms: ListBuffer[Thm]): QApply =
    QApply(location, expression.simplify(isabelle,facts,thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): QApply = this

  override def substituteOracles(subst: Map[String, Call]): Statement = this

  override def renameQVariable(env: Environment, from: QVariable, to: QVariable): QApply = {
    if (this.location.contains(to))
      throw UserException(s"Cannot rename ${from.name} -> ${to.name} in $this: ${to.name} is already in use")
    QApply(location.replace(from, to), expression)
  }

  override def renameCVariable(env: Environment, from: CVariable, to: CVariable): QApply =
    QApply(location, expression.renameCVariable(from, to))
}
final case class Measurement(result:VarTerm[CVariable], location:VarTerm[QVariable], e:RichTerm) extends Statement {
  override def inline(name: String, oracles: List[String], program: Statement): Statement = this
  override def toString: String = s"${Variable.vartermToString(result)} <- measure ${Variable.vartermToString(location)} in $e;"

  override def checkWelltyped(context: Isabelle.Context): Unit = {
    val expected = pure.Type("QRHL_Core.measurement",List(
      Isabelle.tupleT(result.map[Typ](_.valueTyp)),
      Isabelle.tupleT(location.map[Typ](_.valueTyp))))
    e.checkWelltyped(context, expected)
  }
  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.measurement(Isabelle.tupleT(location.map(_.valueTyp):_*), result.valueTyp) $
  //      result.variableTerm $ Isabelle.qvarTuple_var(location) $ e.encodeAsExpression(context).isabelleTerm
  override def simplify(isabelle: Isabelle.Context, facts: List[String], thms: ListBuffer[Thm]): Measurement =
    Measurement(result,location,e.simplify(isabelle,facts,thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): Measurement = this

  override def substituteOracles(subst: Map[String, Call]): Statement = this

  override def renameQVariable(env: Environment, from: QVariable, to: QVariable): Measurement = {
    if (this.location.contains(to))
      throw UserException(s"Cannot rename ${from.name} -> ${to.name} in $this: ${to.name} is already in use")
    Measurement(result, location.replace(from, to), e)
  }

  override def renameCVariable(env: Environment, from: CVariable, to: CVariable): Measurement =
    Measurement(result.replace(from, to), location, e.renameCVariable(from, to))
}

final case class Call(name:String, args:Call*) extends Statement {
  override def toString: String = "call "+toStringShort+";"
  def toStringShort: String =
    if (args.isEmpty) name else s"$name(${args.map(_.toStringShort).mkString(",")})"
  override def inline(name: String, oracles: List[String], program: Statement): Statement = this

  override def checkWelltyped(context: Isabelle.Context): Unit = {}
//  override def programTermOLD(context: Isabelle.Context): Term = {
//    if (args.nonEmpty) {
//      val argTerms = args.map(_.programTermOLD(context)).toList
//      val argList = Isabelle.mk_list(Isabelle.programT, argTerms)
//      Isabelle.instantiateOracles $ Free(name, Isabelle.oracle_programT) $ argList
//    } else
//      Free(name, Isabelle.programT)
//  }
  override def simplify(isabelle: Isabelle.Context, facts: List[String], thms: ListBuffer[Thm]): Call = this

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): Call = {
    if (name.head=='@')
      throw UserException(s"Program code contains program name $name (invalid, @ is for internal names)")
    val name2 = if (oracles.contains(name)) "@"+name else name
    Call(name2, args.map(_.markOracles(oracles)):_*)
  }

  override def substituteOracles(subst: Map[String, Call]): Call = {
    val args2 = args.map(_.substituteOracles(subst))

    if (name.head=='@') {
      if (args.nonEmpty)
        throw UserException(s"Call to oracle $name must not have oracles itself")
      subst(name.substring(1))
    } else
      Call(name,args2:_*)
  }

  override def renameQVariable(env: Environment, from: QVariable, to: QVariable): Call = {
    val varUse = this.variableUse(env)
    if (varUse.quantum.contains(from))
      throw UserException(s"Cannot rename ${from.name} -> ${to.name}: ${from.name} must not occur in $this. Consider inlining ${this.name}")
    if (varUse.quantum.contains(to))
      throw UserException(s"Cannot rename ${from.name} -> ${to.name}: ${to.name} already occurs in $this")
    this
  }

  override def renameCVariable(env: Environment, from: CVariable, to: CVariable): Call = {
    val varUse = this.variableUse(env)
    if (varUse.classical.contains(from))
      throw UserException(s"Cannot rename ${from.name} -> ${to.name}: ${from.name} must not occur in $this. Consider inlining ${this.name}")
    if (varUse.classical.contains(to))
      throw UserException(s"Cannot rename ${from.name} -> ${to.name}: ${to.name} already occurs in $this")
    this
  }
}
