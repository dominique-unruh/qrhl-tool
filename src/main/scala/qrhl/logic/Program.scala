package qrhl.logic

import qrhl.isabellex.IsabelleX.{globalIsabelle => GIsabelle}
import GIsabelle.Ops
import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.mlvalue.MLValue.Converter
import de.unruh.isabelle.control
import de.unruh.isabelle.pure.{Term, Thm, Typ, Type}
import hashedcomputation.{Hash, HashTag, Hashable, HashedValue}
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.logic.Variable.{varsNamesToString, varsToString}
import qrhl.{AllSet, MaybeAllSet, UserException, Utils}

import scala.annotation.tailrec
import scala.collection.immutable.ListSet
import scala.collection.mutable.ListBuffer
import scala.collection.{AbstractIterator, GenSet, mutable}
import scala.concurrent.{ExecutionContext, Future}
import scala.language.{implicitConversions, postfixOps}

// Implicits
import qrhl.Utils.listSetUpcast
import qrhl.Utils.ListSetUtils
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import qrhl.isabellex.MLValueConverters.Implicits._
import scala.concurrent.ExecutionContext.Implicits._
import hashedcomputation.Implicits._
import VarTerm.VarTermHashable

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
  def isabelleTerm(vt:VarTerm[Variable]) : Term = vt match {
    case VTUnit => GIsabelle.variable_unit
    case VTSingle(v) => GIsabelle.variable_singleton(v.variableTerm)
    case VTCons(a, b) => GIsabelle.variable_concat(isabelleTerm(a), isabelleTerm(b))
  }

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

  implicit def varTermHashable[A : Hashable]: VarTermHashable[A] = new VarTermHashable[A](implicitly)
  class VarTermHashable[A](val aHashable: Hashable[A]) extends AnyVal with Hashable[VarTerm[A]] {
    implicit def aH: Hashable[A] = aHashable
    override def hash[A1 <: VarTerm[A]](varTerm: A1): Hash[A1] = (varTerm : VarTerm[A]) match { // TODO better hashing
      case VTUnit => hashVTUnit
      case VTSingle(v) =>
        HashTag()(Hashable.hash(v))
      case VTCons(a, b) =>
        HashTag()(hash(a), hash(b))
    }
  }
  private val hashVTUnit = Hash.randomHash()
}

case class ExprVariableUse
(
  program : ListSet[Variable],
  ambient : ListSet[String]
) {
  @deprecated("","") def classical : ListSet[CVariable] = Variable.classical(program)
  @deprecated("","") def quantum : ListSet[QVariable] = Variable.quantum(program)
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

  @deprecated("","") def classical: ListSet[CVariable] = freeVariables collect { case v : CVariable => v }
  @deprecated("","") def quantum: ListSet[QVariable] = freeVariables collect { case v : QVariable => v }
  @deprecated("","") def overwrittenClassical : ListSet[CVariable] = overwritten collect { case v : CVariable => v }
  @deprecated("","") def overwrittenQuantum : ListSet[QVariable] = overwritten collect { case v : QVariable => v }
  @deprecated("","") def innerClassical : ListSet[CVariable] = inner collect { case v : CVariable => v }
  @deprecated("","") def innerQuantum : ListSet[QVariable] = inner collect { case v : QVariable => v }
  @deprecated("","") def writtenClassical : ListSet[CVariable] = written collect { case v : CVariable => v }

  override def toString: String = s"""
      | Free        ⊆ ${varsToString(freeVariables)}
      | Ambient     ⊆ ${varsNamesToString(ambient)}
      | Programs    = ${varsNamesToString(programs.map(_.name))}
      | Written     ⊆ ${varsToString(written)}
      | Overwritten ⊇ ${varsToString(overwritten)}
      | Inner       ⊆ ${varsToString(inner)}
      | Covered     ⊇ ${if (covered.isAll) "all variables" else varsToString(covered)}
      | Oracles     ⊆ ${varsNamesToString(oracles)}
    """.stripMargin
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
sealed trait Statement extends HashedValue {
  def toSeq: Seq[Statement] = this match {
    case Block(statements @ _*) => statements
    case _ => List(this)
  }

  /** Checks whether "no_conflict renaming this" holds.
   * @param renaming the substitution as an association list. Must not contain pairs (x,x), nor two pairs (x,y), (x,y').
   * @return false if no_conflict does not hold. May returns false negatives. */
  def noConflict(env: Environment, renaming: List[(Variable, Variable)]) : Boolean

  /** Renames all program variables. (subst_vars in Isabelle)
   * @param renaming the substitution as an association list. Must not contain pairs (x,x), nor two pairs (x,y), (x,y'). */
  def renameVariables(env: Environment, renaming: List[(Variable, Variable)]) : Statement

  def substituteOracles(subst: Map[String, Call]) : Statement

  def simplify(isabelle: IsabelleX.ContextX, facts: List[String], thms:ListBuffer[Thm]): Statement

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  def markOracles(oracles: List[String]): Statement

  /** Converts this statement into a block by wrapping it in Block() if necessary */
  def toBlock: Block = Block(this)

  def programTerm(context: IsabelleX.ContextX): RichTerm =
    RichTerm(Ops.statement_to_term_op(
      MLValue((context.context, this))).retrieveNow)

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
          overwritten = sVars.overwritten +++ (ssVars.overwritten -- sVars.freeVariables).intersect(sVars.covered),
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
        val fvE = e.variables(env)
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
      case call @ Call(name, args@_*) =>
        if (name.head != '@') {
          // Call(name, args@_*) is an application C[a1,...,an] where C is referenced by name, and args=(a1,...,an)
          env.programs(name) match {
            case progDecl : ConcreteProgramDecl =>
              Block(call).inline(env, name).variableUse(env)
            case progDecl : AbstractProgramDecl =>
              val progVars = progDecl.variablesRecursive
              val argVars = args map (_.variableUse(env))
              val oracles = argVars.foldLeft(emptySet: ListSet[String]) {
                _ +++ _.oracles
              }
              val isProgram = oracles.isEmpty
              new VariableUse(
                // By Helping_Lemmas.fv_subst' (note that freeVariables is an upper bound)
                freeVariables = progVars.freeVariables ++
                  MaybeAllSet.subtract(argVars.foldLeft[ListSet[Variable]](emptySet) {
                    _ +++ _.freeVariables
                  }, progVars.covered),
                // By Helping_Lemmas.fv_written' (note that freeVariables is an upper bound)
                written = argVars.foldLeft(progVars.written) {
                  _ +++ _.written
                },
                ambient = argVars.foldLeft(progVars.ambient) {
                  _ +++ _.ambient
                },
                programs = argVars.foldLeft(progVars.programs + progDecl) {
                  _ +++ _.programs
                },
                // By Helping_Lemmas.overwr_subst (note that overwritten is a lower bound)
                overwritten = progVars.overwritten,
                oracles = oracles,
                // By Helping_Lemmas.program_inner and .inner_subst (note that inner is an upper bound)
                inner = if (isProgram) emptySet else
                  argVars.foldLeft(progVars.inner) {
                    _ +++ _.inner
                  },
                // By Helping_Lemmas.program_covered and .covered_subst (note that covered is a lower bound)
                covered = if (isProgram) MaybeAllSet.all[Variable]
                else if (progVars.covered.isAll) MaybeAllSet.all // shortcut for the next line
                else progVars.covered ++ argVars.foldLeft[MaybeAllSet[Variable]]
                  (MaybeAllSet.all) { (cov, a) => cov.intersect(a.covered) }
              )
          }
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
        val fvE = e.variables(env)
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
        val fvE = e.variables(env)
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
        val fvE = e.variables(env)
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
        val fvE = e.variables(env)
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
        val fvE = e.variables(env)
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

  def checkWelltyped(context: IsabelleX.ContextX): Unit

  /** All ambient and program variables.
    * Not including nested programs (via Call).
    * Includes local variables.
    * */
  def variablesDirect : Set[String] = {
    val vars = Set.newBuilder[String]
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
    vars.result()
  }

  def inline(name: String, oracles: List[String], program: Statement): Statement

  def unwrapBlock : Seq[Statement] = this  match {
    case Block(st @_*) => st
    case _ => List(this)
  }

}


class Local(val vars: List[Variable], val body : Block) extends Statement {
  assert(vars.nonEmpty)

  lazy val hash : Hash[this.type] =
    HashTag()(Hashable.hash(vars), Hashable.hash(body))

  override def equals(obj: Any): Boolean = obj match {
    case o : Local =>
      (vars == o.vars) && (body == o.body)
    case _ => false
  }

  override def substituteOracles(subst: Map[String, Call]): Statement =
    new Local(vars=vars, body=body.substituteOracles(subst))

  override def simplify(isabelle: IsabelleX.ContextX, facts: List[String], thms: ListBuffer[Thm]): Statement =
    new Local(vars=vars, body=body.simplify(isabelle, facts, thms))

  override def markOracles(oracles: List[String]): Statement =
    new Local(vars=vars, body=body.markOracles(oracles))

  override def checkWelltyped(context: IsabelleX.ContextX): Unit =
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

  def simplifyEmpty: Statement =
    if (vars.isEmpty) body
    else this

  // lemma no_conflict_locals:
  //  assumes "finite X"
  //  assumes "no_conflict (λx. if x ∈ X then x else σ x) c"
  //  assumes "X ∩ σ ` (fv c ∩ var_subst_dom σ) = {}"
  //  shows "no_conflict σ (locals X c)"
  override def noConflict(env: Environment, renaming: List[(Variable, Variable)]): Boolean = {
    val dom = renaming map { _._1 }
    val fv = variableUse(env).freeVariables
    val fvDom = fv & dom.toSet
    // σ ` (fv c ∩ var_subst_dom σ)
    val renaming_fv_dom = renaming.collect { case (x,y) if fvDom.contains(x) => y }.toSet
    //  assumes "X ∩ σ ` (fv c ∩ var_subst_dom σ) = {}"
    if ((this.vars.toSet & renaming_fv_dom).nonEmpty)
      return false
    val renamingFiltered = renaming filterNot { case (x,y) => vars.contains(x) }
    //  assumes "no_conflict (λx. if x ∈ X then x else σ x) c"
    this.body.noConflict(env, renamingFiltered)
  }

  override def renameVariables(env: Environment, renaming: List[(Variable, Variable)]): Local =
    Local(this.vars, body.renameVariables(env, renaming.filterNot { case (x,y) => vars.contains(x) }))

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

  lazy val hash : Hash[this.type] =
    HashTag()(Hashable.hash(statements))

  def unwrapTrivialBlock: Statement = statements match {
    case List(s) => s
    case _ => this
  }

  def ++(other: Block) = new Block(statements ::: other.statements)


  override def simplify(isabelle: IsabelleX.ContextX, facts: List[String], thms: ListBuffer[Thm]): Block =
    Block(statements.map(_.simplify(isabelle,facts,thms)):_*)

  //  @deprecated("too slow", "now")
//  def programListTermOld(context: Isabelle.Context): Term = Isabelle.mk_list(Isabelle.programT, statements.map(_.programTermOLD(context)))

  def programListTerm(context: IsabelleX.ContextX): RichTerm =
    RichTerm(Ops.statements_to_term_op(
      MLValue((context.context, statements))).retrieveNow)


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

  /** Inlines the declared program `name` in this.
   * Does not recursively inline (i.e., `name` is not substituted in the body of `name` itself).
   * (Not sure this case can even occur...) */
  def inline(environment: Environment, name: String): Block = {
    environment.programs(name) match {
      case decl : ConcreteProgramDecl =>
        inline(name: String, decl.oracles, decl.program)
      case _ : AbstractProgramDecl =>
        throw UserException(s"Cannot inline '$name'. It is an abstract program (declared with 'adversary').")
    }
  }

  override def inline(name:String, oracles:List[String], program:Statement): Block = {
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

  override def checkWelltyped(context: IsabelleX.ContextX): Unit =
    for (s <- statements) s.checkWelltyped(context)

  override def markOracles(oracles: List[String]): Block = new Block(statements.map(_.markOracles(oracles)))

  override def substituteOracles(subst: Map[String, Call]): Block = Block(statements.map(_.substituteOracles(subst)):_*)

  // nc_Seq: "no_conflict σ c1 ⟹ no_conflict σ c2 ⟹ no_conflict σ (c1; c2)"
  override def noConflict(env: Environment, renaming: List[(Variable, Variable)]): Boolean =
    this.statements.forall(_.noConflict(env, renaming))

  override def renameVariables(env: Environment, renaming: List[(Variable, Variable)]): Block =
    Block(statements.map(_.renameVariables(env, renaming)) :_*)
}

object Block {
  def makeBlockIfNeeded(statements: Seq[Statement]): Statement = statements match {
    case Seq(s) => s
    case _ => Block(statements:_*)
  }

  def apply(statements: Statement*) : Block = new Block(statements.toList)
  val empty: Block = Block()
  def unapplySeq(block: Block): Some[Seq[Statement]] = Some(block.statements)
}


final case class Assign(variable:VarTerm[CVariable], expression:RichTerm) extends Statement {
  lazy val hash : Hash[this.type] =
    HashTag()(Hashable.hash(variable), Hashable.hash(expression))

  override def toString: String = s"""${Variable.vartermToString(variable)} <- $expression;"""
  override def inline(name: String, oracles: List[String], statement: Statement): Statement = this

  override def checkWelltyped(context: IsabelleX.ContextX): Unit =
    expression.checkWelltyped(context, GIsabelle.tupleT(variable.map[Typ](_.valueTyp)))

  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.assign(variable.valueTyp) $ variable.variableTerm $ expression.encodeAsExpression(context).isabelleTerm
  override def simplify(isabelle: IsabelleX.ContextX, facts: List[String], thms:ListBuffer[Thm]): Assign =
    Assign(variable, expression.simplify(isabelle, facts, thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): Assign = this

  override def substituteOracles(subst: Map[String, Call]): Statement = this

  override def noConflict(env: Environment, renaming: List[(Variable, Variable)]): Boolean = true

  override def renameVariables(env: Environment, renaming: List[(Variable, Variable)]): Assign =
    Assign(variable.map(_.substitute(renaming)), expression.renameCVariables(renaming))
}
final case class Sample(variable:VarTerm[CVariable], expression:RichTerm) extends Statement {
  lazy val hash : Hash[this.type] =
    HashTag()(Hashable.hash(variable), Hashable.hash(expression))

  override def toString: String = s"""${Variable.vartermToString(variable)} <$$ $expression;"""
  override def inline(name: String, oracles: List[String], statement: Statement): Statement = this

  override def checkWelltyped(context: IsabelleX.ContextX): Unit =
    expression.checkWelltyped(context, GIsabelle.distrT(GIsabelle.tupleT(variable.map[Typ](_.valueTyp))))

  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.sample(variable.valueTyp) $ variable.variableTerm $ expression.encodeAsExpression(context).isabelleTerm
  override def simplify(isabelle: IsabelleX.ContextX, facts: List[String], thms: ListBuffer[Thm]): Sample =
    Sample(variable, expression.simplify(isabelle,facts,thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): Sample = this

  override def substituteOracles(subst: Map[String, Call]): Statement = this

  override def noConflict(env: Environment, renaming: List[(Variable, Variable)]): Boolean = true

  override def renameVariables(env: Environment, renaming: List[(Variable, Variable)]): Sample =
    Sample(variable.map(_.substitute(renaming)), expression.renameCVariables(renaming))
}

final case class IfThenElse(condition:RichTerm, thenBranch: Block, elseBranch: Block) extends Statement {
  lazy val hash : Hash[this.type] =
    HashTag()(Hashable.hash(condition), Hashable.hash(thenBranch), Hashable.hash(elseBranch))

  override def inline(name: String, oracles: List[String], program: Statement): Statement =
    IfThenElse(condition,thenBranch.inline(name,oracles,program),elseBranch.inline(name,oracles,program))
  override def toString: String = s"if ($condition) $thenBranch else $elseBranch;"

  override def checkWelltyped(context: IsabelleX.ContextX): Unit = {
    condition.checkWelltyped(context, GIsabelle.boolT)
    thenBranch.checkWelltyped(context)
    elseBranch.checkWelltyped(context)
  }
  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.ifthenelse $ condition.encodeAsExpression(context).isabelleTerm $ thenBranch.programListTermOld(context) $ elseBranch.programListTermOld(context)
  override def simplify(isabelle: IsabelleX.ContextX, facts: List[String], thms: ListBuffer[Thm]): IfThenElse =
    IfThenElse(condition.simplify(isabelle,facts,thms),
      thenBranch.simplify(isabelle,facts,thms),
      elseBranch.simplify(isabelle,facts,thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): IfThenElse = IfThenElse(condition,thenBranch.markOracles(oracles),elseBranch.markOracles(oracles))

  override def substituteOracles(subst: Map[String, Call]): Statement = IfThenElse(condition,thenBranch.substituteOracles(subst),elseBranch.substituteOracles(subst))

  // nc_IfTE: "no_conflict σ c1 ⟹ no_conflict σ c2 ⟹ no_conflict σ (IfTE e c1 c2)"
  override def noConflict(env: Environment, renaming: List[(Variable, Variable)]): Boolean =
    thenBranch.noConflict(env,renaming) && elseBranch.noConflict(env,renaming)

  override def renameVariables(env: Environment, renaming: List[(Variable, Variable)]): Statement =
    IfThenElse(condition.renameCVariables(renaming), thenBranch.renameVariables(env, renaming), elseBranch.renameVariables(env, renaming))
}

final case class While(condition:RichTerm, body: Block) extends Statement {
  lazy val hash : Hash[this.type] =
    HashTag()(Hashable.hash(condition), Hashable.hash(body))

  override def inline(name: String, oracles: List[String], program: Statement): Statement =
    While(condition,body.inline(name,oracles,program))
  override def toString: String = s"while ($condition) $body"

  override def checkWelltyped(context: IsabelleX.ContextX): Unit = {
    condition.checkWelltyped(context, GIsabelle.boolT)
    body.checkWelltyped(context)
  }
  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.whileProg $ condition.encodeAsExpression(context).isabelleTerm $ body.programListTermOld(context)
  override def simplify(isabelle: IsabelleX.ContextX, facts: List[String], thms: ListBuffer[Thm]): While =
    While(condition.simplify(isabelle,facts,thms),
      body.simplify(isabelle,facts,thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): While = While(condition, body.markOracles(oracles))

  override def substituteOracles(subst: Map[String, Call]): Statement = While(condition,body.substituteOracles(subst))

  // nc_While: "no_conflict σ c ⟹ no_conflict σ (While e c)"
  override def noConflict(env: Environment, renaming: List[(Variable, Variable)]): Boolean =
    body.noConflict(env, renaming)

  override def renameVariables(env: Environment, renaming: List[(Variable, Variable)]): While =
    While(condition.renameCVariables(renaming), body.renameVariables(env, renaming))
}

final case class QInit(location:VarTerm[QVariable], expression:RichTerm) extends Statement {
  lazy val hash : Hash[this.type] =
    HashTag()(Hashable.hash(location), Hashable.hash(expression))

  override def inline(name: String, oracles: List[String], program: Statement): Statement = this
  override def toString: String = s"${Variable.vartermToString(location)} <q $expression;"

  override def checkWelltyped(context: IsabelleX.ContextX): Unit = {
    val expected = GIsabelle.ell2T(GIsabelle.tupleT(location.map[Typ](_.valueTyp)))
    expression.checkWelltyped(context, expected)
  }
  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.qinit(Isabelle.tupleT(location.map(_.valueTyp):_*)) $ Isabelle.qvarTuple_var(location) $ expression.encodeAsExpression(context).isabelleTerm
  override def simplify(isabelle: IsabelleX.ContextX, facts: List[String], thms: ListBuffer[Thm]): QInit =
    QInit(location, expression.simplify(isabelle,facts,thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): QInit = this

  override def substituteOracles(subst: Map[String, Call]): Statement = this

  override def noConflict(env: Environment, renaming: List[(Variable, Variable)]): Boolean = true

  override def renameVariables(env: Environment, renaming: List[(Variable, Variable)]): QInit =
    QInit(location.map(_.substitute(renaming)), expression.renameCVariables(renaming))
}

final case class QApply(location:VarTerm[QVariable], expression:RichTerm) extends Statement {
  lazy val hash : Hash[this.type] =
    HashTag()(Hashable.hash(location), Hashable.hash(expression))

  override def inline(name: String, oracles: List[String], program: Statement): Statement = this
  override def toString: String = s"on ${Variable.vartermToString(location)} apply $expression;"

  override def checkWelltyped(context: IsabelleX.ContextX): Unit = {
    val varType = GIsabelle.tupleT(location.map[Typ](_.valueTyp))
    val expected = Type("Bounded_Operators.bounded", varType, varType)
    expression.checkWelltyped(context, expected)
  }
  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.qapply(Isabelle.tupleT(location.map(_.valueTyp):_*)) $ Isabelle.qvarTuple_var(location) $ expression.encodeAsExpression(context).isabelleTerm
  override def simplify(isabelle: IsabelleX.ContextX, facts: List[String], thms: ListBuffer[Thm]): QApply =
    QApply(location, expression.simplify(isabelle,facts,thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): QApply = this

  override def substituteOracles(subst: Map[String, Call]): Statement = this

  override def noConflict(env: Environment, renaming: List[(Variable, Variable)]): Boolean = true

  override def renameVariables(env: Environment, renaming: List[(Variable, Variable)]): QApply =
    QApply(location.map(_.substitute(renaming)), expression.renameCVariables(renaming))
}
final case class Measurement(result:VarTerm[CVariable], location:VarTerm[QVariable], e:RichTerm) extends Statement {
  lazy val hash : Hash[this.type] =
    HashTag()(Hashable.hash(result), Hashable.hash(location), Hashable.hash(e))

  override def inline(name: String, oracles: List[String], program: Statement): Statement = this
  override def toString: String = s"${Variable.vartermToString(result)} <- measure ${Variable.vartermToString(location)} in $e;"

  override def checkWelltyped(context: IsabelleX.ContextX): Unit = {
    val expected = Type("QRHL_Core.measurement",
      GIsabelle.tupleT(result.map[Typ](_.valueTyp)),
      GIsabelle.tupleT(location.map[Typ](_.valueTyp)))
    e.checkWelltyped(context, expected)
  }
  //  override def programTermOLD(context: Isabelle.Context): Term =
  //    Isabelle.measurement(Isabelle.tupleT(location.map(_.valueTyp):_*), result.valueTyp) $
  //      result.variableTerm $ Isabelle.qvarTuple_var(location) $ e.encodeAsExpression(context).isabelleTerm
  override def simplify(isabelle: IsabelleX.ContextX, facts: List[String], thms: ListBuffer[Thm]): Measurement =
    Measurement(result,location,e.simplify(isabelle,facts,thms))

  /** Replaces every program name x in Call-statements by @x if it x is listed in [oracles]
    * Fails if [this] already contains program names of the form @...
    */
  override def markOracles(oracles: List[String]): Measurement = this

  override def substituteOracles(subst: Map[String, Call]): Statement = this

  override def noConflict(env: Environment, renaming: List[(Variable, Variable)]): Boolean = true

  /** Renames all program variables. (subst_vars in Isabelle)
   *
   * @param renaming the substitution as an association list. Must not contain pairs (x,x), nor two pairs (x,y), (x,y'). */
  override def renameVariables(env: Environment, renaming: List[(Variable, Variable)]): Measurement =
    Measurement(result.map(_.substitute(renaming)), location.map(_.substitute(renaming)), e.renameCVariables(renaming))

}

final case class Call(name:String, args:Call*) extends Statement {
  lazy val hash : Hash[this.type] =
    HashTag()(Hashable.hash(name), Hashable.hash(args.toList))

  override def toString: String = "call "+toStringShort+";"
  def toStringShort: String =
    if (args.isEmpty) name else s"$name(${args.map(_.toStringShort).mkString(",")})"
  override def inline(name: String, oracles: List[String], program: Statement): Statement = this
  // TODO: Call.inline should actually inline something. Move the inlining code from Block.inline to here
  // Doing Block(this).inline(name, oracles, program) here is not a good idea, leads to infinite recursion

  override def checkWelltyped(context: IsabelleX.ContextX): Unit = {}

  override def simplify(isabelle: IsabelleX.ContextX, facts: List[String], thms: ListBuffer[Thm]): Call = this

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

  // lemma no_conflict_fv:
  //  assumes "var_subst_dom σ ∩ fv c = {}"
  //  shows "no_conflict σ c"
  // This lemma does not give the tightest bound (localvars_dom_no_conflict is tighter, for example, or we could traverse known programs).
  // But since replacing fails anyways if the domain of sigma contains free variables of a Call-statement, we use this simple overapproximation
  override def noConflict(env: Environment, renaming: List[(Variable, Variable)]): Boolean =
    (variableUse(env).freeVariables & (renaming map { _._1 }).toSet).isEmpty

  override def renameVariables(env: Environment, renaming: List[(Variable, Variable)]): Call = {
    val fv = variableUse(env).freeVariables
    for ((x,y) <- renaming)
      if (fv.contains(x))
        throw UserException(s"Cannot rename ${x.name} -> ${y.name} in $this because ${x.name} is in the free variables. Consider inlining ${this.name}")
    this
  }
}
