package qrhl

import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.{ConcreteTerm, Cterm, MLValueTerm, Term, Thm}
import hashedcomputation.{Hash, HashTag, Hashable, HashedValue, WithByteArray}
import org.log4s
import qrhl.isabellex.IsabelleX.{ContextX, globalIsabelle => GIsabelle}
import GIsabelle.{Ops, show_oracles}
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.logic.{Block, Environment}
import scalaz.Heap.Empty

import java.io.PrintWriter
import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer

// Implicits
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import qrhl.isabellex.MLValueConverters.Implicits._
import scala.concurrent.ExecutionContext.Implicits._
import GIsabelle.isabelleControl
import hashedcomputation.Implicits._
import qrhl.isabellex.Implicits._

sealed trait Subgoal extends HashedValue {
  /** If the subgoal is of the form "true_expression Expr[...]", replace it by "...". */
  def unwrapTrueExpression(implicit context: IsabelleX.ContextX): Subgoal

  def simplify(isabelle: IsabelleX.ContextX, facts: List[String], everywhere:Boolean): Subgoal

  /** Checks whether all isabelle terms in this goal are well-typed.
   * Should always succeed, unless there are bugs somewhere. */
  def checkWelltyped(context: IsabelleX.ContextX): Unit

  /** This goal as a boolean term. (A valid Isabelle representation of this goal.) */
  def toTerm(context:IsabelleX.ContextX): RichTerm

  def checkVariablesDeclared(environment: Environment): Unit

  def containsAmbientVar(x: String) : Boolean

  @tailrec
  final def addAssumptions(assms: List[RichTerm]): Subgoal = assms match {
    case Nil => this
    case a::as => addAssumption(a).addAssumptions(as)
  }

  def addAssumption(assm: RichTerm): Subgoal
}

object Subgoal {
  private val logger = log4s.getLogger

  def printOracles(thms : Thm*): Unit = {
    for (thm <- thms)
      show_oracles(thm)
  }
}

object QRHLSubgoal {
  private val logger = log4s.getLogger
}

/**
 * @param pre Precondition in shortform
 * @param post Postcondition in shortform
 * */
final case class QRHLSubgoal(left:Block, right:Block, pre:RichTerm, post:RichTerm, assumptions:List[RichTerm]) extends Subgoal {
  checkQRHLSubgoalType()

  private def checkQRHLSubgoalType(): Unit = {
    if (pre.typ != GIsabelle.predExpressionT)
      throw UserException(s"Internal error: precondition has type ${IsabelleX.theContext.prettyTyp(pre.typ)}")
    if (post.typ != GIsabelle.predExpressionT)
      throw UserException(s"Internal error: postcondition has type ${IsabelleX.theContext.prettyTyp(post.typ)}")
    for (assm <- assumptions)
      assert(assm.typ == GIsabelle.boolT)
  }

  override def hash: Hash[QRHLSubgoal.this.type] =
    HashTag()(left.hash, right.hash, pre.hash, post.hash, Hashable.hash(assumptions))

  override def toString: String = {
    val assms = if (assumptions.isEmpty) "" else
      s"Assumptions:\n${assumptions.map(a => s"* $a\n").mkString}\n"
    s"${assms}Pre:   $pre\n\n${left.toStringMultiline("Left:  ")}\n\n${right.toStringMultiline("Right: ")}\n\nPost:  $post"
  }

  override def checkVariablesDeclared(environment: Environment): Unit = {
    for (x <- pre.variables)
      if (!environment.variableExistsForPredicateLongform(x))
        throw UserException(s"Undeclared variable $x in precondition")
    for (x <- post.variables)
      if (!environment.variableExistsForPredicateLongform(x))
        throw UserException(s"Undeclared variable $x in postcondition")
    for (x <- left.variablesDirect)
      if (!environment.variableExistsForProg(x))
        throw UserException(s"Undeclared variable $x in left program")
    for (x <- right.variablesDirect)
      if (!environment.variableExistsForProg(x))
        throw UserException(s"Undeclared variable $x in left program")
    for (a <- assumptions; x <- a.variables)
      if (!environment.variableExists(x))
        throw UserException(s"Undeclared variable $x in assumptions")
  }

  override def toTerm(context: IsabelleX.ContextX): RichTerm = {
    val mlVal = MLValue((context.context,left.statements,right.statements,pre.isabelleTerm,post.isabelleTerm,assumptions.map(_.isabelleTerm)))
    val term = Ops.qrhl_subgoal_to_term_op(mlVal).retrieveNow
    RichTerm(term)
  }

  /** Not including ambient vars in nested programs (via Call) */
  override def containsAmbientVar(x: String): Boolean = {
    pre.variables.contains(x) || post.variables.contains(x) ||
      left.variablesDirect.contains(x) || right.variablesDirect.contains(x) ||
      assumptions.exists(_.variables.contains(x))
  }

  override def addAssumption(assm: RichTerm): QRHLSubgoal = {
    assert(assm.typ==GIsabelle.boolT)
    QRHLSubgoal(left,right,pre,post,assm::assumptions)
  }

  /** Checks whether all isabelle terms in this goal are well-typed.
   * Should always succeed, unless there are bugs somewhere. */
  override def checkWelltyped(context:IsabelleX.ContextX): Unit = {
    for (a <- assumptions) a.checkWelltyped(context, GIsabelle.boolT)
    left.checkWelltyped(context)
    right.checkWelltyped(context)
    pre.checkWelltyped(context, GIsabelle.predExpressionT)
    post.checkWelltyped(context, GIsabelle.predExpressionT)
  }

  override def simplify(isabelle: IsabelleX.ContextX, facts: List[String], everywhere:Boolean): QRHLSubgoal = {
    //    if (assumptions.nonEmpty) QRHLSubgoal.logger.warn("Not using assumptions for simplification")
    val thms = new ListBuffer[Thm]()
    val assms2 = assumptions.map(_.simplify(isabelle,facts,thms))
    val assms3: List[RichTerm] = assms2.filter(_.isabelleTerm!=GIsabelle.True_const)
    val pre2 = pre.simplify(isabelle,facts,thms)
    val post2 = post.simplify(isabelle,facts,thms)
    val left2 = if (everywhere) left.simplify(isabelle,facts,thms) else left
    val right2 = if (everywhere) right.simplify(isabelle,facts,thms) else right

    Subgoal.printOracles(thms.toSeq : _*)
    QRHLSubgoal(left2, right2, pre2, post2, assms3)
  }

  /** If the subgoal is of the form "true_expression Expr[...]", replace it by "...". */
  override def unwrapTrueExpression(implicit context: IsabelleX.ContextX): QRHLSubgoal = this
}


final case class DenotationalEqSubgoal(left:Block, right:Block, assumptions:List[RichTerm]) extends Subgoal {
  override def hash: Hash[DenotationalEqSubgoal.this.type] =
    HashTag()(left.hash, right.hash, Hashable.hash(assumptions))

  override def toString: String = {
    val assms = if (assumptions.isEmpty) "" else
      s"Assumptions:\n${assumptions.map(a => s"* $a\n").mkString}\n"
    s"${assms}Denotational equivalence:\n\n${left.toStringMultiline("Left:  ")}\n\n${right.toStringMultiline("Right: ")}"
  }

  override def checkVariablesDeclared(environment: Environment): Unit = {
    for (x <- left.variablesDirect)
      if (!environment.variableExistsForProg(x))
        throw UserException(s"Undeclared variable $x in left program")
    for (x <- right.variablesDirect)
      if (!environment.variableExistsForProg(x))
        throw UserException(s"Undeclared variable $x in left program")
    for (a <- assumptions; x <- a.variables)
      if (!environment.variableExists(x))
        throw UserException(s"Undeclared variable $x in assumptions")
  }

  override def toTerm(context: IsabelleX.ContextX): RichTerm = {
    val term = Ops.denotational_eq_subgoal_to_term_op(
      context.context, Block.makeBlockIfNeeded(left.statements), Block.makeBlockIfNeeded(right.statements), assumptions.map(_.isabelleTerm))
      .retrieveNow
    RichTerm(term)
  }

  /** Not including ambient vars in nested programs (via Call) */
  override def containsAmbientVar(x: String): Boolean = {
    left.variablesDirect.contains(x) || right.variablesDirect.contains(x) ||
      assumptions.exists(_.variables.contains(x))
  }

  override def addAssumption(assm: RichTerm): DenotationalEqSubgoal = {
    assert(assm.typ == GIsabelle.boolT)
    DenotationalEqSubgoal(left, right, assm :: assumptions)
  }

  /** Checks whether all isabelle terms in this goal are well-typed.
   * Should always succeed, unless there are bugs somewhere. */
  override def checkWelltyped(context:IsabelleX.ContextX): Unit = {
    for (a <- assumptions) a.checkWelltyped(context, GIsabelle.boolT)
    left.checkWelltyped(context)
    right.checkWelltyped(context)
  }

  override def simplify(isabelle: IsabelleX.ContextX, facts: List[String], everywhere:Boolean): DenotationalEqSubgoal = {
    //    if (assumptions.nonEmpty) QRHLSubgoal.logger.warn("Not using assumptions for simplification")
    val thms = new ListBuffer[Thm]()
    val assms2 = assumptions.map(_.simplify(isabelle,facts,thms))
//    val assms3: List[RichTerm] = assms2.filter(_.isabelleTerm!=GIsabelle.True_const)
    val left2 = if (everywhere) left.simplify(isabelle,facts,thms) else left
    val right2 = if (everywhere) right.simplify(isabelle,facts,thms) else right

//    Subgoal.printOracles(thms.toSeq : _*)
    DenotationalEqSubgoal(left2, right2, assms2)
  }

  /** If the subgoal is of the form "true_expression Expr[...]", replace it by "...". */
  override def unwrapTrueExpression(implicit context: IsabelleX.ContextX): DenotationalEqSubgoal = this
}

final case class AmbientSubgoal(goal: RichTerm) extends Subgoal {
  private val variables: Set[String] = goal.variables
  checkMemoryVariable()

  private def checkMemoryVariable(): Unit =
    if (variables.contains("_memory"))
      throw UserException("Variable _memory occurs in the goal. This should not happen and is a bug.")

  override def hash: Hash[AmbientSubgoal.this.type] =
    HashTag()(goal.hash)

  override def toString: String = goal.toString

  override def checkVariablesDeclared(environment: Environment): Unit =
    for (x <- variables)
      if (!environment.variableExists(x))
        throw UserException(s"Undeclared variable $x")

  /** This goal as a boolean expression. */
  override def toTerm(context: IsabelleX.ContextX): RichTerm = goal

  override def containsAmbientVar(x: String): Boolean = variables.contains(x)

  override def addAssumption(assm: RichTerm): AmbientSubgoal = {
    assert(assm.typ == GIsabelle.boolT)
    AmbientSubgoal(assm.implies(goal))
  }

  /** Checks whether all isabelle terms in this goal are well-typed.
   * Should always succeed, unless there are bugs somewhere. */
  override def checkWelltyped(context: IsabelleX.ContextX): Unit = goal.checkWelltyped(context, GIsabelle.boolT)

  override def simplify(isabelle: IsabelleX.ContextX, facts: List[String], everywhere:Boolean): AmbientSubgoal = {
    val (term, thm) = goal.simplify(isabelle, facts)
    Subgoal.printOracles(thm)
    AmbientSubgoal(term)
  }

  /** If the subgoal is of the form "true_expression Expr[...]", replace it by "...". */
  override def unwrapTrueExpression(implicit context: IsabelleX.ContextX): AmbientSubgoal = new AmbientSubgoal(goal.unwrapTrueExpression)
}

object AmbientSubgoal {
  def apply(goal: Term, assms: Seq[Term]): AmbientSubgoal =
    new AmbientSubgoal(RichTerm(GIsabelle.boolT, assms.foldRight(goal) { (assm,goal) => GIsabelle.implies(assm,goal) }))
  def apply(goal: RichTerm, assms: Seq[RichTerm]): AmbientSubgoal =
    AmbientSubgoal(goal.isabelleTerm, assms.map(_.isabelleTerm))
}

case class GoalFocus(label: String, subgoals: List[Subgoal]) extends IterableOnce[Subgoal] with HashedValue {
  def isBraceFocus: Boolean = label == "{"

  def applyTactic(state: State, tactic: Tactic)(implicit output: PrintWriter): GoalFocus = {
    if (subgoals.isEmpty)
      throw UserException("Cannot apply the tactic because there is no current goal.")
    GoalFocus(label, tactic.apply(state, subgoals.head) ++ subgoals.tail)
  }

  def longDescription: String = {
    subgoals match {
      case Nil => "No current goal."
      case List(goal1) => s"Goal:\n\n" + goal1
      case List(goal1,rest @ _*) =>
        s"${subgoals.size} subgoals:\n\n" + goal1 + "\n\n----------------------------------------------------\n\n" + rest.mkString("\n\n")
    }
  }

  def isEmpty: Boolean = subgoals.isEmpty
  def nonEmpty: Boolean = !isEmpty
  def length: Int = subgoals.length

  override def iterator: Iterator[Subgoal] = subgoals.iterator

  override def hash: Hash[GoalFocus.this.type] = HashTag()(Hashable.hash(label), Hashable.hash(subgoals))
}

/**
 * Invariant:
 * - every GoalFocus is nonempty except brace foci, and the head
 * - only the last (i.e., outer) GoalFocus can have label ""
 */
class Goal(
            /** Goal focus stack. `foci.head` contains the currently focused subgoals. */
            foci: List[GoalFocus]) extends HashedValue with Iterable[Subgoal] {
  checkInvariant()

  def focusedSubgoals: List[Subgoal] = foci.headOption.map(_.subgoals).getOrElse(Nil)

  def checkInvariant(): Unit = {
    if (foci.nonEmpty) {
      assert(!foci.tail.exists(f => f.isEmpty && !f.isBraceFocus))
      assert(!foci.dropRight(1).exists(_.label == ""))
    }
  }

  def applicableUnfocusCommand: String = {
    if (foci.isEmpty) throw new IllegalStateException("Cannot unfocus with no pending foci")
    if (foci.head.nonEmpty) throw new IllegalStateException("Cannot unfocus while there are focused subgoals")
    else if (foci.head.isBraceFocus) "}"
    else if (foci.tail.head.isBraceFocus) "}"
    else foci.tail.head.label
  }

  def unfocusedShortDescription: String = {
    foci.tail.map { focus =>
      (if (focus.isBraceFocus) "{}" else focus.label) +
        (if (focus.length == 1) "" else " " + focus.length)
    } mkString(", ")
  }


  def longDescription: String = {
    if (isProved)
      "No current goal."
    else if (foci.head.isEmpty)
      s"No focused goals (use ${applicableUnfocusCommand} to unfocus)"
    else if (foci.tail.isEmpty)
      foci.head.longDescription
    else
      foci.head.longDescription + s"\n\n(Additionally, there are some unfocused goals: $unfocusedShortDescription)"

  }

  def applyTactic(state: State, tactic: Tactic)(implicit output: PrintWriter): Goal =
    new Goal(foci.head.applyTactic(state, tactic) :: foci.tail)

  def isProved: Boolean =
    foci.isEmpty || (foci.tail.isEmpty && foci.head.isEmpty && !foci.head.isBraceFocus)

  def focusBrace(selector: SubgoalSelector): Goal = {
    if (isProved) throw UserException("Proof is finished, cannot focus")
    val firstFocus = foci.head
    if (firstFocus.isEmpty) throw UserException("No subgoal to focus on")
    val (focused, remaining) = selector.select(firstFocus.subgoals)
    val remainingFocus = GoalFocus(firstFocus.label, remaining)
    val newFocus = GoalFocus("{", focused)
    if (remainingFocus.nonEmpty || remainingFocus.isBraceFocus)
      new Goal(newFocus :: remainingFocus :: foci.tail)
    else
      new Goal(newFocus :: foci.tail)
  }

  def unfocusBrace(): Goal = {
    if (isProved) throw UserException("Proof is finished, cannot unfocus")
    var foci = this.foci
    if (foci.head.nonEmpty) throw UserException("Cannot unfocus, there are focused subgoals remaining")
    while (foci.nonEmpty && foci.head.isEmpty && !foci.head.isBraceFocus) foci = foci.tail
    if (foci.isEmpty) throw UserException("No enclosing {}-focus.")
    if (!foci.head.isBraceFocus) throw UserException(s"Cannot unfocus using } here.")
    new Goal(foci.tail)
  }

  def isActiveFocusLabel(label: String): Boolean = {
    for (focus <- foci) {
      if (focus.isBraceFocus)
        return false
      else if (focus.label == label)
        return true
    }
    false
  }

  def unfocus(label: String): Goal = {
    if (isProved) throw UserException("Proof is finished, cannot unfocus")
    else if (foci.isEmpty) throw UserException("Nothing to unfocus")
    else if (foci.head.nonEmpty) throw UserException("Cannot unfocus, there are focused subgoals remaining")
    else if (foci.head.isBraceFocus) throw UserException(s"Cannot unfocus using $label, use } to unfocus")
    else if (foci.tail.isEmpty) throw UserException("Nothing to unfocus")
    else if (foci.tail.head.isBraceFocus) throw UserException(s"Cannot unfocus using $label, use } to unfocus")
    else if (foci.tail.head.label == "") throw new IllegalStateException("Unexpected \"\" focus label")
    else if (foci.tail.head.label != label) throw UserException(s"Cannot unfocus using $label, use ${foci.tail.head.label} to unfocus")
    else new Goal(foci.tail)
  }

  def focus(selector: SubgoalSelector, label: String): Goal = {
    if (foci.isEmpty)
      throw UserException("No subgoals.")
    val firstFocus = foci.head
    val (focused, remaining) = selector.select(firstFocus.subgoals)
    val newFoci = focused.map(subgoal => GoalFocus(label, List(subgoal)))
    val remainingFocus = GoalFocus(firstFocus.label, remaining)
    if (remainingFocus.nonEmpty)
      throw UserException(s"Cannot focus on subset of subgoals using bullets ($label). " +
        s"""Try "$selector: {" instead. Or select all goals.""")
    if (remainingFocus.isBraceFocus)
      new Goal(newFoci ++ (remainingFocus :: foci.tail))
    else
      new Goal(newFoci ++ foci.tail)
  }

  def focusOrUnfocus(selector: Option[SubgoalSelector], label: String): Goal = label match {
    case "{" => focusBrace(selector.getOrElse(SubgoalSelector.First))
    case "}" =>
      if (selector.nonEmpty)
        throw UserException(s"Unfocusing subgoals, but a subgoal selector ${selector.get} is given.")
      unfocusBrace()
    case _ =>
      if (isActiveFocusLabel(label)) {
        if (selector.nonEmpty)
          throw UserException(s"Unfocusing subgoals, but a subgoal selector ${selector.get} is given.")
        unfocus(label)
      } else
        focus(selector.getOrElse(SubgoalSelector.All), label)
  }

  override def hash: Hash[Goal.this.type] = HashTag()(Hashable.hash(foci))

  def length: Int = foci.map(_.length).sum

  override def iterator: Iterator[Subgoal] = foci.iterator.flatMap(_.iterator)
}

object Goal {
  val empty : Goal = new Goal(Nil)
  def apply(subgoal: Subgoal) = new Goal(List(GoalFocus("", List(subgoal))))
}

trait SubgoalSelector extends HashedValue {
  def select(subgoals: List[Subgoal]): (List[Subgoal], List[Subgoal]) = {
    val selected = select0(subgoals)
    val unselected = subgoals.filter(s1 => !selected.exists(s2 => s1 eq s2))
    (selected, unselected)
  }
  def select0(subgoals: List[Subgoal]): List[Subgoal]
}

object SubgoalSelector {
  val First: Single = Single(1)

  object All extends SubgoalSelector {
    override def toString: String = "all"
    override val hash: Hash[All.this.type] = HashTag()()
    override def select0(subgoals: List[Subgoal]): List[Subgoal] = subgoals
    override def select(subgoals: List[Subgoal]): (List[Subgoal], List[Subgoal]) = (subgoals, Nil)
  }

  case class Single(index: Int) extends SubgoalSelector {
    assert(index >= 1)
    override lazy val hash: Hash[Single.this.type] = HashTag()(Hashable.hash(index))
    override def toString: String = index.toString
    override def select0(subgoals: List[Subgoal]): (List[Subgoal]) = {
      if (subgoals.isEmpty) throw UserException("No subgoal to focus on.")
      if (subgoals.length < index) throw UserException(s"Only ${subgoals.length} focused subgoals, cannot focus on ${index}th")
      List(subgoals(index-1))
    }
  }

  case class Range(start: Int, end: Int) extends SubgoalSelector {
    assert(start >= 1)
    assert(end >= start)
    override lazy val hash: Hash[Range.this.type] = HashTag()(Hashable.hash(start), Hashable.hash(end))
    override def toString: String = s"$start-$end"

    override def select0(subgoals: List[Subgoal]): List[Subgoal] =  {
      if (subgoals.isEmpty) throw UserException("No subgoal to focus on.")
      if (subgoals.length < end) throw UserException(s"Only ${subgoals.length} focused subgoals, cannot focus on ${end}th")
      subgoals.slice(start-1, end)
    }
  }

  case object Empty extends SubgoalSelector {
    override def toString: String = "none"
    override def hash: Hash[Empty.this.type] = HashTag()()

    override def select0(subgoals: List[Subgoal]): List[Subgoal] = Nil
    override def select(subgoals: List[Subgoal]): (List[Subgoal], List[Subgoal]) = (Nil, subgoals)
  }

  case class Union private (selectors: List[SubgoalSelector]) extends SubgoalSelector {
    assert(selectors.nonEmpty)
    assert(selectors.tail.nonEmpty)
    override lazy val hash: Hash[this.type] = HashTag()(Hashable.hash(selectors))
    override def toString: String = selectors.mkString(",")

    override def select0(subgoals: List[Subgoal]): List[Subgoal] =
      for (selector <- selectors;
           subgoal <- selector.select0(subgoals))
        yield subgoal
  }

  object Union {
    def apply(selectors: List[SubgoalSelector]): SubgoalSelector = selectors match {
      case Nil => Empty
      case List(x) => x
      case _ => new Union(selectors)
    }
  }
}
