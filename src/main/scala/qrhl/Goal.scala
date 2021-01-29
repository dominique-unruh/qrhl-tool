package qrhl

import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.{Term, Thm}
import hashedcomputation.{Hash, HashTag, Hashable, HashedValue, WithByteArray}
import org.log4s
import qrhl.isabellex.IsabelleX.{ContextX, globalIsabelle => GIsabelle}
import GIsabelle.{Ops, show_oracles}
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.logic.{Block, Environment}

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

final case class QRHLSubgoal(left:Block, right:Block, pre:RichTerm, post:RichTerm, assumptions:List[RichTerm]) extends Subgoal {
  override def hash: Hash[QRHLSubgoal.this.type] =
    HashTag()(left.hash, right.hash, pre.hash, post.hash, Hashable.hash(assumptions))

  override def toString: String = {
    val assms = if (assumptions.isEmpty) "" else
      s"Assumptions:\n${assumptions.map(a => s"* $a\n").mkString}\n"
    s"${assms}Pre:   $pre\n\n${left.toStringMultiline("Left:  ")}\n\n${right.toStringMultiline("Right: ")}\n\nPost:  $post"
  }

  override def checkVariablesDeclared(environment: Environment): Unit = {
    for (x <- pre.variables)
      if (!environment.variableExistsForPredicate(x))
        throw UserException(s"Undeclared variable $x in precondition")
    for (x <- post.variables)
      if (!environment.variableExistsForPredicate(x))
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
    pre.checkWelltyped(context, GIsabelle.predicateT)
    post.checkWelltyped(context, GIsabelle.predicateT)
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
    QRHLSubgoal(left2, right2, pre2, post2, assms2)
  }
}

final case class AmbientSubgoal(goal: RichTerm) extends Subgoal {
  override def hash: Hash[AmbientSubgoal.this.type] =
    HashTag()(goal.hash)

  override def toString: String = goal.toString

  override def checkVariablesDeclared(environment: Environment): Unit =
    for (x <- goal.variables)
      if (!environment.variableExists(x))
        throw UserException(s"Undeclared variable $x")

  /** This goal as a boolean expression. */
  override def toTerm(context: IsabelleX.ContextX): RichTerm = goal

  override def containsAmbientVar(x: String): Boolean = goal.variables.contains(x)

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
}

object AmbientSubgoal {
  def apply(goal: Term, assms: Seq[Term]): AmbientSubgoal =
    new AmbientSubgoal(RichTerm(GIsabelle.boolT, assms.foldRight(goal) { (assm,goal) => GIsabelle.implies(assm,goal) }))
  def apply(goal: RichTerm, assms: Seq[RichTerm]): AmbientSubgoal =
    AmbientSubgoal(goal.isabelleTerm, assms.map(_.isabelleTerm))
}

case class GoalFocus(selector: String, subgoals: List[Subgoal]) extends IterableOnce[Subgoal] with HashedValue {
  def applyTactic(state: State, tactic: Tactic)(implicit output: PrintWriter): GoalFocus = new GoalFocus(selector,
    tactic.apply(state, subgoals.head) ++ subgoals.tail)

  def longDescription: String = {
    subgoals match {
      case Nil => "No current goal."
      case List(goal1) => s"Goal:\n\n" + goal1
      case List(goal1,rest @ _*) =>
        s"${subgoals.size} subgoals:\n\n" + goal1 + "\n\n----------------------------------------------------\n\n" + rest.mkString("\n\n")
    }
  }

  def isEmpty: Boolean = subgoals.isEmpty
  def length: Int = subgoals.length

  override def iterator: Iterator[Subgoal] = subgoals.iterator

  override def hash: Hash[GoalFocus.this.type] = HashTag()(Hashable.hash(selector), Hashable.hash(subgoals))
}

class Goal(subgoals: List[GoalFocus]) extends HashedValue with Iterable[Subgoal] {
  def longDescription: String = {
    if (isProved)
      "No current goal"
    else if (subgoals.head.isEmpty)
      "No focused goals"
    else if (subgoals.tail.isEmpty)
      subgoals.head.longDescription
    else
      subgoals.head.longDescription + "\n\n(Additionally, there are some unfocused goals.)"

  }

  def applyTactic(state: State, tactic: Tactic)(implicit output: PrintWriter): Goal =
    new Goal(subgoals.head.applyTactic(state, tactic) :: subgoals.tail)

  def isProved: Boolean = subgoals.forall(_.isEmpty)
  def focusOrUnfocus(focusVariant: String): Goal = ???
  override def hash: Hash[Goal.this.type] = HashTag()(Hashable.hash(subgoals))

  def length: Int = subgoals.map(_.length).sum

  override def iterator: Iterator[Subgoal] = subgoals.iterator.flatMap(_.iterator)
}

object Goal {
  val empty : Goal = new Goal(Nil)
  def apply(subgoal: Subgoal) = new Goal(List(GoalFocus("", List(subgoal))))
}
