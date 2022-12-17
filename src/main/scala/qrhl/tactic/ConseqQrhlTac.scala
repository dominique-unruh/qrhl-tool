package qrhl.tactic

import java.io.PrintWriter
import org.log4s
import qrhl._
import qrhl.isabellex.{IsabelleX, MLValueConverters, RichTerm}
import qrhl.logic.{ExpressionIndexed, Nonindexed, QVariable, QVariableNI, Variable}
import IsabelleX.{globalIsabelle => GIsabelle}
import GIsabelle.Ops
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.Term
import hashedcomputation.Implicits.optionHashable
import hashedcomputation.{Hash, HashTag, Hashable}
import qrhl.logic.Variable.{Index1, Index2}

import scala.collection.mutable.ListBuffer
import scala.collection.immutable.ListSet

// Implicits
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._
import MLValueConverters.Implicits._
import scala.concurrent.ExecutionContext.Implicits._
import GIsabelle.isabelleControl

import hashedcomputation.Implicits._

/**
 * If qvariableSubst=None, applies the rule:
 *
 * {pre2} left ~ right {post2}        (1)
 * pre <= pre2                        (8a)
 * post2 <= post                      (8b)
 * -------------------------
 * {pre} left ~ right {post}
 *
 *  Here (1) has to be given as the already proven theorem given by the argument `rule`
 *
 * ----------------------------------------------------------------
 *
 * Given qvariable substitution beforeLeft->afterLeft, beforeRight->afterRight, applies the rule
 *
 * {A ⊓ ⟦L⟧ ≡𝔮 ⟦R⟧} left ~ right {B ⊓ ⟦L'⟧ ≡𝔮 ⟦R'⟧}        (1)
 * type(beforeLeft) = type(beforeRight) (2a)
 * type(afterLeft) = type(afterRight) (2b)
 * (beforeLeft ∪ afterLeft) ∩ fv(left) = ∅ (3a)
 * (beforeRight ∪ afterRight) ∩ fv(right) = ∅ (3b)
 * each of before/afterLeft/right is on its own a distinct list (4)
 * | type(beforeLeft) | = ∞ ∨ | type(beforeLeft) | ≥ | type(afterLeft) |  (5)
 * LR, L'R', L*R*, L'*R'* each contains no duplicates (6)
 * A, B are colocal with before/afterLeft1/Right2 (7)
 * pre <= A ⊓ ⟦L*⟧ ≡𝔮 ⟦R*⟧        (8a)
 * post >= B ⊓ ⟦L'*⟧ ≡𝔮 ⟦R'*⟧    (8b)
 * --------------------------------------
 * {pre} left ~ right {post}
 *
 * where L*, L'* is L, L' with the suffix beforeLeft1 replaced by afterLeft1
 * and R*, R'* analogous with beforeRight2, afterRight2
 *
 * before/afterLeft1/Right2 is the corresponding variable list with index 1/2
 *
 * Here (1) has to be given as the already proven theorem given by the argument `rule`
 *
 * Premises (5), (7) are given as a single subgoal
 * (8a), (8b) are given as separate subgoals
 * (Three subgoals in total)
 *
 */
case class ConseqQrhlTac(rule: String,
                         qvariableSubst: Option[((List[QVariableNI],List[QVariableNI]),
                           (List[QVariableNI],List[QVariableNI]))]) extends Tactic {
  import ConseqQrhlTac.logger

  override def hash: Hash[ConseqQrhlTac.this.type] =
    HashTag()(Hashable.hash(rule), Hashable.hash(qvariableSubst))

  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case QRHLSubgoal(left,right,pre,post,assms) =>
      val env = state.environment
      val isabelle = state.isabelle.isabelle
      val ctxt = state.isabelle.context

      val ruleAsSubgoals = Ops.thms_as_subgoals(ctxt, rule).retrieveNow

      ruleAsSubgoals match {
        case List(QRHLSubgoal(left2, right2, pre2, post2, assms2)) =>
          if (left != left2)
            throw UserException(s"Left program in current subgoal and in $rule are not identical.\n  $left\nvs.\n  $left2")
          if (right != right2)
            throw UserException(s"Right program in current subgoal and in $rule are not identical.\n  $right\nvs.\n  $right2")
          if (assms2.nonEmpty)
            throw UserException(s"$rule contains assumptions, that is not supported.")

          val goals: ListBuffer[Subgoal] = ListBuffer()

          val (pre3: ExpressionIndexed, post3: ExpressionIndexed) = qvariableSubst match {
            case None => (pre2, post2)
            case Some(((beforeLeft, afterLeft), (beforeRight, afterRight))) =>
              // beforeLeft: Variables on the left that should be replaced
              // beforeRight: Variables on the right that should be replaced
              // afterLeft: Variables by which should be replaced on the left
              // afterRight: Variables by which should be replaced on the right

              var easyGoals = ListSet.empty: ListSet[Term]

              // Checking premise (2a)
              if (GIsabelle.tupleT(beforeLeft.map(_.valueTyp): _*) != GIsabelle.tupleT(beforeRight.map(_.valueTyp): _*))
                throw UserException(s"Variables ${Variable.varsToString(beforeLeft)} and ${Variable.varsToString(beforeRight)} must have the same type.")

              // Checking premise (2b)
              if (GIsabelle.tupleT(afterLeft.map(_.valueTyp): _*) != GIsabelle.tupleT(afterRight.map(_.valueTyp): _*))
                throw UserException(s"Variables ${Variable.varsToString(afterLeft)} and ${Variable.varsToString(afterRight)} must have the same type.")

              // Check that leftVars/rightVars do not occur in left/right program (premises (3a,3b))
              val leftInter = beforeLeft.toSet.union(afterLeft.toSet).intersect(left.variableUse(ctxt, env).quantum)
              if (leftInter.nonEmpty)
                throw UserException(s"Cannot replace variable(s) ${Variable.varsToString(leftInter)}, they are used in the left program.")
              val rightInter = beforeRight.toSet.union(afterRight.toSet).intersect(right.variableUse(ctxt, env).quantum)
              if (rightInter.nonEmpty)
                throw UserException(s"Cannot replace variable(s) ${Variable.varsToString(rightInter)}, they are used in the right program.")

              // Check that none of the variable lists contain duplicates. Premise (4)
              if (!Utils.areDistinct(beforeLeft))
                throw UserException(s"Variables ${Variable.varsToString(beforeLeft)} have repetitions")
              if (!Utils.areDistinct(beforeRight))
                throw UserException(s"Variables ${Variable.varsToString(beforeRight)} have repetitions")
              if (!Utils.areDistinct(afterLeft))
                throw UserException(s"Variables ${Variable.varsToString(afterLeft)} have repetitions")
              if (!Utils.areDistinct(afterRight))
                throw UserException(s"Variables ${Variable.varsToString(afterRight)} have repetitions")

              // beforeLeft as name/typ pairs
              val beforeLeftPairs = beforeLeft map { v => (v.name, v.valueTyp) }
              val beforeRightPairs = beforeRight map { v => (v.name, v.valueTyp) }
              val afterLeftPairs = afterLeft map { v => (v.name, v.valueTyp) }
              val afterRightPairs = afterRight map { v => (v.name, v.valueTyp) }

              // infinite (UNIV::beforeT set) ∨ (finite (UNIV::afterT set) ∧ card (UNIV::beforeT set) ≥ card (UNIV::afterT set)
              // Equivalent to (5).
              // In Isabelle, we need to explicitly make a case distinction on the finiteness of afterT because
              // card is the cardinality only in case of finite sets
              val cardinalityCondition1 = Ops.conseq_qrhl_cardinality_condition(
                MLValue((ctxt, beforeLeftPairs, afterLeftPairs))).retrieveNow
              // Add this to the goals that we need to check
              easyGoals += cardinalityCondition1

              // Like before/afterLeftPairs, but with index 1
              val beforeLeftIdxPairs = beforeLeft  map { v => (v.name, Index1, v.valueTyp) }
              val afterLeftIdxPairs = afterLeft map { v => (v.name, Index1, v.valueTyp) }
              // Like before/afterRightPairs, but with index 2
              val beforeRightIdxPairs = beforeRight map { v => (v.name, Index2, v.valueTyp) }
              val afterRightIdxPairs = afterRight map { v => (v.name, Index2, v.valueTyp) }

              // Parses pre2 as X ⊓ ⟦L⟧ ≡⇩𝔮 ⟦R⟧.
              // Checks that L/R ends with beforeLeftIdxPairs, beforeRightIdxPairs
              //   and replaces those by afterLeftIdxPairs, afterRightIdxPairs --> pre3
              // Also checks:
              //   quantum equality has no duplicate variables before replacement (6)
              //   quantum equality has no duplicate variables after replacement (6)
              // colocalityPre: subgoal that ensures that X is disjoint with beforeLeft/RightIdxPairs, afterLeft/RightIdxPairs, (7)
              val (pre3, colocalityPre) = Ops.conseq_qrhl_replace_in_predicate(
                ctxt, pre2.term.isabelleTerm,
                beforeLeftIdxPairs, afterLeftIdxPairs, beforeRightIdxPairs, afterRightIdxPairs).retrieveNow
              easyGoals += colocalityPre

              // Same for postcondition
              val (post3, colocalityPost) = Ops.conseq_qrhl_replace_in_predicate(
                ctxt, post2.term.isabelleTerm,
                beforeLeftIdxPairs, afterLeftIdxPairs, beforeRightIdxPairs, afterRightIdxPairs).retrieveNow
              easyGoals += colocalityPost

              goals += AmbientSubgoal(GIsabelle.conj(easyGoals.toSeq: _*), assms.map(_.isabelleTerm))

              (RichTerm(pre3), RichTerm(post3))
          }

          // (8a), (8b)
          goals += AmbientSubgoal(pre.leq(pre3), assms)
          goals += AmbientSubgoal(post3.leq(post), assms)

          goals.toList
        case List(goal : AmbientSubgoal) =>
          logger.debug(goal.toString)
          throw UserException(s"Theorem $rule does not refer to a qRHL judgment")
        case _::_ =>
          throw UserException(s"Theorem $rule consists of several theorems")
      }


//
//
//      var goals = List(QRHLSubgoal(left,right,pre.getOrElse(pre2),post.getOrElse(post2),assms)) : List[Subgoal]
//      pre match {
//        case None =>
//        case Some(e) => goals = AmbientSubgoal(pre2.leq(e)).addAssumptions(assms) :: goals
//      }
//      post match {
//        case None =>
//        case Some(e) => goals = AmbientSubgoal(e.leq(post2)).addAssumptions(assms) :: goals
//      }
//      goals
    case _ => throw UserException("Expected a qRHL subgoal")
  }
}

object ConseqQrhlTac {
  private val logger = log4s.getLogger
}