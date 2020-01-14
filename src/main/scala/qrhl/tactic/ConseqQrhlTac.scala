package qrhl.tactic

import info.hupel.isabelle.Operation
import info.hupel.isabelle.pure.{Term, Typ}
import org.log4s
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.logic.QVariable

import scala.collection.mutable.ListBuffer
import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec
import qrhl.isabelle.Codecs._

import scala.collection.immutable.ListSet

case class ConseqQrhlTac(rule: String, qvariableSubst: Option[((List[QVariable],List[QVariable]),(List[QVariable],List[QVariable]))]) extends Tactic {
  import ConseqQrhlTac.logger

  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case QRHLSubgoal(left,right,pre,post,assms) =>
      state.isabelle.isabelle.invoke(Isabelle.thms_as_subgoals,(state.isabelle.contextId,rule)) match {
        case List(QRHLSubgoal(left2,right2,pre2,post2,assms2)) =>
          if (left!=left2)
            throw UserException(s"Left program in current subgoal and in $rule are not identical.\n  $left\nvs.\n  $left2")
          if (right!=right2)
            throw UserException(s"Right program in current subgoal and in $rule are not identical.\n  $right\nvs.\n  $right2")
          if (assms2.nonEmpty)
            throw UserException(s"$rule contains assumptions, that is not supported.")

          val goals : ListBuffer[Subgoal] = ListBuffer()

          def varNames(vars:Iterable[QVariable]) = {
            vars map (_.variableName) mkString ", "
          }

          val (pre3, post3) = if (qvariableSubst.isEmpty) (pre2,post2)
          else {
            val env = state.environment
            val isabelle = state.isabelle.isabelle
            val contextId = state.isabelle.contextId
            var easyGoals = ListSet.empty : ListSet[Term]

            val leftVars = qvariableSubst.get._1
            val rightVars = qvariableSubst.get._2
            // Variables on the left that should be replaced
            val beforeLeft = leftVars._1
            // Variables on the right that should be replaced
            val beforeRight = rightVars._1
            // Variables by which should be replaced on the left
            val afterLeft = leftVars._2
            // Variables by which should be replaced on the right
            val afterRight = rightVars._2

            if (Isabelle.tupleT(beforeLeft.map(_.valueTyp):_*) != Isabelle.tupleT(beforeRight.map(_.valueTyp):_*))
              throw UserException(s"Variables ${varNames(beforeLeft)} and ${varNames((beforeRight))} must have the same type.")

            if (Isabelle.tupleT(afterLeft.map(_.valueTyp):_*) != Isabelle.tupleT(afterRight.map(_.valueTyp):_*))
              throw UserException(s"Variables ${varNames(afterLeft)} and ${varNames((afterRight))} must have the same type.")
            
            // Check that leftVars/rightVars do not occur in left/right program
            val leftInter = beforeLeft.toSet.union(afterLeft.toSet).intersect(left.variableUse(env).quantum)
            if (leftInter.nonEmpty)
              throw UserException(s"Cannot replace variable(s) ${varNames(leftInter)}, they are used in the left program.")
            val rightInter = beforeRight.toSet.union(afterRight.toSet).intersect(right.variableUse(env).quantum)
            if (rightInter.nonEmpty)
              throw UserException(s"Cannot replace variable(s) ${varNames(rightInter)}, they are used in the right program.")

            // Check that none of the variable lists contain duplicates
            if (!Utils.areDistinct(beforeLeft))
              throw UserException(s"Variables ${varNames(beforeLeft)} have repetitions")
            if (!Utils.areDistinct(beforeRight))
              throw UserException(s"Variables ${varNames(beforeRight)} have repetitions")
            if (!Utils.areDistinct(afterLeft))
              throw UserException(s"Variables ${varNames(afterLeft)} have repetitions")
            if (!Utils.areDistinct(afterRight))
              throw UserException(s"Variables ${varNames(afterRight)} have repetitions")

            val beforeLeftPairs = beforeLeft map { v => (v.variableName, v.valueTyp)}
            val beforeRightPairs = beforeRight map { v => (v.variableName, v.valueTyp)}
            val afterLeftPairs = afterLeft map { v => (v.variableName, v.valueTyp)}
            val afterRightPairs = afterRight map { v => (v.variableName, v.valueTyp)}

            val cardinalityCondition1 = isabelle.invoke(ConseqQrhlTac.conseq_qrhl_cardinality_condition,
              (contextId, beforeLeftPairs, afterLeftPairs))
            easyGoals += cardinalityCondition1.isabelleTerm

//            if (leftVars != rightVars) {
//              val cardinalityCondition2 = AmbientSubgoal(isabelle.invoke(ConseqQrhlTac.conseq_qrhl_cardinality_condition,
//                (contextId, beforeRightPairs, afterRightPairs)))
//              goals += cardinalityCondition2
//            }

//            val beforeIdx = (beforeLeft.map(_.index1) ++ beforeRight.map(_.index2))  map { v => (v.variableName, v.valueTyp)}
//            val afterIdx = (afterLeft.map(_.index1) ++ afterRight.map(_.index2))  map { v => (v.variableName, v.valueTyp)}
//            val indexedVars = (beforeIdx ++ afterIdx).distinct

            val beforeLeftIdxPairs = beforeLeft.map(_.index1)  map { v => (v.variableName, v.valueTyp)}
            val afterLeftIdxPairs = afterLeft.map(_.index1)  map { v => (v.variableName, v.valueTyp)}
            val beforeRightIdxPairs = beforeRight.map(_.index2)  map { v => (v.variableName, v.valueTyp)}
            val afterRightIdxPairs = afterRight.map(_.index2)  map { v => (v.variableName, v.valueTyp)}

            val (pre3, colocalityPre) = isabelle.invoke(ConseqQrhlTac.conseq_qrhl_replace_in_predicate,
              (contextId, pre2.isabelleTerm, beforeLeftIdxPairs, afterLeftIdxPairs, beforeRightIdxPairs, afterRightIdxPairs))
            easyGoals += colocalityPre.isabelleTerm
            
            val (post3, colocalityPost) = isabelle.invoke(ConseqQrhlTac.conseq_qrhl_replace_in_predicate,
              (contextId, post2.isabelleTerm, beforeLeftIdxPairs, afterLeftIdxPairs, beforeRightIdxPairs, afterRightIdxPairs))
            easyGoals += colocalityPost.isabelleTerm

            goals += AmbientSubgoal(Isabelle.conj(easyGoals.toSeq : _*), assms.map(_.isabelleTerm))

            (pre3, post3)
          }

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

  private val conseq_qrhl_cardinality_condition = Operation.implicitly[
    (BigInt,List[(String,Typ)],List[(String,Typ)]),
    RichTerm]("conseq_qrhl_cardinality_condition")

  private val conseq_qrhl_replace_in_predicate = Operation.implicitly[
    (BigInt, Term, List[(String,Typ)], List[(String,Typ)], List[(String,Typ)], List[(String,Typ)]),
    (RichTerm, RichTerm)]("conseq_qrhl_replace_in_predicate")
}