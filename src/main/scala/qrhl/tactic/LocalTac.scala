package qrhl.tactic

import info.hupel.isabelle.pure.{App, Const, Term, Typ}
import org.log4s
import qrhl.isabelle.Isabelle.{Inf, QuantumEqualityFull, predicateT, predicate_inf, predicate_top}
import qrhl.isabelle.{Isabelle, IsabelleConsts, RichTerm}
import qrhl.logic.{Block, Local, QVariable}
import qrhl.tactic.FrameRuleTac.colocalityOp
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException}
import qrhl.tactic.LocalTac.{Mode, logger}

case class LocalTac(mode: Mode) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = mode match {
    case LocalTac.joint => applyJoint(state, goal)
    case LocalTac.left => apply1(state, goal, left=true)
    case LocalTac.right => apply1(state, goal, left=false)
  }

  /** Assumes that s1,s2 have same length and matching types */
  private def extendQeq(us1: Term, s1: Term, us2: Term, s2: Term, qvarsL: List[QVariable], qvarsR: List[QVariable]) = {
    import Isabelle.{variable_concat, variable_singleton, quantum_equality_full, idOp, ell2T}
    var us1_ = us1
    var us2_ = us2
    var s1_ = s1
    var s2_ = s2

    for ((q1,q2) <- qvarsL.zip(qvarsR).reverse) {
      s1_ = variable_concat(variable_singleton(q1.index1.variableTerm),s1_)
      s2_ = variable_concat(variable_singleton(q2.index2.variableTerm),s2_)
      us1_ = Isabelle.tensorOp(idOp(ell2T(q1.valueTyp)), us1_)
      us2_ = Isabelle.tensorOp(idOp(ell2T(q2.valueTyp)), us2_)
    }

    quantum_equality_full(us1_, s1_, us2_, s2_)
  }

  def applyJoint(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case AmbientSubgoal(goal) =>
      throw UserException("Expected qRHL goal")
    case QRHLSubgoal(leftProg, rightProg, pre, post, assumptions) =>
      val env = state.environment
      val context = state.isabelle

      // Decomposing left/right program
      val (cvarsL, qvarsL, bodyL) = leftProg match {
        case Block(Local(cvars, qvars, body)) => (cvars, qvars, body)
        case _ => throw UserException(s"Expected left program to be of the form { local ...; ... }")
      }

      val (cvarsR, qvarsR, bodyR) = rightProg match {
        case Block(Local(cvars, qvars, body)) => (cvars, qvars, body)
        case _ => throw UserException(s"Expected right program to be of the form { local ...; ... }")
      }


      def decomposePredicate(which: String, pred: RichTerm) = {
        pred.isabelleTerm match {
          case Inf(main,QuantumEqualityFull(u1,v1,u2,v2)) => (main,u1,v1,u2,v2)
          case QuantumEqualityFull(u1,v1,u2,v2) => (predicate_top,u1,v1,u2,v2)
          case _ => throw UserException(s"""Expected $which to be of the form "A ⊓ Q" where Q is a quantum equality""")
        }
      }

      val (a, us1, s1, us2, s2) = decomposePredicate("precondition", pre)
      val (b, ur1, r1, ur2, r2) = decomposePredicate("postcondition", post)

      // TODO remove
      def p(t:Term) = Isabelle.pretty(t)
      logger.debug(s"A:   ${p(a)}")
      logger.debug(s"US:  ${p(us1)}")
      logger.debug(s"S:   ${p(s1)}")
      logger.debug(s"US': ${p(us2)}")
      logger.debug(s"S':  ${p(s2)}")
      logger.debug(s"B:   ${p(b)}")
      logger.debug(s"UR:  ${p(ur1)}")
      logger.debug(s"R:   ${p(r1)}")
      logger.debug(s"UR': ${p(ur2)}")
      logger.debug(s"R':  ${p(r2)}")

      // TODO check qvars1, qvars2 has same length and same types

      val newPre = predicate_inf $ a $ extendQeq(us1,s1,us2,s2,qvarsL,qvarsR)
      // TODO: unitarity condition
      val unitarity = Isabelle.classical_subspace $ Isabelle.mk_conjs(Isabelle.unitary(ur1), Isabelle.unitary(ur2))
      val newPost = Isabelle.inf(b, unitarity, extendQeq(ur1,r1,ur2,r2,qvarsL,qvarsR))

      logger.debug(s"Pre: ${p(newPre)}")
      logger.debug(s"Post: ${p(newPost)}")

      val newQrhl = QRHLSubgoal(bodyL, bodyR, RichTerm(predicateT, newPre), RichTerm(predicateT, newPost), assumptions)

      // TODO check premises of rule

      // TODO create subgoal for fv-q-conditions

//      // Checking whether pre/postcondition contains local classical variables
//      val cvars12 = (cvarsL map { _.index1 }) ++ (cvarsR map { _.index2 })
//      val preConflict = pre.caVariables(env).classical.intersect(cvars12.toSet)
//      if (preConflict.nonEmpty)
//        throw UserException(s"Precondition must not contain the classical variable(s) ${cvars12 map { _.name } mkString ", "}")
//      val postConflict = post.caVariables(env).classical.intersect(cvars12.toSet)
//      if (postConflict.nonEmpty)
//        throw UserException(s"Postcondition must not contain the classical variable(s) ${cvars12 map { _.name } mkString ", "}")

      List(newQrhl)
  }

  def apply1(state: State, goal: Subgoal, left:Boolean): List[Subgoal] = goal match {
    case AmbientSubgoal(goal) =>
      throw UserException("Expected qRHL goal")
    case QRHLSubgoal(leftProg, rightProg, pre, post, assumptions) =>
      val lrWord = if (left) "left" else "right"
      val env = state.environment

      val (cvars, qvars, body) = (if (left) leftProg else rightProg) match {
        case Block(Local(cvars, qvars, body)) => (cvars, qvars, body)
        case _ => throw UserException(s"Expected $lrWord program to be of the form { local ...; ... }")
      }

      // Checking that pre/postcondition do not contain local classical variables
      val cvarsIdx = cvars map { _.index(left) }
      val preConflict = pre.caVariables(env).classical.intersect(cvarsIdx.toSet)
      if (preConflict.nonEmpty)
        throw UserException(s"Precondition must not contain the classical variable(s) ${cvarsIdx map { _.name } mkString ", "}")
      val postConflict = post.caVariables(env).classical.intersect(cvarsIdx.toSet)
      if (postConflict.nonEmpty)
        throw UserException(s"Postcondition must not contain the classical variable(s) ${cvarsIdx map { _.name } mkString ", "}")

      // Subgoals for checking that pre/postcondition do not contain local quantum variables
      val qvarsIdx = qvars map { _.index(left) }
      val qVarsIdxPairs = qvarsIdx.map { v => (v.variableName, v.valueTyp) }
      val colocalityPre = AmbientSubgoal(state.isabelle.isabelle.invoke(colocalityOp,
        (state.isabelle.contextId, pre.isabelleTerm, qVarsIdxPairs)))
      val colocalityPost = AmbientSubgoal(state.isabelle.isabelle.invoke(colocalityOp,
        (state.isabelle.contextId, post.isabelleTerm, qVarsIdxPairs)))

      // qRHL goal without the "local"
      val newQRHLGoal = if (left)
        QRHLSubgoal(body, rightProg, pre, post, assumptions)
      else
        QRHLSubgoal(leftProg, body, pre, post, assumptions)

      logger.debug(colocalityPre.toString)
      logger.debug(colocalityPost.toString)
      logger.debug(newQRHLGoal.toString)

      List(colocalityPre, colocalityPost, newQRHLGoal)
  }
}

object LocalTac {
  sealed trait Mode
  case object left extends Mode
  case object right extends Mode
  case object joint extends Mode

  private val logger = log4s.getLogger
}