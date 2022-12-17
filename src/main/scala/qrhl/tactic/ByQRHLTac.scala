package qrhl.tactic

import java.io.PrintWriter
import org.log4s
import qrhl._
import qrhl.isabellex.{IsabelleConsts, IsabelleX, RichTerm}
import qrhl.logic._
import IsabelleX.{globalIsabelle => GIsabelle}
import GIsabelle.{DenotationalEquivalence, Ops}
import de.unruh.isabelle.pure.{Abs, App, Bound, Const, Context, Free, Term}
import hashedcomputation.Implicits.listHashable
import hashedcomputation.{Hash, HashTag, Hashable}
import qrhl.isabellex.IsabelleX.globalIsabelle.clT
import qrhl.tactic.ByQRHLTac.logger

import scala.collection.immutable.ListSet

// Implicits
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._
import scala.concurrent.ExecutionContext.Implicits._
import qrhl.isabellex.IsabelleX.globalIsabelle.isabelleControl

case class ByQRHLTac(qvariables: List[QVariableNI]) extends Tactic {
  override def hash: Hash[ByQRHLTac.this.type] =
    HashTag()(Hashable.hash(qvariables))

  /** Pattern-matcher that matches Pr[e : prog (rho)]
   * and returns e
   *             Call(prog) (prog must be a program)
   *             rho
   *
   * e inside Pr[] must be in longform.
   *
   * Special case: if the term to be matched is "1", return (True, empty program, null)
   */
  class Probability(left : Boolean, state : State) {
    def unapply(term: Term): Option[(ExpressionNonindexed,Statement,Term)] = term match {
      case App(App(App(Const(GIsabelle.probability.name,_),e),p),rho) =>
        val e2 = ExpressionNonindexed.fromTerm(e)
//        val e2 = Ops.addIndexToExpressionOp(state.isabelle.context, e, left).retrieveNow
//        val e3 = RichTerm.decodeFromExpression(state.isabelle, e2).isabelleTerm

        val pname = p match {
          case Free(n,_) => n
          case _ => throw UserException(s"Program in lhs must be the name of a program (not $p)")
        }
        val prog = state.environment.programs.getOrElse(pname, throw UserException(s"$pname is not the name of a program"))
        if (prog.numOracles != 0)
          throw UserException(s"Program $p expects arguments, that is not supported in a Pr[...] statement")

        Some((e2,Call(prog.name),rho))
      case Const(IsabelleConsts.one,_) =>
        Some((ExpressionNonindexed.constant(GIsabelle.True_const), Block.empty, null))
      case _ =>
        ByQRHLTac.logger.debug(s"Term: $term")
        None
    }
  }

//  private val connectiveT = HOLogic.boolT -->: HOLogic.boolT -->: HOLogic.boolT
  private def bitToBool(b:Term) =
    GIsabelle.mk_eq(b, Const("Groups.one_class.one", GIsabelle.bitT))

  /**
   * Implements the rule
   *
   * {q...r} ⊇ quantum( fv(p)-overwr(p), fv(q)-overwr(q) )
   * {Cla[x1=x2 /\ ... /\ z1=z2] ⊓ [q1...r1] ==q [q2...r2]} p ~ q { e <->/--> f }
   * ----------------------------------------------------------------------------
   * Pr[e:p(rho)] =/<= Pr[f:q(rho)]
   *
   * Here {x...z} := classical( fv(p), fv(q), fv(e), fv(f) )
   * And {q...r} := user chosen quantum variables, or minimal set satisfying the rule
   *
   * Rule is proven in local variables paper, QrhlElimEqNew.
   *
   * |===== OR =====|
   *
   * {q...r} ⊇ quantum( fv(p), fv(q) )
   * {Cla[x1=x2 /\ ... /\ z1=z2] ⊓ [q1...r1] ==q [q2...r2]} p ~ q { same as precondition }
   * -------------------------------------------------------------------------------------
   * p denotationally-equal q
   *
   * Here {x...z} := classical( fv(p), fv(q) )
   * And {q...r} := user chosen quantum variables, or minimal set satisfying the rule
   *
   * TODO: Reference proof
   */
  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = {
    val ProbLeft = new Probability(true, state)
    val ProbRight = new Probability(false, state)

    goal match {
        // Subgoal: Pr[e1:p1(rho)] R Pr[e2:p2(rho)]
        // lhs or rhs can also be just "1"
        // Variables `e1`, `e2` contain *indexed* expressions!   // TODO why???
      case AmbientSubgoal(RichTerm(App(App(Const(rel,_),ProbLeft(e1,p1,rho1)),ProbRight(e2,p2,rho2)))) =>
        // e1,e2 are in shortform

        if (rho1!=null && rho2!=null && rho1!=rho2)
          throw UserException("The initial state in lhs and rhs must be identical (syntactically same term, not just equal)")

        logger.debug((rel,e1,p1,e2,p2).toString)

        val env = state.environment
        val ctxt = state.isabelle.context

        // R must be one of <= or =
        // connective := --> or = then.
        val connective = rel match {
          case IsabelleConsts.less_eq => GIsabelle.implies
          case IsabelleConsts.eq => GIsabelle.iff
          case _ => throw UserException("There should be = or <= or >= between the lhs and the rhs")
        }

        def stripIndices(vs: Iterable[CVariable]) =
          vs.collect { case Variable.IndexedC(v, _) => v }

        val vars1 = p1.variableUse(ctxt, env)
        val vars2 = p2.variableUse(ctxt, env)
        val vars1expr = e1.variables(ctxt, env).classical
        val vars2expr = e2.variables(ctxt, env).classical

        // fv(p1), fv(p2), fv(e1), fv(e2) (not indexed, only classical)
        val cvars = vars1.classical ++ vars2.classical ++ vars1expr ++ vars2expr
        // fv(p1)-overwr(p1)  union   fv(p2)-overwr(p2)   (only quantum)
        // The minimum set that have to be included in the quantum equality
        val requiredQvars = (vars1.quantum -- vars1.overwrittenQuantum) ++ (vars2.quantum -- vars2.overwrittenQuantum)

        // variables to include in the quantum equality
        val qvars =
          if (qvariables.isEmpty)
            requiredQvars
          else {
            val qvariables2 = ListSet(qvariables:_*)
            if (!requiredQvars.subsetOf(qvariables2))
              throw UserException(s"You must specify at least the following qvars: $requiredQvars")
            qvariables2
          }

        // Cla[x1==x2 /\ ... /\ z1==z2] ⊓ [q1...r1] ==q [q2...r2]
        // if cvars =: x...z and qvars =: q...r
        val pre = Ops.byQRHLPreOp(
            cvars.toList.map(v => (v.name, v.valueTyp)),
            qvars.toList.map(v => (v.name, v.valueTyp))).retrieveNow

        val left = p1.toBlock
        val right = p2.toBlock

        // Cla[e1 -->/= e2]
        val post = RichTerm(GIsabelle.predExpressionT,
          Abs("mem", GIsabelle.cl2T,
            GIsabelle.classical_subspace(connective $
              (e1.term.isabelleTerm $ (GIsabelle.fst(clT, clT) $ Bound(0))) $
              (e2.term.isabelleTerm $ (GIsabelle.snd(clT, clT) $ Bound(0))))))

        List(QRHLSubgoal(left,right,ExpressionIndexed.fromTerm(pre),ExpressionIndexed.fromTerm(post),Nil))
      // Subgoal: p1 denotationally-equivalent p2
      case DenotationalEqSubgoal(p1, p2, assms) =>
        val env = state.environment
        implicit val ctxt: Context = state.isabelle.context

        val vars1 = p1.variableUse(ctxt, env)
        val vars2 = p2.variableUse(ctxt, env)

        /** fv(p1), fv(p2) (not indexed, only classical) */
        val cvars = vars1.classical ++ vars2.classical
        /** fv(p1)  union   fv(p2)   (only quantum)
         * The minimum set that have to be included in the quantum equality */
        val requiredQvars = vars1.quantum ++ vars2.quantum

        /** variables to include in the quantum equality */
        val qvars =
          if (qvariables.isEmpty)
            requiredQvars
          else {
            val qvariables2 = ListSet(qvariables: _*)
            if (!requiredQvars.subsetOf(qvariables2))
              throw UserException(s"You must specify at least the following qvars: $requiredQvars")
            qvariables2
          }

        /** Precondition.
         * Cla[x1==x2 /\ ... /\ z1==z2] ⊓ [q1...r1] ==q [q2...r2]
         * if cvars =: x...z and qvars =: q...r
         *
         * In shortform.
         */
        val pre = Ops.byQRHLPreOp(
          cvars.toList.map(v => (v.name, v.valueTyp)),
          qvars.toList.map(v => (v.name, v.valueTyp))).retrieveNow

        val left = p1.toBlock
        val right = p2.toBlock

        /** postcondition */
        val post = pre

        List(QRHLSubgoal(left, right, ExpressionIndexed.fromTerm(pre), ExpressionIndexed.fromTerm(post), assms))
      case _ =>
        throw UserException(
          """Expected subgoal of the form "Pr[e:p(rho)] = Pr[f:q(rho2)]" (or with <= or >=) where p,q are program names\n
            |Or a denotational equivalence.""".stripMargin)
    }
  }
}

object ByQRHLTac {
  private val logger = log4s.getLogger


}