package qrhl.tactic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.{App, Const, Free, Term, Type}
import info.hupel.isabelle.{Operation, pure}
import org.log4s
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.logic._
import qrhl.isabelle.RichTerm.term_tight_codec
import qrhl.isabelle.RichTerm.typ_tight_codec

case object ByQRHLTac extends Tactic {
  private val logger = log4s.getLogger

  class Probability(left : Boolean, state : State) {
    def unapply(term: pure.Term): Option[(pure.Term,Statement,pure.Term)] = term match {
      case App(App(App(Const(Isabelle.probability.name,_),v),p),rho) =>
        val addIndexToExpressionOp = Operation.implicitly[(BigInt,Term,Boolean), RichTerm]("add_index_to_expression")

        val v2 = state.isabelle.isabelle.invoke(addIndexToExpressionOp, (state.isabelle.contextId,v,left))
        val v3 = RichTerm.decodeFromExpression(state.isabelle, v2.isabelleTerm).isabelleTerm

        val pname = p match {
          case Free(n,_) => n
          case _ => throw UserException(s"Program in lhs must be the name of a program (not $p)")
        }
        val prog = state.environment.programs.getOrElse(pname, throw UserException(s"$pname is not the name of a program"))
        if (prog.numOracles != 0)
          throw UserException(s"Program $p expects arguments, that is not supported in a Pr[...] statement")

        Some((v3,Call(prog.name),rho))
      case Const(Isabelle.one_name,_) =>
        Some((Isabelle.True_const, Block(), null))
      case _ =>
        ByQRHLTac.logger.debug(s"Term: $term")
        None
    }
  }

  private val connectiveT = HOLogic.boolT -->: HOLogic.boolT -->: HOLogic.boolT
  private def bitToBool(b:Term) =
    Isabelle.mk_eq(Isabelle.bitT, b, Const("Groups.one_class.one", Isabelle.bitT))

  val byQRHLPreOp: Operation[(BigInt, List[(String, String, pure.Typ)], List[(String, String, pure.Typ)]), RichTerm]
    = Operation.implicitly[(BigInt, List[(String,String,pure.Typ)], List[(String,String,pure.Typ)]), RichTerm]("byQRHLPre") // TODO: move

  override def apply(state: State, goal: Subgoal): List[Subgoal] = {
    val ProbLeft = new Probability(true, state)
    val ProbRight = new Probability(false, state)

    goal match {
      case AmbientSubgoal(RichTerm(App(App(Const(rel,_),ProbLeft(v1,p1,rho1)),ProbRight(v2,p2,rho2)))) =>
        if (rho1!=null && rho2!=null && rho1!=rho2)
          throw UserException("The initial state in lhs and rhs must be identical (syntactically same term, not just equal)")

        val env = state.environment

        val connective = rel match {
          case "Orderings.ord_class.less_eq" => Const("HOL.implies", connectiveT)
          case "HOL.eq" => Const("HOL.eq", connectiveT)
          case _ => throw UserException("There should be = or <= or >= between the lhs and the rhs")
        }

        val vars1 = p1.variableUse(state.environment)
        val vars2 = p2.variableUse(state.environment)
        val cvars = vars1.classical ++ vars2.classical
        val qvars = (vars1.quantum -- vars1.overwrittenQuantum) ++ (vars2.quantum -- vars2.overwrittenQuantum)

        val isa = state.isabelle
        val pre = isa.isabelle.invoke(byQRHLPreOp,
          (isa.contextId,
            cvars.toList.map(v => (v.index1.name, v.index2.name, v.valueTyp)),
            qvars.toList.map(v => (v.index1.name, v.index2.name, v.valueTyp))))

        val left = p1.toBlock
        val right = p2.toBlock
        val post = RichTerm(Isabelle.predicateT, Isabelle.classical_subspace $ (connective $ v1 $ v2))

        List(QRHLSubgoal(left,right,pre,post,Nil))
      case _ =>
        throw UserException("""Expected subgoal of the form "Pr[e:p(rho)] = Pr[f:q(rho2)]" (or with <= or >=) where p,q are program names""")
    }
  }
}
