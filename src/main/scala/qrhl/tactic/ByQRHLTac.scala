package qrhl.tactic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.{App, Const, Free, Term, Type}
import info.hupel.isabelle.{Operation, pure}
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.logic._

import qrhl.isabelle.RichTerm.term_tight_codec
import qrhl.isabelle.RichTerm.typ_tight_codec

case object ByQRHLTac extends Tactic {
  class Probability(left : Boolean, state : State) {
    def unapply(term: pure.Term): Option[(pure.Term,pure.Term,pure.Term)] = term match {
      case App(App(App(Const(Isabelle.probability.name,_),v),p),rho) =>
        val addIndexToExpressionOp = Operation.implicitly[(BigInt,Term,Boolean), RichTerm]("add_index_to_expression")

        val v2 = state.isabelle.isabelle.invoke(addIndexToExpressionOp, (state.isabelle.contextId,v,left))
        val v3 = RichTerm.decodeFromExpression(state.isabelle, v2.isabelleTerm).isabelleTerm
        Some(v3,p,rho)
      case _ => None
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
        val p1name = p1 match {
          case Free(n,_) => n
          case _ => throw UserException(s"Program in lhs must be the name of a program (not $p1)")
        }
        val p2name = p2 match {
          case Free(n,_) => n
          case _ => throw UserException(s"Program in rhs must be the name of a program (not $p2)")
        }
        if (rho1!=rho2)
          throw UserException("The initial state in lhs and rhs must be identical (syntactically same term, not just equal)")
//        val rho = rho1

        //        val v1name = Isabelle.dest_string(v1)
//        val v2name = Isabelle.dest_string(v2)

        val env = state.environment
//        val v1var = env.cVariables.getOrElse(v1name, throw UserException(s"$v1 is not the name of a classical variable")).index1
//        val v2var = env.cVariables.getOrElse(v2name, throw UserException(s"$v2 is not the name of a classical variable")).index2
        val p1prog = env.programs.getOrElse(p1name, throw UserException(s"$p1name is not the name of a program"))
        val p2prog = env.programs.getOrElse(p2name, throw UserException(s"$p2name is not the name of a program"))

        //        val v1bool = v1var.typ.isabelleTyp match {
//          case Type("HOL.bool",Nil) => v1var.isabelleTerm
//          case Type("QRHL_Core.bit",Nil) => bitToBool(v1var.isabelleTerm)
//          case _ => throw UserException(s"$v1name must have type bool or bit, not ${v1var.typ}")
//        }
//
//        val v2bool = v2var.typ.isabelleTyp match {
//          case Type("HOL.bool",Nil) => v2var.isabelleTerm
//          case Type("QRHL_Core.bit",Nil) => bitToBool(v2var.isabelleTerm)
//          case _ => throw UserException(s"$v2name must have type bool or bit, not ${v2var.typ}")
//        }

        val connective = rel match {
          case "Orderings.ord_class.less_eq" => Const("HOL.implies", connectiveT)
          case "HOL.eq" => Const("HOL.eq", connectiveT)
          case _ => throw UserException("There should be = or <= or >= between the lhs and the rhs")
        }

        val (cvars1,qvars1,_,_) = p1prog.variablesRecursive
        val (cvars2,qvars2,_,_) = p2prog.variablesRecursive
        val cvars = (cvars1 ++ cvars2).distinct
        val qvars = (qvars1 ++ qvars2).distinct

        val isa = state.isabelle
        val pre = isa.isabelle.invoke(byQRHLPreOp,
          (isa.contextId,
            cvars.map(v => (v.index1.name, v.index2.name, v.valueTyp)),
            qvars.map(v => (v.index1.name, v.index2.name, v.valueTyp))))

        val left = Block(Call(p1name))
        val right = Block(Call(p2name))
//        val pre = Expression(Isabelle.predicateT, preTerm)
        val post = RichTerm(Isabelle.predicateT, Isabelle.classical_subspace $ (connective $ v1 $ v2))

        List(QRHLSubgoal(left,right,pre,post,Nil))
      case _ =>
        throw UserException("""Expected subgoal of the form "Pr[b:p(rho)] = Pr[c:q(rho2)]" (or with <= or >=) where b,c are bool or bit program variables, and p,q are program names""")
    }
  }
}
