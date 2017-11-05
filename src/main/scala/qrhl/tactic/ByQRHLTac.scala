package qrhl.tactic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.{App, Const, Free, Term, Type}
import info.hupel.isabelle.pure
import info.hupel.isabelle.ml
import qrhl._
import qrhl.isabelle.Isabelle
import qrhl.logic._

case object ByQRHLTac extends Tactic {
  object Probability {
    def unapply(term: pure.Term): Option[(pure.Term,pure.Term,pure.Term)] = term match {
      case App(App(App(Const("QRHL.probability",_),v),p),rho) => Some(v,p,rho)
      case _ => None
    }

  }

  private val connectiveT = Type("HOL.bool",Nil) -->: Type("HOL.bool",Nil) -->: Type("HOL.bool",Nil)
  private def bitToBool(b:Term) = Isabelle.mk_eq(Type("QRHL.bit",Nil), b, Const("Groups.one_class.one", Type("QRHL.bit",Nil)))

//  def mkCEquality(cvars: List[CVariable]) : Term =
//    Isabelle.mk_conjs((for (c<-cvars)
//      yield Isabelle.mk_eq(c.typ.isabelleTyp, c.index1.isabelleTerm, c.index2.isabelleTerm)) : _*)
//
//  def mkQEquality(qvars: List[QVariable]) : Term = Const("HOL.undefined", Isabelle.predicateT)

  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case AmbientSubgoal(Expression(App(App(Const(rel,_),Probability(v1,p1,rho1)),Probability(v2,p2,rho2)))) =>
      val p1name = p1 match {
        case Free(n,_) => n
        case _ => throw UserException(s"Program in lhs must be the same of a program (not $p1)")
      }
      val p2name = p2 match {
        case Free(n,_) => n
        case _ => throw UserException(s"Program in rhs must be the same of a program (not $p2)")
      }
      if (rho1!=rho2)
        throw UserException("The initial state in lhs and rhs must be identical (syntactically same term, not just equal)")
      val rho = rho1

      val v1name = Isabelle.dest_string(v1)
      val v2name = Isabelle.dest_string(v2)

      val env = state.environment
      val v1var = env.cVariables.getOrElse(v1name, throw UserException(s"$v1 is not the name of a classical variable")).index1
      val v2var = env.cVariables.getOrElse(v2name, throw UserException(s"$v2 is not the name of a classical variable")).index2
      val p1prog = env.programs.getOrElse(p1name, throw UserException(s"$p1name is not the name of a program"))
      val p2prog = env.programs.getOrElse(p2name, throw UserException(s"$p2name is not the name of a program"))

      val v1bool = v1var.typ.isabelleTyp match {
        case Type("HOL.bool",Nil) => v1var.isabelleTerm
        case Type("QRHL.bit",Nil) => bitToBool(v1var.isabelleTerm)
        case _ => throw UserException(s"$v1name must have type bool or bit, not ${v1var.typ}")
      }

      val v2bool = v2var.typ.isabelleTyp match {
        case Type("HOL.bool",Nil) => v2var.isabelleTerm
        case Type("QRHL.bit",Nil) => bitToBool(v2var.isabelleTerm)
        case _ => throw UserException(s"$v2name must have type bool or bit, not ${v2var.typ}")
      }

      val connective = rel match {
        case "Orderings.ord_class.less_eq" => Const("HOL.implies", connectiveT)
        case "HOL.eq" => Const("HOL.eq", connectiveT)
        case _ => throw UserException("There should be = or <= or >= between the lhs and the rhs")
      }

      val (cvars1,qvars1) = p1prog.variablesRecursive
      val (cvars2,qvars2) = p2prog.variablesRecursive
      val cvars = (cvars1 ++ cvars2).distinct
      val qvars = (qvars1 ++ qvars2).distinct

      val lit = ml.Expr.uncheckedLiteral[List[(String,String,pure.Typ)] => List[(String,String,pure.Typ)] => Term]("QRHL.byQRHLPre")
      val mlExpr = (lit(cvars.map(v => (v.index1.name, v.index2.name, v.typ.isabelleTyp)))(implicitly)
                       (qvars.map(v => (v.index1.name, v.index2.name, v.typ.isabelleTyp)))(implicitly))

      val isa = state.isabelle.get
      val left = Block(Call(p1name))
      val right = Block(Call(p2name))
      val pre = Expression(isa, state.predicateT, isa.runExpr(mlExpr))
      val post = Expression(isa, state.predicateT, Isabelle.classical_subspace $ (connective $ v1bool $ v2bool))

      List(QRHLSubgoal(left,right,pre,post,Nil))
    case _ =>
      throw UserException("""Expected subgoal of the form "Pr[b:p(rho)] = Pr[c:q(rho2)]" (or with <= or >=) where b,c are bool or bit program variables, and p,q are program names""")
  }
}
