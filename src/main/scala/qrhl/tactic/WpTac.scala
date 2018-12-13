package qrhl.tactic

import info.hupel.isabelle.Operation
import info.hupel.isabelle.pure.{Term, Typ => ITyp}
import qrhl.isabelle.Isabelle
import qrhl.logic._
import qrhl.{QRHLSubgoal, State, Subgoal, UserException}

import Expression.typ_tight_codec
import Expression.term_tight_codec

case class WpTac(left:Boolean)
  extends IsabelleTac(WpTac.wpTacOp, { context => left }) {
  override def toString: String = s"wp(${if (left) "left" else "right"})"

  override def check(state: State, goal: Subgoal, newGoals: List[Subgoal]): Unit = {
    assert(newGoals.length==1, newGoals.length)
    assert(newGoals.head.isInstanceOf[QRHLSubgoal], newGoals.head)
  }
}

/*case class WpTacOld(override val left:Boolean) extends WpStyleTac(left) {
  override def toString: String = s"wp(${if (left) "left" else "right"})"

  override def getWP(state: State, statement: Statement, post: Expression): Expression = statement match {
    case Assign(v,e) =>
      val env = state.environment
      post.substitute(v.index(left=left),e.index(env, left=left))

    case Sample(x, e) =>
      val isabelle = state.isabelle
      val env = state.environment
      val e1 = e.index(env, left=left)
      val x1 = x.index(left=left)

//      val ml = Expr.uncheckedLiteral[String => ITyp => Term => Term => Term]("QRHL.sampleWp")
//      val wpExpr = ml(x1.name)(implicitly) (x1.typ.isabelleTyp)(implicitly) (e1.isabelleTerm)(implicitly) (post.isabelleTerm)
//      val wp = post.isabelle.runExpr(wpExpr)

      val wp = isabelle.isabelle.invoke(WpTac.sampleWpOp,
        ((x1.name,x1.valueTyp),(e1.isabelleTerm,post.isabelleTerm)))

      wp

    case QApply(vs,e) =>
      val env = state.environment
      val e1 = e.index(env,left=left)
      val vs2 = vs.map(_.index(left=left))

//      val ml = Expr.uncheckedLiteral[Term => Term => List[Term] => Term]("QRHL.qapplyWp")
//      val wpExpr = ml(post.isabelleTerm)(implicitly) (e1.isabelleTerm)(implicitly) (vs2.map(_.isabelleTerm))
//      val wp = post.isabelle.runExpr(wpExpr)

      val wp = state.isabelle.isabelle.invoke(WpTac.qapplyWpOp,
        (post.isabelleTerm, e1.isabelleTerm, vs2.map(_.variableTerm)))

      wp

    case Measurement(x,q,e) =>
      val env = state.environment
      val e1 = e.index(env,left=left)
      val q1 = q.map(_.index(left=left))
      val x1 = x.index(left=left)

//      val ml = Expr.uncheckedLiteral[Term => Term => Term => List[Term] => Term]("QRHL.measureWp")
//      val wpExpr = (ml(post.isabelleTerm)(implicitly)
//                      (x1.isabelleTerm)(implicitly)
//                      (e1.isabelleTerm)(implicitly)
//                      (q1.map(_.isabelleTerm)))
//      val wp = post.isabelle.runExpr(wpExpr)

      val wp = state.isabelle.isabelle.invoke(WpTac.measureWpOp,
        ((post.isabelleTerm, x1.valueTerm), (e1.isabelleTerm, q1.map(_.variableTerm))))

      wp

    case QInit(vs,e) =>
      val env = state.environment
      val e1 = e.index(env,left=left)
      val vs2 = vs.map(_.index(left=left))

//      val ml = Expr.uncheckedLiteral[Term => Term => List[Term] => Term]("QRHL.qinitWp")
//      val wpExpr = ml(post.isabelleTerm)(implicitly) (e1.isabelleTerm)(implicitly) (vs2.map(_.isabelleTerm))
//      val wp = state.isabelle.runExpr(wpExpr)

      val wp = state.isabelle.isabelle.invoke(WpTac.qinitWpOp,
        (post.isabelleTerm, e1.isabelleTerm, vs2.map(_.variableTerm)))

      wp

    case IfThenElse(e,thenBranch,elseBranch) =>
      val thenWp = getWP(state, thenBranch.statements, post)
      val elseWp = getWP(state, elseBranch.statements, post)
      val e1 = e.index(state.environment, left=left)

//      val ml = Expr.uncheckedLiteral[Term => Term => Term => Term]("QRHL.ifWp")
//      val wpExpr = ml(e1.isabelleTerm)(implicitly)  (thenWp.isabelleTerm)(implicitly)  (elseWp.isabelleTerm)
//      val wp = state.isabelle.runExpr(wpExpr)

      val wp = state.isabelle.isabelle.invoke(WpTac.ifWpOp,
        (e1.isabelleTerm, thenWp.isabelleTerm, elseWp.isabelleTerm))

      wp

    case _ => throw UserException(s"""statement "$statement" unsupported by WpTac""")
  }

  def getWP(state: State, statements: Seq[Statement], post: Expression): Expression = {
    statements.foldRight(post) { (statement,wp) => getWP(state,statement,wp) }
  }
}*/

object WpTac {
  val wpTacOp: Operation[(Boolean, Term, BigInt), Option[(List[Expression],BigInt)]] =
    Operation.implicitly[(Boolean,Term,BigInt), Option[(List[Expression],BigInt)]]("wp_tac")

/*  val sampleWpOp: Operation[((String, ITyp), (Term, Term)), Expression] =
    Operation.implicitly[((String,ITyp), (Term, Term)), Term]("sampleWp")
  val qapplyWpOp: Operation[(Term, Term, List[Term]), Expression] =
    Operation.implicitly[(Term,Term,List[Term]), Term]("qapplyWp")
  val measureWpOp: Operation[((Term, Term), (Term, List[Term])), Expression] =
    Operation.implicitly[((Term, Term), (Term,List[Term])), Term]("measureWp")
  val qinitWpOp: Operation[(Term, Term, List[Term]), Expression] =
    Operation.implicitly[(Term,Term,List[Term]), Term]("qinitWp")
  val ifWpOp: Operation[(Term, Term, Term), Expression] =
    Operation.implicitly[(Term,Term,Term), Term]("ifWp")*/
}