package qrhl.tactic

import info.hupel.isabelle.ml.Expr
import info.hupel.isabelle.pure.{Term, Typ=>ITyp}
import qrhl.{State, UserException}
import qrhl.logic._

case class WpTac(override val left:Boolean) extends WpStyleTac(left) {
  override def toString: String = s"wp(${if (left) "left" else "right"})"

  override def getWP(state: State, statement: Statement, post: Expression): Expression = statement match {
    case Assign(v,e) =>
      val env = state.environment
      post.substitute(v.index(left=left),e.index(env, left=left))

    case Sample(x, e) =>
      val isabelle = post.isabelle
      val env = state.environment
      val e1 = e.index(env, left=left)
      val x1 = x.index(left=left)

      val ml = Expr.uncheckedLiteral[String => ITyp => Term => Term => Term]("QRHL.sampleWp")
      val wpExpr = ml(x1.name)(implicitly) (x1.typ.isabelleTyp)(implicitly) (e1.isabelleTerm)(implicitly) (post.isabelleTerm)
      val wp = post.isabelle.runExpr(wpExpr)
      Expression(post.isabelle,wp)

    case QApply(vs,e) =>
      val env = state.environment
      val e1 = e.index(env,left=left)
      val vs2 = vs.map(_.index(left=left))

      val ml = Expr.uncheckedLiteral[Term => Term => List[Term] => Term]("QRHL.qapplyWp")
      val wpExpr = ml(post.isabelleTerm)(implicitly) (e1.isabelleTerm)(implicitly) (vs2.map(_.isabelleTerm))
      val wp = post.isabelle.runExpr(wpExpr)
      Expression(post.isabelle,wp)

    case Measurement(x,q,e) =>
      val env = state.environment
      val e1 = e.index(env,left=left)
      val q1 = q.map(_.index(left=left))
      val x1 = x.index(left=left)

      val ml = Expr.uncheckedLiteral[Term => Term => Term => List[Term] => Term]("QRHL.measureWp")
      val wpExpr = (ml(post.isabelleTerm)(implicitly)
                      (x1.isabelleTerm)(implicitly)
                      (e1.isabelleTerm)(implicitly)
                      (q1.map(_.isabelleTerm)))
      val wp = post.isabelle.runExpr(wpExpr)
      Expression(post.isabelle,wp)

    case QInit(vs,e) =>
      val env = state.environment
      val e1 = e.index(env,left=left)
      val vs2 = vs.map(_.index(left=left))

      val ml = Expr.uncheckedLiteral[Term => Term => List[Term] => Term]("QRHL.qinitWp")
      val wpExpr = ml(post.isabelleTerm)(implicitly) (e1.isabelleTerm)(implicitly) (vs2.map(_.isabelleTerm))
      val wp = state.isabelle.get.runExpr(wpExpr)
      Expression(state.isabelle.get,wp)

    case IfThenElse(e,thenBranch,elseBranch) =>
      val thenWp = getWP(state, thenBranch.statements, post)
      val elseWp = getWP(state, elseBranch.statements, post)
      val e1 = e.index(state.environment, left=left)

      val ml = Expr.uncheckedLiteral[Term => Term => Term => Term]("QRHL.ifWp")
      val wpExpr = ml(e1.isabelleTerm)(implicitly)  (thenWp.isabelleTerm)(implicitly)  (elseWp.isabelleTerm)
      val wp = state.isabelle.get.runExpr(wpExpr)
      Expression(state.isabelle.get,wp)

    case _ => throw UserException(s"""statement "$statement" unsupported by WpTac""")
  }

  def getWP(state: State, statements: Seq[Statement], post: Expression): Expression = {
    statements.foldRight(post) { (statement,wp) => getWP(state,statement,post) }
  }
}
