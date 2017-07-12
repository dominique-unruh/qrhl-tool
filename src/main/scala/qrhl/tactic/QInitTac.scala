package qrhl.tactic

import info.hupel.isabelle.ml.Expr
import info.hupel.isabelle.pure.Term
import qrhl.logic.{Expression, QInit, Statement}
import qrhl.{State, Tactic}


case class QInitTac(left: Boolean) extends WpStyleTac(left=left) {
  override def getWP(state: State, left: Boolean, statement: Statement, post: Expression): Expression = statement match {
    case QInit(vs,e) =>
      val env = state.environment
      val e1 = e.index(env,left=left)
      val vs2 = vs.map(_.index(left=left))

      val wpExpr = QInitTac.ml(post.isabelleTerm)(implicitly) (e1.isabelleTerm)(implicitly) (vs2.map(_.isabelleTerm))
      val wp = post.isabelle.runExpr(wpExpr)
      Expression(post.isabelle,wp)
  }
}

object QInitTac {
  private val ml = Expr.uncheckedLiteral[Term => Term => List[Term] => Term]("QRHL.qinitWp")
}