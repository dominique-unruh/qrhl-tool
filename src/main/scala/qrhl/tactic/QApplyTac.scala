package qrhl.tactic

import info.hupel.isabelle.ml.Expr
import info.hupel.isabelle.pure.Term
import qrhl.State
import qrhl.logic.{Expression, QApply, QInit, Statement}
import info.hupel.isabelle.pure.Term
import qrhl.logic.{Expression, QInit, Statement}
import qrhl.{State, Tactic}

//@deprecated
//case class QApplyTac(left: Boolean) extends WpStyleTac(left=left) {
//  override def getWP(state: State, left: Boolean, statement: Statement, post: Expression): Expression = statement match {
//    case QApply(vs,e) =>
//      val env = state.environment
//      val e1 = e.index(env,left=left)
//      val vs2 = vs.map(_.index(left=left))
//
//      val wpExpr = QApplyTac.ml(post.isabelleTerm)(implicitly) (e1.isabelleTerm)(implicitly) (vs2.map(_.isabelleTerm))
//      val wp = post.isabelle.runExpr(wpExpr)
//      Expression(post.isabelle,wp)
//  }
//
//  override def toString: String = s"qapply(${if (left) "left" else "right"})"
//}
//
//object QApplyTac {
//  private val ml = Expr.uncheckedLiteral[Term => Term => List[Term] => Term]("QRHL.qapplyWp")
//}
