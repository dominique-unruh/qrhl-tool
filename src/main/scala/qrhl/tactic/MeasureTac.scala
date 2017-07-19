package qrhl.tactic

import info.hupel.isabelle.ml.Expr
import info.hupel.isabelle.pure.Term
import qrhl.logic.{Expression, Measurement, QInit, Statement}
import qrhl.{State, Tactic, UserException}

//@deprecated
//case class MeasureTac(left: Boolean) extends WpStyleTac(left=left) {
//  override def getWP(state: State, left: Boolean, statement: Statement, post: Expression): Expression = statement match {
//    case Measurement(x,q,e) =>
//      val env = state.environment
//      val e1 = e.index(env,left=left)
//      val q1 = q.map(_.index(left=left))
//      val x1 = x.index(left=left)
//
//      val wpExpr = (MeasureTac.ml(post.isabelleTerm)(implicitly)
//                    (x1.isabelleTerm)(implicitly)
//                    (e1.isabelleTerm)(implicitly)
//                    (q1.map(_.isabelleTerm)))
//      val wp = post.isabelle.runExpr(wpExpr)
//      Expression(post.isabelle,wp)
//    case _ => throw UserException(s"Expected a measurement as last statement on ${if (left) "left" else "right"} side")
//  }
//}
//
//object MeasureTac {
//  private val ml = Expr.uncheckedLiteral[Term => Term => Term => List[Term] => Term]("QRHL.measureWp")
//}
