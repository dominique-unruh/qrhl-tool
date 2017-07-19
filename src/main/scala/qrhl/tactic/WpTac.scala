package qrhl.tactic

import info.hupel.isabelle.ml.Expr
import info.hupel.isabelle.pure.{Term, Typ=>ITyp}
import qrhl.{State, UserException}
import qrhl.logic._

case class WpTac(left:Boolean) extends WpStyleTac(left=left) {
  override def getWP(state: State, left: Boolean, statement: Statement, post: Expression): Expression = statement match {
    case Assign(v,e) =>
      val env = state.environment
      post.substitute(v.index(left=left),e.index(env, left=left))
    case Sample(x, e) =>
      val isabelle = post.isabelle
      val env = state.environment
      val e1 = e.index(env, left=left)
      val x1 = x.index(left=left)

      val ml = Expr.uncheckedLiteral[String => ITyp => Term => Term => Term]( // TODO: move to qrhl.ml
      """(fn v => fn T => fn e => fn B =>
        |    let val distrT = Type(@{type_name distr},[T])
        |        val _ = if fastype_of e = distrT then ()
        |                else raise(TYPE("variable and expression, type mismatch",[T,fastype_of e],[e]))
        |        val _ = if fastype_of B = @{typ assertion} then ()
        |                else raise(TYPE("assertion has wrong type",[fastype_of B],[B]))
        |        val setT = Type(@{type_name set},[T])
        |        val supp = Const(@{const_name supp}, distrT --> setT) $ e
        |        val absB = Term.absfree (v,T) B
        |        val B2 = @{const Inf(assertion)} $
        |                      (Const(@{const_name image}, (T --> @{typ assertion}) --> setT -->  @{typ "assertion set"})
        |                         $ absB $ supp)
        |        val total = @{const classical_subspace} $
        |             HOLogic.mk_eq (Const(@{const_name weight}, distrT --> @{typ real}) $ e, @{term "1::real"})
        |    in
        |      @{term "inf::assertion=>assertion=>assertion"} $ total $ B2
        |    end)
      """.stripMargin)
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
      val wp = post.isabelle.runExpr(wpExpr)
      Expression(post.isabelle,wp)
    case _ => throw UserException(s"""statement "$statement" unsupported by WpTac""")
  }
}
