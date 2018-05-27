package qrhl.tactic
import info.hupel.isabelle.pure.{Term, Typ}
import info.hupel.isabelle.{Operation, pure}
import qrhl.isabelle.Isabelle
import qrhl.logic.{Expression, Sample, Statement}
import qrhl.{State, UserException}

case class RndTac(map:Option[Expression]=None) extends WpBothStyleTac {
  override def getWP(state: State, left: Statement, right: Statement, post: Expression): (Expression,Nil.type) = (left,right) match {
    case (Sample(x,e), Sample(y,f)) =>
//      val isabelle = post.isabelle
      val env = state.environment
      val e1 = e.index1(env)
      val x1 = x.index1
      val f2 = f.index2(env)
      val y2 = y.index2

      map match {
      case None =>
        if (x.valueTyp != y.valueTyp)
          throw UserException(s"The assigned variables $x and $y must have the same type (they have types ${x.valueTyp} and ${y.valueTyp})")

//        val lit = ml.Expr.uncheckedLiteral[String => pure.Term => String => pure.Term => pure.Typ => pure.Term => pure.Term]("QRHL.rndWp")
//        val wpExpr = (lit(x1.name)(implicitly)(e1.isabelleTerm)(implicitly)
//        (y2.name)(implicitly)(f2.isabelleTerm)(implicitly)
//        (x1.typ.isabelleTyp)(implicitly)(post.isabelleTerm))
//        val wp = state.isabelle.runExpr(wpExpr)
        val wp = state.isabelle.isabelle.invoke(rndWpOp,
            ((x1.name,e1.isabelleTerm, y2.name), (f2.isabelleTerm, x1.valueTyp, post.isabelleTerm)))
        (Expression(Isabelle.predicateT, wp), Nil)
      case Some(distr) =>
//        val lit = ml.Expr.uncheckedLiteral[String => pure.Typ => pure.Term => String => pure.Typ => pure.Term =>
//                                                     pure.Term => pure.Term => pure.Term]("QRHL.rndWp2")
//        val wpExpr = (lit(x1.name)(implicitly) (x1.typ.isabelleTyp)(implicitly) (e1.isabelleTerm)(implicitly)
//                         (y2.name)(implicitly) (y2.typ.isabelleTyp)(implicitly) (f2.isabelleTerm)(implicitly)
//                         (distr.isabelleTerm)(implicitly) (post.isabelleTerm))
//        val wp = state.isabelle.runExpr(wpExpr)

        val wp = state.isabelle.isabelle.invoke(rndWp2Op,
           ((x1.name,x1.valueTyp,e1.isabelleTerm),
            (y2.name,y2.valueTyp,f2.isabelleTerm),
            (distr.isabelleTerm,post.isabelleTerm)))

        (Expression(Isabelle.predicateT, wp), Nil)
    }
    case _ =>
      throw UserException("Expected sampling statement as last statement on both sides")
  }

  val rndWpOp: Operation[((String, Term, String), (Term, Typ, Term)), Term] =
    Operation.implicitly[((String, pure.Term, String), (pure.Term, pure.Typ, pure.Term)), pure.Term]("rndWp")
  val rndWp2Op: Operation[((String, Typ, Term), (String, Typ, Term), (Term, Term)), Term] =
    Operation.implicitly[((String, pure.Typ, pure.Term), (String, pure.Typ, pure.Term), (pure.Term, pure.Term)), pure.Term]("rndWp2")
}