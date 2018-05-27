package qrhl.tactic

import info.hupel.isabelle.hol.HOLogic
import info.hupel.isabelle.pure.Term
import info.hupel.isabelle.{Operation, ml, pure}
import qrhl.isabelle.Isabelle
import qrhl.logic.{Call, Expression, Statement}
import qrhl.{State, Tactic, UserException}

@deprecated("Superseeded by EqualTac","now")
case object CallTac extends WpBothStyleTac() {
  override def getWP(state: State, left: Statement, right: Statement, post: Expression): (Expression, List[Expression]) = (left,right) match {
    case (Call(prog), Call(prog2)) =>
      if (prog!=prog2) throw UserException(s"Both program names need to be the same ($prog≠$prog2)")
      val decl = state.environment.programs.getOrElse(prog, throw new Exception("should not happen"))
      val (cvars,qvars,_,_) = decl.variablesRecursive
      val cvarsIdx1 = cvars.map(_.index1)
      val cvarsIdx2 = cvars.map(_.index2)
      val qvarsIdx1 = qvars.map(_.index1)
      val qvarsIdx2 = qvars.map(_.index2)
      val forbidden = cvarsIdx1.map(_.name).toSet ++ cvarsIdx2.map(_.name) ++ qvarsIdx1.map(_.name) ++ qvarsIdx2.map(_.name)
//      for (v <- post.variables)
//        if (forbidden.contains(v))
//          throw UserException(s"Postcondition must not contain variable $v (used by program $prog)")

//      val lit = ml.Expr.uncheckedLiteral[List[pure.Term] => List[pure.Term] => List[pure.Term] => List[pure.Term]
//                          => pure.Term => (pure.Term,pure.Term)]("QRHL.callWp")
//      val mlExpr = (lit(cvarsIdx1.map(_.isabelleTerm))(implicitly) (cvarsIdx2.map(_.isabelleTerm))(implicitly)
//                       (qvarsIdx1.map(_.isabelleTerm))(implicitly) (qvarsIdx2.map(_.isabelleTerm))(implicitly)
//                       (post.isabelleTerm))
//      val (wp,colocality) = post.isabelle.runExpr(mlExpr)
      val (wp, colocality) = state.isabelle.get.isabelle.invoke(callWpOp,
           ((cvarsIdx1.map(_.valueTerm), cvarsIdx2.map(_.valueTerm),
            qvarsIdx1.map(_.variableTerm)), (qvarsIdx2.map(_.variableTerm),
            post.isabelleTerm)))


//      for (v <- varsInPost)
//        if (forbidden.contains(v)) {
////          val claStr = state.isabelle.get.prettyExpression(claTerm)
//          val quaStr = state.isabelle.get.prettyExpression(quaTerm)
//          throw UserException(s"Postcondition must not contain variable $v (used by program $prog), " +
//            s"except within the term $quaStr")
//        }

      val wp2 = Expression(Isabelle.predicateT, wp)
      val colocality2 = Expression(Isabelle.boolT, colocality)
      (wp2,List(colocality2))
    case _ => throw UserException("Expected a call statement as last statement on both sides")
  }

  val callWpOp: Operation[((List[Term], List[Term], List[Term]), (List[Term], Term)), (Term, Term)] =
    Operation.implicitly[((List[pure.Term], List[pure.Term], List[pure.Term]), (List[pure.Term], pure.Term)), (pure.Term, pure.Term)]("callWp")
}
