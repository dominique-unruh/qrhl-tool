package qrhl.tactic

import info.hupel.isabelle.pure.Term
import info.hupel.isabelle.{Operation, pure}
import qrhl.logic.{Expression, Statement}
import qrhl.{State, UserException}

case object EqualTac extends WpBothStyleTac() {
  override def getWP(state: State, left: Statement, right: Statement, post: Expression): (Expression, List[Expression]) = {
    if (left!=right) throw UserException(s"The last statement on both sides needs to be the same")
    val (cvars,qvars,_,_) = left.cqapVariables(state.environment,recurse = true)
    val cvarsIdx1 = cvars.map(_.index1)
    val cvarsIdx2 = cvars.map(_.index2)
    val qvarsIdx1 = qvars.map(_.index1)
    val qvarsIdx2 = qvars.map(_.index2)
    val forbidden = cvarsIdx1.map(_.name).toSet ++ cvarsIdx2.map(_.name) ++ qvarsIdx1.map(_.name) ++ qvarsIdx2.map(_.name)

    val (wp, colocality) = state.isabelle.get.isabelle.invoke(callWpOp,
      ((cvarsIdx1.map(_.valueTerm), cvarsIdx2.map(_.valueTerm),
        qvarsIdx1.map(_.variableTerm)), (qvarsIdx2.map(_.variableTerm),
        post.isabelleTerm)))

    val wp2 = Expression(state.isabelle.get, state.predicateT, wp)
    val colocality2 = Expression(state.isabelle.get, state.boolT, colocality)
    (wp2,List(colocality2))
  }

  val callWpOp: Operation[((List[Term], List[Term], List[Term]), (List[Term], Term)), (Term, Term)] =
    Operation.implicitly[((List[pure.Term], List[pure.Term], List[pure.Term]), (List[pure.Term], pure.Term)), (pure.Term, pure.Term)]("callWp")
}
