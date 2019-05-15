package qrhl.tactic

import info.hupel.isabelle.pure.Term
import info.hupel.isabelle.{Operation, pure}
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.logic._

import scala.collection.mutable
import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec
import qrhl.isabelle.Codecs._

import scala.collection.immutable.ListSet

case class EqualTac(exclude: List[String], qvariables: List[QVariable]) extends WpBothStyleTac() {
  def diff(left:Statement, right:Statement): (Statement, List[(Statement,Statement)]) = {
    val mismatches = new mutable.ListBuffer[(Statement,Statement)]()

    def collect(l: Statement, r: Statement) : Statement = (l,r) match {
      case (Assign(xl,el), Assign(xr,er)) if xl==xr && el==er =>
        Assign(xl,el)
      case (Sample(xl,el), Sample(xr,er)) if xl==xr && el==er =>
        Sample(xl,el)
      case (Block(ssl @ _*), Block(ssr @ _*)) if ssl.length==ssr.length =>
        Block(ssl.zip(ssr).map { case (a,b) => collect(a,b) } :_*)
      case (Call(namel, argsl @ _*), Call(namer, argsr @ _*)) if namel==namer && !exclude.contains(namel) =>
        assert(argsl.length==argsr.length)
        Call(namel, argsl.zip(argsr).map { case (a,b) => collect(a,b).asInstanceOf[Call] } :_*)
      case (While(el,bodyl), While(er,bodyr)) if el==er =>
        While(el, collect(bodyl,bodyr).toBlock)
      case (IfThenElse(el,p1l,p2l), IfThenElse(er,p1r,p2r)) if el==er =>
        IfThenElse(el, collect(p1l,p1r).toBlock, collect(p2l,p2r).toBlock)
      case (QInit(vs1,e1),QInit(vs2,e2)) if vs1==vs2 && e1==e2 =>
        QInit(vs1,e1)
      case (Measurement(vl,vsl,el),Measurement(vr,vsr,er)) if vl==vr && vsl==vsr && el==er =>
        Measurement(vl,vsl,el)
      case (QApply(vsl,el), QApply(vsr,er)) if vsl==vsr && el==er =>
        QApply(vsl,el)
      case lr =>
        val idx = mismatches.indexOf(lr)
        if (idx == -1) {
          mismatches += lr
          Call(s"@${mismatches.length-1}")
        }
        else
          Call(s"@$idx")
    }

    val context = collect(left, right)

    (context, mismatches.toList)
  }

  override def getWP(state: State, left: Statement, right: Statement, post: RichTerm): (RichTerm, List[Subgoal]) = {
    val (context, mismatches) = diff(left,right)

    val env = state.environment

    val varUse = context.variableUse(env)

    val cvars = varUse.classical
    val qvars =
      if (qvariables.isEmpty)
        varUse.quantum
      else {
        if (!varUse.quantum.subsetOf(qvariables.toSet))
          throw UserException(s"You need to list at least the following qvars: ${varUse.quantum.mkString(", ")}")
        ListSet(qvariables:_*)
      }

    val in_cvars = cvars -- varUse.overwrittenClassical
    val in_qvars = qvars -- varUse.overwrittenQuantum

    val cvarsIdx1 = cvars.toList.map(_.index1)
    val cvarsIdx2 = cvars.toList.map(_.index2)
    val qvarsIdx1 = qvars.toList.map(_.index1)
    val qvarsIdx2 = qvars.toList.map(_.index2)

    val in_cvarsIdx1 = in_cvars.toList.map(_.index1)
    val in_cvarsIdx2 = in_cvars.toList.map(_.index2)
    val in_qvarsIdx1 = in_qvars.toList.map(_.index1)
    val in_qvarsIdx2 = in_qvars.toList.map(_.index2)

    // Computes wp and colocality, see QRHL.callWp in Isabelle/ML sources
    val (in_wp, wp, colocality) = state.isabelle.isabelle.invoke(callWpOp,
      (in_cvarsIdx1.map(_.valueTerm), in_cvarsIdx2.map(_.valueTerm),
        in_qvarsIdx1.map(_.variableTerm), in_qvarsIdx2.map(_.variableTerm),
        cvarsIdx1.map(_.valueTerm), cvarsIdx2.map(_.valueTerm),
        qvarsIdx1.map(_.variableTerm), qvarsIdx2.map(_.variableTerm),
        post.isabelleTerm, state.isabelle.contextId))

    val mismatchGoals = mismatches.map {
      case (l,r) => QRHLSubgoal(l.toBlock,r.toBlock,wp,wp,Nil)
    }

    // For each element (l,e) of mismatches, mismatchGoals contains a goal of the form {wp}l~r{wp}

    // Returns wp as the "weakest precondition", and colocality and mismatchGoals as additional goals.
    (in_wp, AmbientSubgoal(colocality)::mismatchGoals)
  }

  val callWpOp: Operation[(List[Term], List[Term], List[Term], List[Term], List[Term], List[Term], List[Term], List[Term], Term, BigInt), (RichTerm, RichTerm, RichTerm)] =
    Operation.implicitly[(List[Term], List[Term], List[Term], List[Term], List[Term], List[Term], List[Term], List[Term], Term, BigInt), (RichTerm, RichTerm, RichTerm)]("callWp")
}

/*
case object EqualTacOld extends WpBothStyleTac() {
  override def getWP(state: State, left: Statement, right: Statement, post: RichTerm): (RichTerm, List[Subgoal]) = {
    if (left!=right) throw UserException(s"The last statement on both sides needs to be the same")
    val (cvars,qvars,_,_) = left.cqapVariables(state.environment,recurse = true)
    val cvarsIdx1 = cvars.map(_.index1)
    val cvarsIdx2 = cvars.map(_.index2)
    val qvarsIdx1 = qvars.map(_.index1)
    val qvarsIdx2 = qvars.map(_.index2)
//    val forbidden = cvarsIdx1.map(_.name).toSet ++ cvarsIdx2.map(_.name) ++ qvarsIdx1.map(_.name) ++ qvarsIdx2.map(_.name)

    val (wp, colocality) = state.isabelle.isabelle.invoke(callWpOp,
      ((cvarsIdx1.map(_.valueTerm), cvarsIdx2.map(_.valueTerm),
        qvarsIdx1.map(_.variableTerm)), (qvarsIdx2.map(_.variableTerm),
        post.isabelleTerm, state.isabelle.contextId)))

//    val wp2 = Expression(Isabelle.predicateT, wp)
//    val colocality2 = Expression(Isabelle.boolT, colocality)
    (wp,List(AmbientSubgoal(colocality)))
  }

  val callWpOp: Operation[((List[Term], List[Term], List[Term]), (List[Term], Term, BigInt)), (RichTerm, RichTerm)] =
    Operation.implicitly[((List[pure.Term], List[pure.Term], List[pure.Term]), (List[pure.Term], pure.Term, BigInt)), (RichTerm, RichTerm)]("callWp")
}
*/
