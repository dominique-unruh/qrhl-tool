package qrhl.tactic

import info.hupel.isabelle.pure.Term
import info.hupel.isabelle.{Operation, pure}
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.logic._

import scala.collection.mutable

object EqualTac {
  def apply(): EqualTac = EqualTac(Nil)
}

import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec

case class EqualTac(exclude: List[String]) extends WpBothStyleTac() {
  override def getWP(state: State, left: Statement, right: Statement, post: RichTerm): (RichTerm, List[Subgoal]) = {
    val cvars = new mutable.LinkedHashSet[CVariable]()
    val qvars = new mutable.LinkedHashSet[QVariable]()
    val dummy = new mutable.LinkedHashSet[String]()

    val mismatches = new mutable.LinkedHashSet[(Statement,Statement)]()
    val env = state.environment

    def collectExpr(e: RichTerm): Unit = e.caVariables(env,cvars,dummy)

    def collect(l: Statement, r: Statement) : Unit = (l,r) match {
      case (Assign(xl,el), Assign(xr,er)) if xl==xr && el==er =>
        cvars += xl; collectExpr(el)
      case (Sample(xl,el), Sample(xr,er)) if xl==xr && el==er =>
        cvars += xl; el.caVariables(env,cvars,dummy)
      case (Block(ssl @ _*), Block(ssr @ _*)) if ssl.length==ssr.length =>
        for ((sl,sr) <- ssl.zip(ssr))
          collect(sl,sr)
      case (Call(namel, argsl @ _*), Call(namer, argsr @ _*)) if namel==namer && !exclude.contains(namel) =>
        val p = env.programs(namel)
        val (cv,qv,_,_) = p.variablesRecursive
        cvars ++= cv; qvars ++= qv
        assert(argsl.length==argsr.length)
        for ((pl,pr) <- argsl.zip(argsr))
          collect(pl,pr)
      case (While(el,bodyl), While(er,bodyr)) if el==er =>
        collectExpr(el); collect(bodyl,bodyr)
      case (IfThenElse(el,p1l,p2l), IfThenElse(er,p1r,p2r)) if el==er =>
        collectExpr(el); collect(p1l,p1r); collect(p2l,p2r)
      case (QInit(vs1,e1),QInit(vs2,e2)) if vs1==vs2 && e1==e2 =>
        qvars ++= vs1; collectExpr(e1)
      case (Measurement(vl,vsl,el),Measurement(vr,vsr,er)) if vl==vr && vsl==vsr && el==er =>
        cvars += vl; collectExpr(el); qvars ++= vsl
      case (QApply(vsl,el), QApply(vsr,er)) if vsl==vsr && el==er =>
        qvars ++= vsl; collectExpr(el)
      case lr => mismatches.add(lr)
    }

    collect(left,right)

    val cvarsIdx1 = cvars.toList.map(_.index1)
    val cvarsIdx2 = cvars.toList.map(_.index2)
    val qvarsIdx1 = qvars.toList.map(_.index1)
    val qvarsIdx2 = qvars.toList.map(_.index2)
//    val forbidden = cvarsIdx1.map(_.name).toSet ++ cvarsIdx2.map(_.name) ++ qvarsIdx1.map(_.name) ++ qvarsIdx2.map(_.name)

    val (wp, colocality) = state.isabelle.isabelle.invoke(callWpOp,
      ((cvarsIdx1.map(_.valueTerm), cvarsIdx2.map(_.valueTerm),
        qvarsIdx1.map(_.variableTerm)), (qvarsIdx2.map(_.variableTerm),
        post.isabelleTerm, state.isabelle.contextId)))
//    val wp2 = Expression(Isabelle.predicateT, wp)
//    val colocality2 = Expression(Isabelle.boolT, colocality)

    if (mismatches.nonEmpty) {
      println("*** WARNING: equal tactic with mismatches is not proven or carefully thought through yet! ***")
    }

    val mismatchGoals = mismatches.toList.map {
      case (l,r) => QRHLSubgoal(l.toBlock,r.toBlock,wp,wp,Nil)
    }

    (wp,AmbientSubgoal(colocality)::mismatchGoals)
  }

  val callWpOp: Operation[((List[Term], List[Term], List[Term]), (List[Term], Term, BigInt)), (RichTerm, RichTerm)] =
    Operation.implicitly[((List[pure.Term], List[pure.Term], List[pure.Term]), (List[pure.Term], Term, BigInt)), (RichTerm, RichTerm)]("callWp")
}

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
