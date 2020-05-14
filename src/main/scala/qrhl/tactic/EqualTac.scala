package qrhl.tactic

import info.hupel.isabelle.pure.Term
import info.hupel.isabelle.{Operation, pure}
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.logic._

import scala.collection.mutable
import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec
import org.log4s
import qrhl.isabelle.Codecs._
import qrhl.tactic.EqualTac.logger

import scala.collection.immutable.ListSet

import Utils.listSetUpcast
import Utils.ListSetUtils

case class EqualTac(exclude: List[String], qvariables: List[QVariable], midqvariables: List[QVariable], amount:Int=1) extends WpBothStyleTac(leftAmount=amount, rightAmount=amount) {
  def diff(left:Statement, right:Statement): (Statement, List[(Statement,Statement)]) = {
    val mismatches = new mutable.ListBuffer[(Statement,Statement)]()

    // Finds a common context matching both l,r, and collects the differences in mismatches
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
      case (Local(varsl, bodyl), Local(varsr, bodyr))
        if Set(varsl :_*) == Set(varsr :_*) =>
        Local(varsl, collect(bodyl, bodyr).toBlock)
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
    val env = state.environment
    val isabelle = state.isabelle
    val contextId = isabelle.contextId

    // ==== Get the context and the mismatches

    val (context, mismatches) = diff(left,right)

    logger.debug(s"Context: $context")

    val varUse = context.variableUse(env)

    logger.debug(s"Context has the following variable use: $varUse")

    // ==== Choose in/out/mid variables

    val out_cvars = varUse.classical
    val cwvars = varUse.written collect { case v : CVariable => v }
    val out_qvars =
      if (qvariables.isEmpty)
        varUse.quantum
      else {
        ListSet(qvariables:_*)
      }

    // TODO: could be user choosable
    val in_cvars = out_cvars -- varUse.overwrittenClassical
    val in_qvars = out_qvars -- varUse.overwrittenQuantum

    val inner_cvars = varUse.innerClassical
    val inner_qvars = varUse.innerQuantum

    val mid_cvars = out_cvars +++ inner_cvars
    val mid_qvars =
      if (midqvariables.isEmpty)
        out_qvars +++ inner_qvars
      else
        ListSet(midqvariables:_*)
    logger.debug(s"XXXXX mid_qvars=${mid_qvars}")

    logger.debug(s"In variables: $in_cvars, $in_qvars; out variables: $out_cvars, $out_qvars; mid variables: $mid_cvars, $mid_qvars")

    // ==== Convenient abbreviations

    val out_cvarsIdx1 = out_cvars.toList.map(_.index1).map(_.valueTerm)
    val out_cvarsIdx2 = out_cvars.toList.map(_.index2).map(_.valueTerm)
    val cwvarsIdx1 = cwvars.toList.map(_.index1).map(_.valueTerm)
    val cwvarsIdx2 = cwvars.toList.map(_.index2).map(_.valueTerm)
    val out_qvarsIdx1 = out_qvars.toList.map(_.index1).map(_.variableTerm)
    val out_qvarsIdx2 = out_qvars.toList.map(_.index2).map(_.variableTerm)
    val in_cvarsIdx1 = in_cvars.toList.map(_.index1).map(_.valueTerm)
    val in_cvarsIdx2 = in_cvars.toList.map(_.index2).map(_.valueTerm)
    val in_qvarsIdx1 = in_qvars.toList.map(_.index1).map(_.variableTerm)
    val in_qvarsIdx2 = in_qvars.toList.map(_.index2).map(_.variableTerm)
    val mid_cvarsIdx1 = mid_cvars.toList.map(_.index1).map(_.valueTerm)
    val mid_cvarsIdx2 = mid_cvars.toList.map(_.index2).map(_.valueTerm)
    val mid_qvarsIdx1 = mid_qvars.toList.map(_.index1).map(_.variableTerm)
    val mid_qvarsIdx2 = mid_qvars.toList.map(_.index2).map(_.variableTerm)

    // ==== Get R (the "rest" of the predicate), and the resulting pre/postconditions
    val R = isabelle.isabelle.invoke(
      Operation.implicitly[(BigInt, RichTerm, List[Term], List[Term], List[Term], List[Term], List[Term]),RichTerm]("equal_get_R"),
      (contextId, post,
        out_cvarsIdx1, out_cvarsIdx2,
        out_qvarsIdx1, out_qvarsIdx2,
        (cwvarsIdx1 ++ cwvarsIdx2)))

    logger.debug(s"R: $R")

    val rVarUse = R.caVariables(env)

    val mk_equals_wp = Operation.implicitly[(BigInt, RichTerm, List[Term], List[Term], List[Term], List[Term]), RichTerm]("mk_equals_wp")

//    val Aout = isabelle.isabelle.invoke(mk_equals_wp, (contextId, R, out_cvarsIdx1, out_cvarsIdx2, out_qvarsIdx1, out_qvarsIdx2))
//    logger.debug(s"Aout: $Aout")

    val Ain = isabelle.isabelle.invoke(mk_equals_wp, (contextId, R, in_cvarsIdx1, in_cvarsIdx2, in_qvarsIdx1, in_qvarsIdx2))
    logger.debug(s"Ain: $Ain")

    val Amid = isabelle.isabelle.invoke(mk_equals_wp, (contextId, R, mid_cvarsIdx1, mid_cvarsIdx2, mid_qvarsIdx1, mid_qvarsIdx2))
    logger.debug(s"Amid: $Amid")

    // ==== Check choices

    // fv(C) <= Xout Qout
    assert (varUse.classical.subsetOf(out_cvars))
    if (!varUse.quantum.subsetOf(out_qvars))
      throw UserException(s"You need to list at least the following qvars: ${varUse.quantum.mkString(", ")}")

    // Qout \ ow(C) <= Qin <= Qout
    assert((out_qvars -- varUse.overwrittenQuantum).subsetOf(in_qvars))
    assert(in_qvars.subsetOf(out_qvars))
    // Xout \ ow(C) <= Xin <= Xout
    assert((out_cvars -- varUse.overwrittenClassical).subsetOf(in_cvars))
    assert(in_cvars.subsetOf(out_cvars))
    // Qmid >= Qout + inner(C)^qu
    assert((out_qvars +++ inner_qvars).subsetOf(mid_qvars))
    // Xmid >= Xout + inner(C)^cl
    assert((out_cvars +++ inner_cvars).subsetOf(mid_cvars))
    
    // # means disjoint
    // fv(R)^qu # fv(C)^qu: by subgoal below

    // C is fv(R)^cl-readonly
    assert(rVarUse.classical.intersect(varUse.writtenClassical).isEmpty)

    // fv(R)^qu # Qout \ Qmid: by subgoal below

    // fv(R)^cl # Xout \ Xmid
    assert(rVarUse.classical.intersect(out_cvars -- mid_cvars).isEmpty)


    // ==== Create subgoals

    // fv(R)^qu # fv(C)^qu: by subgoal
    // fv(R)^qu # Qout \ Qmid: by subgoal
    val forbidden = varUse.quantum +++ (mid_qvars -- out_qvars)
    val forbidden12 = (forbidden.map(_.index1) +++ forbidden.map(_.index2)) map { v => (v.variableName, v.valueTyp) }
    val colocality = isabelle.isabelle.invoke(FrameRuleTac.colocalityOp,
      (contextId, R.isabelleTerm, forbidden12.toList))

    logger.debug(s"Colocality: $colocality")


    // For each element (l,e) of mismatches, mismatchGoals contains a goal of the form {Amid}l~r{Amid}
    val mismatchGoals = mismatches.map {
      case (l,r) => QRHLSubgoal(l.toBlock,r.toBlock,Amid,Amid,Nil)
    }

    (Ain, AmbientSubgoal(colocality)::mismatchGoals)
  }
}

object EqualTac {
  private val logger = log4s.getLogger
}
