package qrhl.tactic

import java.io.IOException

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
import qrhl.tactic.EqualTac.{FixableConditionException, UnfixableConditionException, logger}

import scala.collection.immutable.ListSet
import Utils.listSetUpcast
import Utils.ListSetUtils
import qrhl.logic.Variable.quantum

import scala.tools.nsc.backend.jvm.opt.BytecodeUtils.VarInstruction

case class EqualTac(exclude: List[String], in: List[Variable], mid: List[Variable], out: List[Variable], amount:Int=1) extends WpBothStyleTac(leftAmount=amount, rightAmount=amount) {
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

  def checkConditions(varUse: VariableUse, in: Set[Variable], out: Set[Variable], mid: Set[Variable]): Unit = {
    //    assumes qrhl_s: "⋀i. qRHL (R ⊓ Eq Vmid) (s i) (s' i) (R ⊓ Eq Vmid)"
    // TODO
    println("*** MISSING CHECKS ***")

    //    assumes aux_Vmid: "aux ∈ Vmid"
    // TODO
    println("*** MISSING CHECKS ***")

    //    assumes inner_Vmid: "inner C ⊆ Vmid"
    {
      val missing = varUse.inner -- mid
      if (missing.nonEmpty)
        throw FixableConditionException("inner(C) ⊆ Vmid", extraMid = missing)
    }
    //    assumes Vout_Vmid: "Vout ⊆ Vmid"
    {
      val missing = out -- mid
      if (missing.nonEmpty)
        throw FixableConditionException("Vout ⊆ Vmid", extraMid = missing)
    }

    //    assumes Vout_overwr_Vin: "Vout - overwr C ⊆ Vin"
    {
      val missing = out -- varUse.overwritten -- in
      if (missing.nonEmpty)
        throw FixableConditionException("Vout - overwr(C) ⊆ Vin", extraIn = missing)
    }

    //    assumes Vout_Vin_R: "(Vout - Vin) ∩ Rv = {}"
    // TODO
    println("*** MISSING CHECKS ***")

    //    assumes Vin_Vout_overwr: "quantum' Vin ⊆ Vout ∪ overwr C"
    {
    val missing = in.filter(_.isQuantum) -- varUse.overwritten -- out
      if (missing.nonEmpty)
        throw FixableConditionException("quantum(Vin) ⊆ Vout ∪ overwr(C)", extraOut = missing)
    }

    //    assumes Vin_Vout_R: "quantum' (Vin - Vout) ∩ Rv = {}"
    // TODO
    println("*** MISSING CHECKS ***")

    //    assumes Vmid_R_Vin_covered: "Vmid ∩ Rv ⊆ Vin ∪ covered C"
    // TODO
    println("*** MISSING CHECKS ***")

    //    assumes Vmid_R_Vout_covered: "quantum' (Vmid ∩ Rv) ⊆ Vout ∪ covered C"
    // TODO
    println("*** MISSING CHECKS ***")

    //    assumes Vmid_s_Vin_covered: "⋀i. Vmid ∩ (fv (s i) ∪ fv (s' i)) ⊆ Vin ∪ covered C ∪ classical' (overwr (s i) ∩ overwr (s' i))"
    // TODO
    println("*** MISSING CHECKS ***")

    //    assumes Vmid_s_Vout_covered: "⋀i. quantum' Vmid ∩ (fv (s i) ∪ fv (s' i)) ⊆ Vout ∪ covered C"
    // TODO
    println("*** MISSING CHECKS ***")

    //    assumes C_Vmid: "fv C ⊆ Vmid"
    {
      val missing = varUse.freeVariables -- mid
      if (missing.nonEmpty)
        throw FixableConditionException("fv(C) ⊆ Vmid", extraMid = missing)
    }

    //    assumes C_Vin_overwr: "fv C ⊆ Vin ∪ overwr C"
    {
      val missing = varUse.freeVariables -- varUse.overwritten -- in
      if (missing.nonEmpty)
        throw FixableConditionException("fv(C) ⊆ Vin ∪ overwr(C)", extraIn = missing)
    }

    //    assumes C_Vin_R: "fv C ⊆ Vin - Rv"
    // TODO
    println("*** MISSING CHECKS ***")

    //    assumes C_Vout: "quantum' (fv C) ⊆ Vout"
    {
      val missing = varUse.freeVariables.filter(_.isQuantum) -- out
      if (missing.nonEmpty)
        throw FixableConditionException("quantum(fv C) ⊆ Vout", extraOut = missing)
    }

    //    assumes R_inner: "Rv ∩ inner C = {}"
    // TODO
    println("*** MISSING CHECKS ***")

    //    assumes R_written: "Rv ∩ written C = {}"
    // TODO
    println("*** MISSING CHECKS ***")
  }

  override def getWP(state: State, left: Statement, right: Statement, post: RichTerm): (RichTerm, List[Subgoal]) = {
    val env = state.environment
    val isabelle = state.isabelle
    val contextId = isabelle.contextId

    // ==== Get the context and the mismatches

    val (context, mismatches) = diff(left,right)

    logger.debug(s"Context: $context")

    val varUse = context.variableUse(env)

    println("Variable use of the context:")
    println(varUse)

    // ==== Choose in/out/mid variables

    var in_ = mutable.LinkedHashSet(this.in:_*)
    var mid_ = mutable.LinkedHashSet(this.mid:_*)
    var out_ = mutable.LinkedHashSet(this.out:_*)

    def printVars(): Unit = {
      println(s"In variables  (Vin):  $in_")
      println(s"Mid variables (Vmid): $mid_")
      println(s"Out variables (Vout): $out_")
    }

    var found = false
    while (!found) {
      try {
        checkConditions(varUse, in = in_.toSet, out = out_.toSet, mid = mid_.toSet)
        found = true
      } catch {
        case UnfixableConditionException(msg) =>
          printVars()
          throw UserException(s"Could not chose variables such that the tactic applies: $msg")
        case FixableConditionException(msg, extraIn, extraMid, extraOut) =>
          println(s"""The condition "$msg" is not safistied yet""")
          if (extraIn.nonEmpty) {
            println(s"Adding to Vin:  $extraIn")
            in_ ++= extraIn
          }
          if (extraMid.nonEmpty) {
            println(s"Adding to Vmid: $extraMid")
            mid_ ++= extraMid
          }
          if (extraOut.nonEmpty) {
            println(s"Adding to Vout: $extraOut")
            out_ ++= extraOut
          }
      }
    }

    printVars()

    val in = ListSet(in_.toSeq:_*)
    val mid = ListSet(mid_.toSeq:_*)
    val out = ListSet(out_.toSeq:_*)

    // ==== Convenient abbreviations

    val out_cvarsIdx1 = out.toList collect { case v : CVariable => v.index1.valueTerm }
    val out_cvarsIdx2 = out.toList collect { case v : CVariable => v.index2.valueTerm }
    val cwvarsIdx1 = varUse.written.toList collect { case v : CVariable => v.index1.valueTerm }
    val cwvarsIdx2 = varUse.written.toList collect { case v : CVariable => v.index2.valueTerm }
    val out_qvarsIdx1 = out.toList collect { case v : QVariable => v.index1.variableTerm }
    val out_qvarsIdx2 = out.toList collect { case v : QVariable => v.index2.variableTerm }
    val in_cvarsIdx1 = in.toList collect { case v : CVariable => v.index1.valueTerm }
    val in_cvarsIdx2 = in.toList collect { case v : CVariable => v.index2.valueTerm }
    val in_qvarsIdx1 = in.toList collect { case v : QVariable => v.index1.variableTerm }
    val in_qvarsIdx2 = in.toList collect { case v : QVariable => v.index2.variableTerm }
    val mid_cvarsIdx1 = mid.toList collect { case v : CVariable => v.index1.valueTerm }
    val mid_cvarsIdx2 = mid.toList collect { case v : CVariable => v.index2.valueTerm }
    val mid_qvarsIdx1 = mid.toList collect { case v : QVariable => v.index1.variableTerm }
    val mid_qvarsIdx2 = mid.toList collect { case v : QVariable => v.index2.variableTerm }

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

    val Ain = isabelle.isabelle.invoke(mk_equals_wp, (contextId, R, in_cvarsIdx1, in_cvarsIdx2, in_qvarsIdx1, in_qvarsIdx2))
    logger.debug(s"Ain: $Ain")

    val Amid = isabelle.isabelle.invoke(mk_equals_wp, (contextId, R, mid_cvarsIdx1, mid_cvarsIdx2, mid_qvarsIdx1, mid_qvarsIdx2))
    logger.debug(s"Amid: $Amid")

    // ==== Check choices

    // fv(R)^qu # fv(C)^qu: by subgoal
    // fv(R)^qu # Qout \ Qmid: by subgoal
    val forbidden = varUse.quantum +++ (quantum(mid) -- quantum(out))
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
  private case class FixableConditionException(msg: String, extraIn:Traversable[Variable]=Nil,
                                               extraMid:Traversable[Variable]=Nil,
                                               extraOut:Traversable[Variable]=Nil) extends Exception {
    assert(extraIn.nonEmpty || extraMid.nonEmpty || extraOut.nonEmpty)
  }
  private case class UnfixableConditionException(msg: String) extends Exception
}
