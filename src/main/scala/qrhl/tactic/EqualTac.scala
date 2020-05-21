package qrhl.tactic

import java.io.IOException

import info.hupel.isabelle.pure.{Free, Term, Typ}
import info.hupel.isabelle.{Operation, pure}
import qrhl._
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.logic._

import scala.collection.mutable
import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec
import org.log4s
import qrhl.isabelle.Codecs._
import qrhl.tactic.EqualTac.{isInfinite_op, logger}

import scala.collection.immutable.ListSet
import Utils.listSetUpcast
import Utils.ListSetUtils
import qrhl.isabelle.Isabelle.{Context, QuantumEqualityFull}
import qrhl.logic.Variable.quantum
import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec
import info.hupel.isabelle.hol.HOLogic
import Variable.varsToString

import EqualTac._

import scala.collection.mutable.ListBuffer
import scala.util.control.{Breaks, ControlThrowable}

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

  private def checkConditions(env: Environment, varUse: VariableUse, mismatchesFree: Set[Variable],
                      isInfinite: Variable => Boolean,
                      in: Set[Variable], out: Set[Variable], mid: Set[Variable]): Unit = {
  }

  override def getWP(state: State, left: Statement, right: Statement, post: RichTerm): (RichTerm, List[Subgoal]) = {
    val env = state.environment
    val isabelle = state.isabelle
    val contextId = isabelle.contextId

    // ==== Get the context and the mismatches

    val (context, mismatches) = diff(left,right)

    logger.debug(s"Context: $context")

    val varUse = context.variableUse(env)

    val mismatchesVarUse = mismatches map { case (l,r) => (l.variableUse(env), r.variableUse(env)) }
    val mismatchesFree = mutable.HashSet[Variable]()
    for ((l,r) <- mismatchesVarUse) {
      mismatchesFree ++= l.freeVariables
      mismatchesFree ++= r.freeVariables
    }

    println("Variable use of the context:")
    println(varUse)

    // ==== Choose in/out/mid variables

    val in = mutable.LinkedHashSet(this.in:_*)
    val mid = mutable.LinkedHashSet(this.mid:_*)
    val out = mutable.LinkedHashSet(this.out:_*)

    def printVars(): Unit = {
      println(s"In variables  (Vin):  $in")
      println(s"Mid variables (Vmid): $mid")
      println(s"Out variables (Vout): $out")
    }

    // Classical variables that we remove from the postcondition
    // This will be done at the end in one go
    val classicalsRemovedPost = mutable.LinkedHashSet[CVariable]()
    // Quantum variables that we removed from the postcondition
    // The postcondition will be updated right away
    var removedQeq : ListSet[QVariable] = null

    var updated = false
    def add(msg: String, extraIn:Set[Variable]=Set.empty, extraMid:Set[Variable]=Set.empty,
            extraOut:Set[Variable]=Set.empty): Unit = {
      val extraIn2 = extraIn -- in
      val extraOut2 = extraOut -- out
      val extraMid2 = extraMid -- mid
      if (msg != null && (extraIn2.nonEmpty || extraMid2.nonEmpty || extraOut2.nonEmpty))
        println(s"""Trying to make "$msg" true:""")

      if (extraIn2.nonEmpty) {
        println(s"Adding to Vin:  ${varsToString(extraIn2)}")
        updated = true
        in ++= extraIn2
      }
      if (extraMid2.nonEmpty) {
        println(s"Adding to Vmid: ${varsToString(extraMid2)}")
        updated = true
        mid ++= extraMid2
      }
      if (extraOut2.nonEmpty) {
        if (removedQeq != null) {
          val quantum = Variable.quantum(extraOut2)
          logger.debug(s"add extraOut ${quantum} # ${removedQeq}")
          if (!quantum.toSet.subsetOf(removedQeq))
            throw UserException(s"Trying to add ${varsToString(quantum)} to Vout, but we already committed on removing " +
              s"quantum equality for ${varsToString(removedQeq)} from the postcondition")
        }
        println(s"Adding to Vout: ${varsToString(extraOut2)}")
        updated = true
        out ++= extraOut2
      }
    }

    // TODO: this should be a list that also excludes the removed classical vars
    var varUsePostcondition = post.caVariables(env, deindex=true)
    var postcondition = post

    def removeFromPost(msg: String, vars: Set[Variable]): Unit = {
      val quantum = Variable.quantum(vars) & varUsePostcondition.quantum
      val classical = Variable.classical(vars) & varUsePostcondition.classical -- classicalsRemovedPost

      logger.debug(s"removeFromPost ${msg}, ${varsToString(quantum ++ classical)}")

      if (msg != null && (quantum.nonEmpty || classical.nonEmpty))
        println(s"""Trying to make "$msg" true:""")

      if (classical.nonEmpty) {
        updated = true
        println(s"Removing classical variables $classical from postcondition")
        classicalsRemovedPost ++= classical
      }

      if (quantum.nonEmpty) {
        updated = true
        if (removedQeq != null)
          throw UserException(s"Cannot remove quantum variables because we already remove one quantum equality from postcondition")

        val (newPostcondition, newRemovedQeq) = EqualTac.removeQeq(env, postcondition, quantum)
        postcondition = newPostcondition
        removedQeq = newRemovedQeq
        varUsePostcondition = postcondition.caVariables(env)

        if (!out.subsetOf(removedQeq))
          throw UserException(s"Should remove quantum equality for variables ${varsToString(removedQeq)}, but Vout already contains ${varsToString(out)}")
        println(s"Removing quantum variables ${varsToString(removedQeq)} from postcondition")
        out ++= removedQeq
      }
    }

    val isInfiniteHashtable = mutable.HashMap[Variable, Boolean]()
    def isInfinite(v: Variable): Boolean =
      isInfiniteHashtable.getOrElseUpdate(v, {
        val result = state.isabelle.isabelle.invoke(isInfinite_op, (isabelle.contextId, v.valueTyp))
        logger.debug(s"Checking infiniteness of $v: $result")
        result
      })

    // Ensuring all conditions except those referring to qRHL subgoals

    // Removing quantum equality involving variables in out.
    // Not an explicit condition for applying the adversary rule, but since we will later add a quantum equality with
    // the variables in out anyway, this won't hurt
    if (out.nonEmpty)
      removeFromPost(null, out.toSet)
    // It is conceivable that there is more than one quantum equality with those variables.
    // In that case we might remove the wrong one. However, this rare (or impossible?) case
    // can be remedied by explicitly specifying the quantum variables in out

    //    assumes inner_Vmid: "inner C ⊆ Vmid"
    add("inner(C) ⊆ Vmid", extraMid = varUse.inner)
    //    assumes C_Vmid: "fv C ⊆ Vmid"
    add("fv(C) ⊆ Vmid", extraMid = varUse.freeVariables)
    //    assumes C_Vin_overwr: "fv C ⊆ Vin ∪ overwr C"
    add("fv(C) ⊆ Vin ∪ overwr(C)", extraIn = varUse.freeVariables -- varUse.overwritten)
    //    assumes C_Vout: "quantum' (fv C) ⊆ Vout"
    add("quantum(fv C) ⊆ Vout", extraOut = varUse.freeVariables.filter(_.isQuantum))

    // Here we loop until nothing changes any more because adding variables to satisfy one condition may make another wrong again
    do {
      updated = false

      //    assumes Vout_Vmid: "Vout ⊆ Vmid"
      add("Vout ⊆ Vmid", extraMid = out.toSet)

      //    assumes Vout_overwr_Vin: "Vout - overwr C ⊆ Vin"
      add("Vout - overwr(C) ⊆ Vin", extraIn = (out -- varUse.overwritten).toSet)

      //    assumes Vin_Vout_overwr: "quantum' Vin ⊆ Vout ∪ overwr C"
      add("quantum(Vin) ⊆ Vout ∪ overwr(C)", extraOut = in.toSet.filter(_.isQuantum) -- varUse.overwritten)

      //    assumes Vmid_s_Vin_covered: "⋀i. Vmid ∩ (fv (s i) ∪ fv (s' i)) ⊆ Vin ∪ covered C ∪ classical' (overwr (s i) ∩ overwr (s' i))"
      for ((l,r) <- mismatchesVarUse) {
          add("Vmid ∩ (fv(l) ∪ fv(r)) ⊆ Vin ∪ covered C ∪ classical' (overwr(l) ∩ overwr(r)) for every mismatch l,r",
            extraIn = (mid.toSet & (l.freeVariables ++ r.freeVariables)) -- varUse.covered -- (l.overwritten & r.overwritten).filter(_.isClassical))
      }

      //    assumes Vmid_s_Vout_covered: "⋀i. quantum' Vmid ∩ (fv (s i) ∪ fv (s' i)) ⊆ Vout ∪ covered C"
      for ((l,r) <- mismatchesVarUse) {
          add("quantum' Vmid ∩ (fv(l) ∪ fv(r)) ⊆ Vout ∪ covered(C) for every mismatch l,r", extraOut = (mid.toSet.filter(_.isClassical) & (l.freeVariables & r.freeVariables)) -- varUse.covered)
      }

      //    assumes Vout_Vin_R: "(Vout - Vin) ∩ Rv = {}"
      removeFromPost("(Vout - Vin) ∩ Rv = {}", (out -- in).toSet)

      //    assumes Vin_Vout_R: "quantum' (Vin - Vout) ∩ Rv = {}"
      removeFromPost("quantum' (Vin - Vout) ∩ Rv = {}", (in.filter(_.isQuantum) -- out).toSet)

      //    assumes R_inner: "Rv ∩ inner C = {}"
      removeFromPost("Rv ∩ inner C = {}", varUse.inner)

      //    assumes R_written: "Rv ∩ written C = {}"
      removeFromPost("Rv ∩ written C = {}", varUse.written)

      //    assumes aux_Vmid: "aux ∈ Vmid"
      //    assumes aux_si: "⋀i. aux ∉ fv (s i)"
      //    assumes aux_s'i: "⋀i. aux ∉ fv (s' i)"
      //    assumes inf_aux: "infinite_var aux" and quant_aux: "is_quantum aux"
      // We construct the set of all variables in mid that satisfy the conditions for aux
      // We filter "isInfinite" last because this is the slowest part
      if (!mid.exists( v => v.isQuantum && !mismatchesFree.contains(v) && isInfinite(v))) {
        Breaks.breakable {
          for (v <- env.qVariables.values)
            if (!mismatchesFree.contains(v) && isInfinite(v)) {
              println("Adding an infinite quantum variable (that does not occur in any of the mismatches) in Vmid")
              add(msg = null, extraMid = Set(v))
              Breaks.break()
            }
          throw UserException(s"""Need an infinite quantum variable in Vmid that does not occur in any of the mismatches. I.e., not one of ${mismatchesFree.filter(_.isQuantum)}. If there is such a variable already, make sure the Isabelle simplified can prove "infinite (UNIV::typ)" where typ is the type of that variable.""")
        }
      }


      // If removedQeq == null, we do not know yet what the quantum variables of the postcondition will be.
      // (They could still become less) So we hold off adding quantum variables to `in` until things have stabilized (!updated)
      if (removedQeq!=null || !updated) {
        //    assumes C_Vin_R: "fv C ∩ Rv ⊆ Vin"
        add("fv(C) ∩ Rv ⊆ Vin", extraIn = varUse.freeVariables & varUsePostcondition.program)
        //    assumes Vmid_R_Vin_covered: "Vmid ∩ Rv ⊆ Vin ∪ covered C"
        add("Vmid ∩ Rv ⊆ Vin ∪ covered(C)", extraIn = (mid.toSet & varUsePostcondition.program) -- varUse.covered)
        //    assumes Vmid_R_Vout_covered: "quantum' (Vmid ∩ Rv) ⊆ Vout ∪ covered C"
        add("quantum' (Vmid ∩ Rv) ⊆ Vout ∪ covered(C)", extraOut = (mid.toSet.filter(_.isQuantum) & varUsePostcondition.program) -- varUse.covered)
      } else {
        //    assumes C_Vin_R: "fv C ∩ Rv ⊆ Vin"
        add("fv(C) ∩ Rv ⊆ Vin", extraIn = varUse.freeVariables.filter(_.isClassical) & varUsePostcondition.program)
        //    assumes Vmid_R_Vin_covered: "Vmid ∩ Rv ⊆ Vin ∪ covered C"
        add("Vmid ∩ Rv ⊆ Vin ∪ covered(C)", extraIn = (mid.toSet.filter(_.isClassical) & varUsePostcondition.program) -- varUse.covered)
      }

    } while (updated)

    printVars()
    logger.debug(s"Postcondition: ${postcondition}; without ${varsToString(classicalsRemovedPost)}")
    // TODO: do something with classicalsRemovedPost

//    // ==== Convenient abbreviations
//
//    val out_cvarsIdx1 = out.toList collect { case v : CVariable => v.index1.valueTerm }
//    val out_cvarsIdx2 = out.toList collect { case v : CVariable => v.index2.valueTerm }
//    val cwvarsIdx1 = varUse.written.toList collect { case v : CVariable => v.index1.valueTerm }
//    val cwvarsIdx2 = varUse.written.toList collect { case v : CVariable => v.index2.valueTerm }
//    val out_qvarsIdx1 = out.toList collect { case v : QVariable => v.index1.variableTerm }
//    val out_qvarsIdx2 = out.toList collect { case v : QVariable => v.index2.variableTerm }
//    val in_cvarsIdx1 = in.toList collect { case v : CVariable => v.index1.valueTerm }
//    val in_cvarsIdx2 = in.toList collect { case v : CVariable => v.index2.valueTerm }
//    val in_qvarsIdx1 = in.toList collect { case v : QVariable => v.index1.variableTerm }
//    val in_qvarsIdx2 = in.toList collect { case v : QVariable => v.index2.variableTerm }
//    val mid_cvarsIdx1 = mid.toList collect { case v : CVariable => v.index1.valueTerm }
//    val mid_cvarsIdx2 = mid.toList collect { case v : CVariable => v.index2.valueTerm }
//    val mid_qvarsIdx1 = mid.toList collect { case v : QVariable => v.index1.variableTerm }
//    val mid_qvarsIdx2 = mid.toList collect { case v : QVariable => v.index2.variableTerm }
//
    // TODO: Remove from Isabelle source, too
//    // ==== Get R (the "rest" of the predicate), and the resulting pre/postconditions
//    val R = isabelle.isabelle.invoke(
//      Operation.implicitly[(BigInt, RichTerm, List[Term], List[Term], List[Term], List[Term], List[Term]),RichTerm]("equal_get_R"),
//      (contextId, post,
//        out_cvarsIdx1, out_cvarsIdx2,
//        out_qvarsIdx1, out_qvarsIdx2,
//        (cwvarsIdx1 ++ cwvarsIdx2)))
//
//    logger.debug(s"R: $R")
//
//    val rVarUse = R.caVariables(env)
//
//
//
//    val mk_equals_wp = Operation.implicitly[(BigInt, RichTerm, List[Term], List[Term], List[Term], List[Term]), RichTerm]("mk_equals_wp")
//
//    val Ain = isabelle.isabelle.invoke(mk_equals_wp, (contextId, R, in_cvarsIdx1, in_cvarsIdx2, in_qvarsIdx1, in_qvarsIdx2))
//    logger.debug(s"Ain: $Ain")
//
//    val Amid = isabelle.isabelle.invoke(mk_equals_wp, (contextId, R, mid_cvarsIdx1, mid_cvarsIdx2, mid_qvarsIdx1, mid_qvarsIdx2))
//    logger.debug(s"Amid: $Amid")

    // ==== Check choices

//    // fv(R)^qu # fv(C)^qu: by subgoal
//    // fv(R)^qu # Qout \ Qmid: by subgoal
//    val forbidden = varUse.quantum +++ (quantum(mid) -- quantum(out))
//    val forbidden12 = (forbidden.map(_.index1) +++ forbidden.map(_.index2)) map { v => (v.variableName, v.valueTyp) }
//    val colocality = isabelle.isabelle.invoke(FrameRuleTac.colocalityOp,
//      (contextId, R.isabelleTerm, forbidden12.toList))

    // TODO
    val colocality = RichTerm(Isabelle.True_const)
    logger.debug(s"Colocality: $colocality")

    // TODO

    //    assumes qrhl_s: "⋀i. qRHL (R ⊓ Eq Vmid) (s i) (s' i) (R ⊓ Eq Vmid)"
    // TODO
    println("*** MISSING CHECKS ***")

    val Amid = makePredicate(mid,postcondition)
    val Ain = makePredicate(in,postcondition)

    // For each element (l,e) of mismatches, mismatchGoals contains a goal of the form {Amid}l~r{Amid}
    val mismatchGoals = mismatches.map {
      case (l,r) => QRHLSubgoal(l.toBlock,r.toBlock,Amid,Amid,Nil)
    }

    (Ain, AmbientSubgoal(colocality)::mismatchGoals)
  }
}

object EqualTac {
  private def makePredicate(vars: Traversable[Variable], predicate: RichTerm) : RichTerm = {
    val classical = Variable.classical(vars)
    val quantum = Variable.quantum(vars)

    val qeq : Term =
      if (quantum.isEmpty) Isabelle.predicate_top
      else {
        val left = VarTerm.varlist(quantum.map(_.index1)).toIsabellTerm
        val right = VarTerm.varlist(quantum.map(_.index2)).toIsabellTerm
        Isabelle.quantum_equality(left, right)
      }

    val ceq : Term =
      if (classical.isEmpty) Isabelle.True_const
      else {
        val eqs = classical.map { v => Isabelle.mk_eq(v.index1.variableTerm, v.index2.variableTerm) }
        Isabelle.conj(eqs.toSeq :_*)
      }

    val newPred = Isabelle.infOptimized(predicate.isabelleTerm, Isabelle.classical_subspace_optimized(ceq), qeq)
    RichTerm(Isabelle.predicateT, newPred)
  }

  private val logger = log4s.getLogger
//  private case class FixableConditionException(msg: String, extraIn:Traversable[Variable]=Nil,
//                                               extraMid:Traversable[Variable]=Nil,
//                                               extraOut:Traversable[Variable]=Nil) extends Exception {
//    assert(extraIn.nonEmpty || extraMid.nonEmpty || extraOut.nonEmpty)
//  }
//  private case class UnfixableConditionException(msg: String) extends Exception

  private val isInfinite_op = Operation.implicitly[(BigInt, Typ), Boolean]("is_finite")

  class SimpleQeq(env: Environment) {
    private object trySwapped extends ControlThrowable
    private object noMatch extends ControlThrowable

    def unapply(arg: Term): Option[ListSet[QVariable]] = arg match {
      case QuantumEqualityFull(Isabelle.IdOp(),q,Isabelle.IdOp(),r) =>
        val result = ListBuffer[QVariable]()

        def parse(vt1: Term, vt2: Term): Unit = (vt1, vt2) match {
          case (Isabelle.Variable_Unit(), Isabelle.Variable_Unit()) =>
          case (Isabelle.Variable_Singleton(Free(Variable.Indexed(name1, left1), typ1)),
                Isabelle.Variable_Singleton(Free(Variable.Indexed(name2, left2), typ2))) =>
            if (name1 != name2) throw noMatch
            val v = env.qVariables.getOrElse(name1, throw noMatch)
            if (v.variableTyp != typ1) throw noMatch
            if (v.variableTyp != typ2) throw noMatch
            if (!left1 || left2)
              throw trySwapped
            result += v
          case (Isabelle.Variable_Concat(vt1a, vt1b), Isabelle.Variable_Concat(vt2a, vt2b)) =>
            parse(vt1a, vt2a); parse(vt1b, vt2b)
          case _ =>
            throw noMatch
        }

        try {
          try
            parse(q, r)
          catch {
            case `trySwapped` => parse(r,q)
          }
        } catch {
          case `noMatch` => return None
        }

        // TODO check no repetitions
        Some(result.to[ListSet])
      case _ => None
    }
  }

  /** Finds a quantum equality ''(x1y1z1… ==q x2y2z2…)'' in `pred` such that ''vars ⊆ {x,y,z,…}''.
   * Then removes this quantum equality.
   * It is guaranteed that ''`result` ∩ (x1y1z1… ==q x2y2z2…)  ⊆   `pres`''.
   * If no such quantum equality is found, throws a [[qrhl.UserException]]
   * @param pred a quantum predicate
   * @return (result, qeqVars) result = the predicate, qeqVars = x,y,z…
   */
  private def removeQeq(env: Environment, pred: RichTerm, vars: Traversable[QVariable]) = {
    var qeqVars : Option[ListSet[QVariable]] = None
    val simpleQeq = new SimpleQeq(env)
    def replace(term: Term) : Term = term match {
      case Isabelle.Inf(t1,t2) => Isabelle.inf(replace(t1), replace(t2))
      case `simpleQeq`(qeqVars2) =>
        logger.debug(s"qeqVars = ${qeqVars.map(varsToString)}")
        if (qeqVars.isEmpty) {
          qeqVars = Some(qeqVars2)
          Isabelle.predicate_top
        } else if (qeqVars.get == qeqVars2)
          Isabelle.predicate_top
        else term
      case term => term
    }

    val result = replace(pred.isabelleTerm)
    val resultVars = qeqVars.getOrElse {
      throw UserException(s"Could not find a quantum equality involving ${varsToString(vars)}")
    }
    (RichTerm(Isabelle.predicateT, result), resultVars)
  }
}
