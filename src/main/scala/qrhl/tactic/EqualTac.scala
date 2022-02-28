package qrhl.tactic

import java.io.PrintWriter
import org.log4s
import qrhl._
import qrhl.isabellex.{IsabelleX, RichTerm}
import qrhl.logic.Variable.varsToString
import qrhl.logic._
import qrhl.tactic.EqualTac._
import IsabelleX.{globalIsabelle => GIsabelle}
import GIsabelle.{Ops, QuantumEqualityFull}
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.{Free, Term}
import hashedcomputation.{Hash, HashTag, Hashable}

import scala.collection.immutable.ListSet
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.util.control.{Breaks, ControlThrowable}

// Implicits
import scala.concurrent.ExecutionContext.Implicits.global
import GIsabelle.isabelleControl
import de.unruh.isabelle.pure.Implicits._
import de.unruh.isabelle.mlvalue.Implicits._

import hashedcomputation.Implicits._

case class EqualTac(exclude: List[String], in: List[Variable], mid: List[Variable], out: List[Variable], amount:Int=1) extends WpBothStyleTac(leftAmount=amount, rightAmount=amount) {

  override def toString: String = {
    def stringIfNonEmpty(keyword: String, list: List[Any]) : String = list match {
      case Nil => ""
      case _ => s" $keyword ${list.mkString(", ")}"
    }
    s"equal $amount" + stringIfNonEmpty("exclude",exclude) + stringIfNonEmpty("in",in) +
      stringIfNonEmpty("mid",mid) + stringIfNonEmpty("out",out)
  }

  override def hash: Hash[EqualTac.this.type] =
    HashTag()(Hashable.hash(exclude), Hashable.hash(in), Hashable.hash(mid), Hashable.hash(out), Hashable.hash(amount))

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

/*  private def checkConditions(env: Environment, varUse: VariableUse, mismatchesFree: Set[Variable],
                      isInfinite: Variable => Boolean,
                      in: Set[Variable], out: Set[Variable], mid: Set[Variable]): Unit = {
  }*/

  override def getWP(state: State, left: Statement, right: Statement, post: RichTerm)(implicit output: PrintWriter): (RichTerm, List[Subgoal]) = {
    val env = state.environment
    val isabelle = state.isabelle

    import output.println

    // ==== Get the context and the mismatches

    val (context, mismatches) = diff(left,right)

    println()
    println("tl;dr: Below is the detailed reasoning of the equal-tactic that lead to the current subgoals / the current error.")

    println()
    println(s"You have requested to prove the equivalence of the last $amount lines of the left/right program.")
    println(s"""I have identified that the following is the common part of those lines (called the "context" in the following):""")
    println(s"  $context")

    println()
    if (mismatches.isEmpty)
      println("In this specific case, there are no differences between the two sides.")
    if (mismatches.nonEmpty) {
      println(s"Here occurrences of 'call @0', 'call @1', ... stand for places where the left/right program are different.")
      println(s"In those places, the left/right program have the following pairs of program fragments:")
      for (((l,r),i) <- mismatches.zipWithIndex)
        println(s"  @$i: $l   -vs-   $r")
      println("We call those pairs the \"mismatches\".")
    }

    println("Each difference will lead to an additional subgoal in which you need to prove that the invariant is preserved.")
    println("Sometimes, you may want to add additional fragments on the two sides that should be treated as if they are not equal (i.e., produce a separate subgoal) because those fragments will not be included in the computation of the free variables and related sets.")
    println("If you wish this, use the \"exclude\" option to the equal-tactic (see the manual).")
    if (mismatches.isEmpty) println("We refer to these differences (nonexisting in the present case) in the following as \"mismatches\".")
    println()

    val varUse = context.variableUse(env)

    val mismatchesVarUse = mismatches map { case (l,r) => (l.variableUse(env), r.variableUse(env)) }
    val mismatchesFree = mutable.HashSet[Variable]()
    for ((l,r) <- mismatchesVarUse) {
      mismatchesFree ++= l.freeVariables
      mismatchesFree ++= r.freeVariables
    }

    println("The context contains the following variables:")
    output.println(varUse)

    println()
    println("Here e.g. \"Free ⊆ ...\" means that ... is an upper bound on the set of free variables (i.e., there might be less free variables), and \"Overwritten ⊇ ...\" means that ... is an upper bound on the set of overwritten variables.")
    println("In the following, the free, written, overwritten, inner, and covered variables of the context are relevant.")
    println("In a nutshell, free variables are variables that are not hidden by a local-statement, written ones are written to (any access to a quantum variables is considered write access), overwritten ones are initialized by the program, inner variables are local variables visible from a hole of the context, covered variables are those that are declared local over every hole.")
    println("See https://arxiv.org/pdf/2007.14155.pdf, Section 3.3 for precise definitions.")

    println()
    println("We will try to apply the Adversary rule (https://arxiv.org/pdf/2007.14155.pdf, Section 9).")
    println("This rule is too complex to write out in detail, but in a nutshell, it proves the following:")
    println()
    println("   {R ⊓ ≡Vmid} left ~ right {R ⊓ ≡Vmid}")
    println("                           for each mismatch (left,right)")
    println("   ... many conditions about variables ...")
    println("-----------------------------------------------------------------------------")
    println(" {R ⊓ ≡Vin} context[left mismatches] ~ context[right mismatches] {R ⊓ ≡Vout}")
    println()
    println("Here R is some predicate, and Vin, Vout, Vmid are sets of variables.")
    println("And ≡V means that all variables in V are equal on both sides. (E.g., V={x,q,r} for classical x, quantum q,r is short for Cla[x1=x2] ⊓ ⟦q1,r1⟧ ≡q ⟦q2,r2⟧.)")

    println()
    println("So what we need to do is to instantiate R and Vin, Vout, Vmid in such a way that (R ⊓ ≡Vout) implies (≤) the current postcondition.")
    println(s"Then (combining the Adversary rule this with the Seq rule) we get one subgoal for each mismatch (of the form {R ⊓ ≡Vmid} left ~ right {R ⊓ ≡Vmid}), and one subgoal that consists everything before the last $amount lines, with the new postcondition {R ⊓ ≡Vin}.")

    // ==== Choose in/out/mid variables

    val in = mutable.LinkedHashSet(this.in:_*)
    val mid = mutable.LinkedHashSet(this.mid:_*)
    val out = mutable.LinkedHashSet(this.out:_*)

    def printVars(): Unit =
      println(s"Vin = ${varsToString(in)}, Vout = ${varsToString(out)}, Vmid = ${varsToString(mid)}")

    println("Initially we pick Vin, Vout, Vmid to be empty (unless differently specified in invocation of the equal-tactic with the in/out/mid parameters, see the manual).")
    println("That is, we have the following sets:")
    printVars()

    println("We will now add more variables to those sets as required by the many conditions of the Adversary tactic until they are satisfied or we get stuck.")
    println("You can influence this process by specifying the sets Vin, Vout, Vmid using the in/out/mid parameters.")

    // Classical variables that we remove from the postcondition
    // This will be done at the end in one go
    val classicalsRemovedFromPost = mutable.LinkedHashSet[CVariable]()
    // Quantum variables that we removed from the postcondition
    // The postcondition will be updated right away
    var removedQeq : ListSet[QVariable] = null
    // Quantum variables that we do not want to occur in the postcondition
    // We remove them right away anyway, but there is a possibility that some occur in the postcondition that we do not "see"
    // So we keep track here
    var forbiddenQuantumInPostcondition = mutable.HashSet[QVariable]()

    var updated = false
    def add(msg: => String, extraIn:Set[Variable]=Set.empty, extraMid:Set[Variable]=Set.empty,
            extraOut:Set[Variable]=Set.empty): Unit = {
      val extraIn2 = extraIn -- in
      val extraOut2 = extraOut -- out
      val extraMid2 = extraMid -- mid
      if (msg != null && (extraIn2.nonEmpty || extraMid2.nonEmpty || extraOut2.nonEmpty)) {
        println("---")
        println(msg)
      }

      if (extraIn2.nonEmpty) {
        println(s"So we add to Vin:  ${varsToString(extraIn2)}")
        updated = true
        in ++= extraIn2
        println(s"  Vin = ${varsToString(in)}")
      }
      if (extraMid2.nonEmpty) {
        println(s"So we add to Vmid: ${varsToString(extraMid2)}")
        updated = true
        mid ++= extraMid2
        println(s"  Vmid = ${varsToString(mid)}")
      }
      if (extraOut2.nonEmpty) {
        if (removedQeq != null) {
          val quantum = Variable.quantum(extraOut2)
          println(s"So we add to Vout: ${varsToString(extraOut2)}")
          if (!quantum.toSet.subsetOf(removedQeq)) {
            println(
              s"""
                 |PROBLEM:
                 |We have already removed a quantum equality involving the variables ${varsToString(removedQeq)} from R at some earlier point.
                 |This was justified by the fact that the "R ⊓ ≡Vout" with or without this quantum equality is the same.
                 |This would not be true if we now added more variables to Vout.
                 |So we are stuck and give up.  😞""".stripMargin)
            throw UserException(s"Trying to add ${varsToString(quantum)} to Vout, but we already committed on removing " +
              s"quantum equality for ${varsToString(removedQeq)} from the postcondition")
          }
        }
        updated = true
        out ++= extraOut2
        println(s"  Vout = ${varsToString(out)}")
      }
    }

    var postcondition = post

    def postconditionString(postcondition : RichTerm = postcondition) : String =
      if (classicalsRemovedFromPost.isEmpty) postcondition.toString
      else s"$postcondition (with variables ${varsToString(classicalsRemovedFromPost)} removed)"

    println("We also need to choose the predicate R so that (R ⊓ ≡Vout) implies the current postcondition.")
    println("We tentatively choose R to be the whole postcondition (we may change this later to avoid variable conflicts).")
    println()
    println(s"  R := ${postconditionString()}")
    println()

    // Free variables of postcondition, with variables in
    val postconditionVariables: mutable.Set[Variable] =
      mutable.HashSet(post.variables(env, deindex=true).program.toSeq :_*)

    /** vars: non-indexed vars */
    def removeFromPost(msg: => String, vars: Set[Variable]): Unit = {
      // variables that actually need removing
      val vars2 = vars & postconditionVariables
      val quantum = Variable.quantum(vars2)
      val classical = Variable.classical(vars2)
      forbiddenQuantumInPostcondition ++= quantum

      logger.debug(s"removeFromPost ${msg}, ${varsToString(vars)}")

      if (msg != null && vars2.nonEmpty) {
        println("---")
        println(msg)
      }

      if (classical.nonEmpty) {
        updated = true
        classicalsRemovedFromPost ++= classical
        postconditionVariables --= classical
        println(
          s"""We have to remove the classical variables ${varsToString(classical)} from R.
             |We will do this later (in a way that ensures that the new R implies the old R).
             |For now, we just remember that we want to remove those variables.
             |  R = ${postconditionString()}""".stripMargin)
      }

      if (quantum.nonEmpty) {
        updated = true

        println(
          s"""To remove ${varsToString(quantum)}, we try to do so by finding a quantum equality involving those variables and removing it from R.
             |(In such a way that "R ⊓ ≡Vout" implies the original postcondition.)""".stripMargin)


        if (removedQeq != null) {
          println(s"""
             |PROBLEM:
             |However, we have already removed a quantum equality involving the variables ${varsToString(removedQeq)} from R at some earlier point.
             |We cannot do this twice because it would mean two different
             |This would not be true if we now added more variables to Vout.
             |So we are stuck and give up. 😞""".stripMargin)
          throw UserException(s"Cannot remove quantum variables because we already removed one quantum equality from postcondition")
        }

        val (newPostcondition, newRemovedQeq, newRemovedQeqTerm) = EqualTac.removeQeq(env, postcondition, quantum).getOrElse {
            println(s"""
               |PROBLEM:
               |No such quantum equality was found.
               |We have no way to remove the quantum variables from the postcondition.
               |We give up. 😞""".stripMargin)
            throw UserException(s"Could not find a quantum equality involving ${varsToString(quantum)}")
        }

        println(
          s"""To remove ${varsToString(quantum)}, we remove "$newRemovedQeqTerm" from the predicate R,
             |and we update the set Vout to contain the variables in that quantum equality (and no other quantum variables):
             |  R := ${postconditionString(newPostcondition)}
             |  quantum(Vout) := ${varsToString(newRemovedQeq)}
             |Note that (R ⊓ ≡Vout) then implies the original postcondition.
             |""".stripMargin)

        if (!Variable.quantum(out).toSet.subsetOf(newRemovedQeq)) {
          println(
            s"""
               |PROBLEM:
               |We notice that we had "quantum(Vout) = ${varsToString(out.filter(_.isQuantum))}" before this step.
               |This means that we are removing variables from Vout. (Namely ${varsToString(newRemovedQeq.removedAll(Variable.quantum(out)))})
               |This would lead to an infinite loop of removing/readding, or violate the constraints you gave as a parameter to the equal-tactic.
               |Therefore we give up at this point. 😞""".stripMargin)
          throw UserException(s"Couldn't remove variables ${varsToString(quantum)} from postcondition because this means removing the $newRemovedQeqTerm, but that would be incompatible with the choice of Vout")
        }
        postcondition = newPostcondition
        removedQeq = newRemovedQeq
        postconditionVariables.clear()
        postconditionVariables ++= postcondition.variables(env, deindex = true).program
        postconditionVariables --= classicalsRemovedFromPost

        out ++= removedQeq
        println(s"We now have: Vout = ${varsToString(out)}")
      }
    }

    val isInfiniteHashtable = mutable.HashMap[Variable, Boolean]()
    def isInfinite(v: Variable): Boolean =
      isInfiniteHashtable.getOrElseUpdate(v, {
        val result =
          Ops.isInfinite_op(MLValue((isabelle.context, v.valueTyp))).retrieveNow
        logger.debug(s"Checking infiniteness of $v: $result")
        result
      })

    // Ensuring all conditions except those referring to qRHL subgoals

    // Removing quantum equality involving variables in out.
    // Not an explicit condition for applying the adversary rule, but since we will later add a quantum equality with
    // the variables in out anyway, this won't hurt
    if (out.exists(_.isQuantum)) {
      val qvars = out.filter(_.isQuantum).toSet
      removeFromPost(
        s"""You have explicitly specified Vout = ${varsToString(out)} which contains the quantum variables ${varsToString(qvars)}.
           |This means the postcondition should be split into some predicate R, and some quantum equality containing those quantum variables.
           |""".stripMargin,
        qvars)
    }
    // It is conceivable that there is more than one quantum equality with those variables.
    // In that case we might remove the wrong one. However, this rare (or impossible?) case
    // can be remedied by explicitly specifying the quantum variables in out


    println("\nWe now go through the various requirements of the adversary rule and add variables to Vin, Vout, Vmid as needed.\n")

    //    assumes inner_Vmid: "inner C ⊆ Vmid"
    add(
      s"""We need "inner(context) ⊆ Vmid" to hold. Currently:
         |  Vmid = ${varsToString(mid)}
         |  inner(context) = ${varsToString(varUse.inner)}
         |So we add the missing variables to Vmid.""".stripMargin,
      extraMid = varUse.inner)

    //    assumes C_Vmid: "fv C ⊆ Vmid"
    add(
      s"""We need "fv(context) ⊆ Vmid" to hold. Currently:
         |  Vmid = ${varsToString(mid)}
         |  fv(context) = ${varsToString(varUse.freeVariables)}
         |So we add the missing variables to Vmid.""".stripMargin,
      extraMid = varUse.freeVariables)

    //    assumes C_Vin_overwr: "fv C ⊆ Vin ∪ overwr C"
    add(
      s"""We need "fv(context) ⊆ Vin ∪ overwritten(context)" to hold. Currently:
        |  fv(context) = ${varsToString(varUse.freeVariables)}
        |  Vin = ${varsToString(in)}
        |  overwritten(context) = ${varUse.overwritten}
        |So we add the missing variables to Vin.""".stripMargin,
      extraIn = varUse.freeVariables -- varUse.overwritten)

    //    assumes C_Vout: "quantum' (fv C) ⊆ Vout"
    add(
      s"""We need "quantum(fv(context)) ⊆ Vout" to hold. Currently:
        |  quantum(fv(context)) = ${varsToString(varUse.freeVariables.filter(_.isQuantum))}
        |  Vout = ${varsToString(out)}
        |So we add the missing variables to Vout.""".stripMargin,
      extraOut = varUse.freeVariables.filter(_.isQuantum))

    // Here we loop until nothing changes any more because adding variables to satisfy one condition may make another wrong again
    do {
      updated = false


      //    assumes Vout_Vmid: "Vout ⊆ Vmid"
      add(
        s"""We need "Vout ⊆ Vmid" to hold. Currently:
           |  Vout = ${varsToString(out)}
           |  Vmid = ${varsToString(mid)}
           |So we add the missing variables to Vmid.""".stripMargin,
        extraMid = out.toSet)

      //    assumes Vout_overwr_Vin: "Vout - overwr C ⊆ Vin"
      add(
        s"""We need "Vout - overwritten(context) ⊆ Vin" to hold. Currently:
           |  Vout = ${varsToString(out)}
           |  overwritten(context) = ${varsToString(varUse.overwritten)}
           |  Vin = ${varsToString(in)}
           |So we add the missing variables to Vin.""".stripMargin,
        extraIn = (out -- varUse.overwritten).toSet)

      //    assumes Vin_Vout_overwr: "quantum' Vin ⊆ Vout ∪ overwr C"
      add(
        s"""We need "quantum(Vin) ⊆ Vout ∪ overwritten(context)" to hold. Currently:
           |  quantum(Vin) = ${varsToString(in.toSet.filter(_.isQuantum))}
           |  Vout = ${varsToString(out)}
           |  overwritten(context) = ${varsToString(varUse.overwritten)}
           |So we add the missing variables to Vout.""".stripMargin,
        extraOut = in.toSet.filter(_.isQuantum) -- varUse.overwritten)

      //    assumes Vmid_s_Vin_covered: "⋀i. Vmid ∩ (fv (s i) ∪ fv (s' i)) ⊆ Vin ∪ covered C ∪ classical' (overwr (s i) ∩ overwr (s' i))"
      for (((l,r), i) <- mismatchesVarUse.zipWithIndex) {
          add(
            s"""We need "Vmid ∩ (fv(left) ∪ fv(right)) ⊆ Vin ∪ covered(context) ∪ classical(overwritten(left) ∩ overwr(right))" to hold where left/right is mismatch @$i. Currently:
               |  left = ${mismatches(i)._1}
               |  right = ${mismatches(i)._2}
               |  Vmid = ${varsToString(mid)}
               |  fv(left) = ${varsToString(l.freeVariables)}
               |  fv(right) = ${varsToString(r.freeVariables)}
               |  Vin = ${varsToString(in)}
               |  covered(context) = ${varsToString(varUse.covered)}
               |  classical(overwritten(left)) = ${varsToString(l.overwritten.filter(_.isClassical))}
               |  classical(overwritten(right)) = ${varsToString(r.overwritten.filter(_.isClassical))}
               |So we add the missing variables to Vin.""".stripMargin,
            extraIn = (mid.toSet & (l.freeVariables ++ r.freeVariables)) -- varUse.covered -- (l.overwritten & r.overwritten).filter(_.isClassical))
      }

      //    assumes Vmid_s_Vout_covered: "⋀i. quantum' Vmid ∩ (fv (s i) ∪ fv (s' i)) ⊆ Vout ∪ covered C"
      for (((l,r),i) <- mismatchesVarUse.zipWithIndex) {
          add(
            s"""We need "quantum(Vmid) ∩ (fv(left) ∪ fv(right)) ⊆ Vout ∪ covered(context)" to hold where left/right is mismatch @$i. Currently:
               |  left = ${mismatches(i)._1}
               |  right = ${mismatches(i)._2}
               |  quantum(Vmid) = ${varsToString(mid.filter(_.isQuantum))}
               |  fv(left) = ${varsToString(l.freeVariables)}
               |  fv(right) = ${varsToString(r.freeVariables)}
               |  Vout = ${varsToString(out)}
               |  covered(context) = ${varsToString(varUse.covered)}
               |So we add the missing variables to Vout.""".stripMargin,
            extraOut = (mid.toSet.filter(_.isClassical) & (l.freeVariables & r.freeVariables)) -- varUse.covered)
      }

      //    assumes Vout_Vin_R: "(Vout - Vin) ∩ Rv = {}"
      removeFromPost(
        s"""We need "(Vout - Vin) ∩ fv(R) = ∅" to hold. Currently:
           |  R = ${postconditionString()}
           |  Vout = ${varsToString(out)}
           |  Vin = ${varsToString(in)}
           |  fv(R) = ${varsToString(postconditionVariables)}
           |So we remove the superfluous variables from R.""".stripMargin,
        (out -- in).toSet)

      //    assumes Vin_Vout_R: "quantum' (Vin - Vout) ∩ Rv = {}"
      removeFromPost(
        s"""We need "quantum(Vin - Vout) ∩ fv(R) = ∅" to hold. Currently:
           |  R = ${postconditionString()}
           |  quantum(Vin) = ${varsToString(in)}
           |  quantum(Vout) = ${varsToString(out)}
           |  fv(R) = ${varsToString(postconditionVariables)}
           |So we remove the superfluous variables from R.""".stripMargin,
        (in.filter(_.isQuantum) -- out).toSet)

      //    assumes R_inner: "Rv ∩ inner C = {}"
      removeFromPost(
        s"""We need "fv(R) ∩ inner(context) = ∅" to hold. Currently:
           |  R = ${postconditionString()}
           |  fv(R) = ${varsToString(postconditionVariables)}
           |  inner(context) = ${varsToString(varUse.inner)}
           |So we remove the superfluous variables from R.""".stripMargin,
        varUse.inner)

      //    assumes R_written: "Rv ∩ written C = ∅"
      removeFromPost(
        s"""We need "fv(R) ∩ written(context) = ∅" to hold. Currently:
           |  R = ${postconditionString()}
           |  fv(R) = ${varsToString(postconditionVariables)}
           |  written(context) = ${varsToString(varUse.written)}
           |So we remove the superfluous variables from R.""".stripMargin,
        varUse.written)

      //    assumes aux_Vmid: "aux ∈ Vmid"
      //    assumes aux_si: "⋀i. aux ∉ fv (s i)"
      //    assumes aux_s'i: "⋀i. aux ∉ fv (s' i)"
      //    assumes inf_aux: "infinite_var aux" and quant_aux: "is_quantum aux"
      // We construct the set of all variables in mid that satisfy the conditions for aux
      // We filter "isInfinite" last because this is the slowest part
      if (!mid.exists( v => v.isQuantum && !mismatchesFree.contains(v) && isInfinite(v))) {
        println(
          s"""---
             |We need Vmid to contain some quantum variable of infinite type (e.g., type nat, string, infinite, bit list, …) that is not contained in any of the mismatches.
             |  fv(all mismatches) = ${varsToString(mismatchesFree)}""".stripMargin)
        Breaks.breakable {
          for (v <- env.qVariables.values)
            if (!mismatchesFree.contains(v) && isInfinite(v)) {
              println(
                s"""We arbitrarily choose ${v.name} for that purpose. If you wish to use another one, add it to Vmid via the mid-parameter of the equal-tactic.
                   |Also make sure the Isabelle simplifier can prove "infinite (UNIV::typ)" where typ is the type of that variable, otherwise I will not recognize it as infinite.""".stripMargin)
              add(msg = null, extraMid = Set(v))
              Breaks.break()
            }
          println(
            """We could not find any quantum variable to use for this purpose.
              |Fix: declare an arbitrary additional variable using "quantum var : variable_name : infinite.
              |If a suitable variable already exists and I don't find it, make sure the Isabelle simplifier can prove "infinite (UNIV::typ)" where typ is the type of that variable."""".stripMargin)
          throw UserException(
            s"""Need an infinite quantum variable in Vmid that does not occur in any of the mismatches.""".stripMargin)
        }
      }


      // If removedQeq == null, we do not know yet what the quantum variables of the postcondition will be.
      // (They could still become less) So we hold off adding quantum variables to `in` until things have stabilized (!updated)
      if (removedQeq!=null || !updated) {
        //    assumes C_Vin_R: "fv C ∩ Rv ⊆ Vin"
        add(
          s"""We need "fv(context) ∩ fv(R) ⊆ Vin" to hold. Currently:
             |  R = ${postconditionString()}
             |  fv(context) = ${varsToString(varUse.freeVariables)}
             |  fv(R) = ${varsToString(postconditionVariables)}
             |  Vin = ${varsToString(in)}
             |So we add the missing variables to Vin.""".stripMargin,
          extraIn = varUse.freeVariables & postconditionVariables)

        //    assumes Vmid_R_Vin_covered: "Vmid ∩ Rv ⊆ Vin ∪ covered C"
        add(
          s"""We need "Vmid ∩ fv(R) ⊆ Vin ∪ covered(context)" to hold. Currently:
             |  R = ${postconditionString()}
             |  Vmid = ${varsToString(mid)}
             |  fv(R) = ${varsToString(postconditionVariables)}
             |  Vin = ${varsToString(in)}
             |  covered(context) = ${varsToString(varUse.covered)}
             |So we add the missing variables to Vin.""".stripMargin,
          extraIn = MaybeAllSet.subtract(mid.toSet & postconditionVariables, varUse.covered))

        //    assumes Vmid_R_Vout_covered: "quantum' (Vmid ∩ Rv) ⊆ Vout ∪ covered C"
        add(
          s"""We need "quantum(Vmid ∩ fv(R)) ⊆ Vout ∪ covered(context)" to hold. Currently:
             |  R = ${postconditionString()}
             |  quantum(Vmid) = ${varsToString(mid.filter(_.isQuantum))}
             |  quantum(fv(R)) = ${varsToString(postconditionVariables.filter(_.isQuantum))}
             |  Vout = ${varsToString(out)}
             |  covered(context) = ${varsToString(varUse.covered)}
             |So we add the missing variables to Vout.""".stripMargin,
          extraOut = MaybeAllSet.subtract(mid.toSet.filter(_.isQuantum) & postconditionVariables, varUse.covered))
      } else {
        //    assumes C_Vin_R: "fv C ∩ Rv ⊆ Vin"
        add(
          s"""We need "fv(context) ∩ fv(R) ⊆ Vin" to hold. Currently:
             |  R = ${postconditionString()}
             |  fv(context) = ${varsToString(varUse.freeVariables)}
             |  fv(R) = ${varsToString(postconditionVariables)}
             |  Vin = ${varsToString(in)}
             |So we add the missing variables to Vout. (For now, only the classical ones. We do the quantum ones later.)""".stripMargin,
          extraIn = varUse.freeVariables.filter(_.isClassical) & postconditionVariables)

        //    assumes Vmid_R_Vin_covered: "Vmid ∩ Rv ⊆ Vin ∪ covered C"
        add(
          s"""We need "Vmid ∩ fv(R) ⊆ Vin ∪ covered(C)" to hold. Currently:
             |  R = ${postconditionString()}
             |  quantum(Vmid) = ${varsToString(mid.filter(_.isQuantum))}
             |  quantum(fv(R)) = ${varsToString(postconditionVariables.filter(_.isQuantum))}
             |  Vin = ${varsToString(in)}
             |  covered(context) = ${varsToString(varUse.covered)}
             |So we add the missing variables to Vin. (For now, only the classical ones. We do the quantum ones later.)""".stripMargin,
          extraIn = MaybeAllSet.subtract(mid.toSet.filter(_.isClassical) & postconditionVariables, varUse.covered))
      }

    } while (updated)



    // Adding some additional classical variables to out. This will make the call to removeClassicals produce a better postcondition
    // We need to make sure that these conditions stay satisfied:
    //    assumes Vout_overwr_Vin: "Vout - overwr C ⊆ Vin"
    //    assumes Vout_Vmid: "Vout ⊆ Vmid"
    //    assumes Vout_Vin_R: "(Vout - Vin) ∩ Rv = ∅"
    //    assumes Vin_Vout_R: "quantum' (Vin - Vout) ∩ Rv = ∅"
    add(
      """We try to add as many additional classical variables to Vout as we can without breaking any assumptions of the Adversary rule.
        |This is not required for applying the Adversary rule, but it will lead to a stronger postcondition in the step "Recall had to remove the classical variables…" below.
        |(We do not do the same with quantum variables because adding quantum variables to a quantum equality leads does not make the equality stronger but incomparable.)""".stripMargin,
      extraOut = mid.toSet & (in ++ varUse.overwritten) & classicalsRemovedFromPost.toSet)


    // It is possible that we did not remove any quantum equality yet.
    // So we try to remove the quantum equality containing the quantum variables in out
    // This may fail if there is only a quantum equality with the wrong variables, then we just skip this.
    try {
      // TODO don't use removeFromPost for this (confusing explanations result)
      removeFromPost(
        """TODO: explanation here not clear!
          |trying to get rid of quantum equality in postcondition""".stripMargin,
        out.filter(_.isQuantum).toSet)
    } catch {
      case _ : UserException =>
    }

    printVars()
    logger.debug(s"Postcondition: ${postcondition}; without ${varsToString(classicalsRemovedFromPost)}")

    if (classicalsRemovedFromPost.nonEmpty) {
      val newPostcondition = removeClassicals(env, postcondition, classicalsRemovedFromPost.toSet, Variable.classical(out).toSet)
      println(
        s"""Recall had to remove the classical variables ${varsToString(classicalsRemovedFromPost)} from the postcondition. I.e., we want:
           |  R = ${postconditionString()}
           |We need to do so in a way such that "R_new ⊓ ≡Vout" implies "R_old ⊓ ≡Vout". (Note: Vout = ${varsToString(out)}.)
           |There are many ways to do this, e.g., simply "all-quantifying" over the values of ${varsToString(classicalsRemovedFromPost)}.
           |(We put "all-quantifying" in quotes because technically speaking, we use the intersection of subspaces instead of an all-quantifies, but for the intuition we shall think of "all-quantifying".)
           |One way that works particularly well is to "all-quantify" R over the those values of the variables so that the variables in Vout are equal on the left and right side.
           |Concretely, this leads to the following new postcondition:
           |  R = $newPostcondition
           |Then "R_new ⊓ ≡Vout" implies "R_old ⊓ ≡Vout".""".stripMargin)
      postcondition = newPostcondition
    }

    println(
      s"""
        |---
        |We have now instantiated the sets Vin, Vout, Vmid as well as the predicate R in a way that satisfies the conditions of the Adversary rule:
        |  Vin = ${varsToString(in)}
        |  Vout = ${varsToString(out)}
        |  Vmid = ${varsToString(mid)}
        |  R = $postcondition
        |(Note: logically, the order of the variables in those sets does not matter.
        |However, in the quantum equalities produced in the final subgoals, the variables in the quantum equalities will be in that order.
        |If you prefer a different order, add the variables in the desired order an in-/out-/mid-parameters to the equal-tactic.)
        |
        |The subgoals created by the equal tactic will be:
        |* One subgoal that shows that R does not contain any of the variables ${varsToString(forbiddenQuantumInPostcondition)}.
        |  (This should already hold and can usually be proven by simp!. We have it as an explicit subgoal because it is possible that the equal tactic incorrectly analyzed the free quantum variables of R.)
        |* One subgoal "{R ⊓ ≡Vmid} left ~ right {R ⊓ ≡Vmid}" for each mismatch left/right (there are ${mismatches.length} of them).
        |* One subgoal "{original_pre} before_left ~ before_right {R ⊓ ≡Vin}"
        |  where "original_pre" is the precondition of the goal we are operating on,
        |  and "before_left"/"before_right" are programs without the last $amount lines.
        |""".stripMargin)

    val colocality = RichTerm(Ops.colocalityOp(postcondition.isabelleTerm,
      for (v <- forbiddenQuantumInPostcondition.toList;
           v12 <- Seq(v.index1, v.index2))
        yield (v12.variableName, v12.valueTyp)).retrieveNow)

    logger.debug(s"Colocality: $colocality")

    val sort_reference = (if (removedQeq==null) Nil else removedQeq.toList) ++ this.in ++ this.out ++ this.mid
    def sort(list: Seq[Variable], reference: Seq[Variable]) = {
      val ref = reference.toList ++ sort_reference
      list.sortBy(ref.indexOf)
    }

    val Amid = makePredicate(sort(mid.toSeq,this.mid),postcondition)
    val Ain = makePredicate(sort(in.toSeq,this.in),postcondition)

    // For each element (l,e) of mismatches, mismatchGoals contains a goal of the form {Amid}l~r{Amid}
    //    assumes qrhl_s: "⋀i. qRHL (R ⊓ Eq Vmid) (s i) (s' i) (R ⊓ Eq Vmid)"
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
      if (quantum.isEmpty) GIsabelle.predicate_top
      else {
        val left = VarTerm.isabelleTerm(VarTerm.varlist(quantum.map(_.index1).toSeq:_*))
        val right = VarTerm.isabelleTerm(VarTerm.varlist(quantum.map(_.index2).toSeq:_*))
        GIsabelle.quantum_equality(left, right)
      }

    val ceq : Term =
      if (classical.isEmpty) GIsabelle.True_const
      else {
        val eqs = classical.map { v => GIsabelle.mk_eq(v.index1.valueTerm, v.index2.valueTerm) }
        GIsabelle.conj(eqs.toSeq :_*)
      }

    val newPred = GIsabelle.infOptimized(predicate.isabelleTerm, GIsabelle.classical_subspace_optimized(ceq), qeq)
    RichTerm(GIsabelle.predicateT, newPred)
  }

  private val logger = log4s.getLogger
//  private case class FixableConditionException(msg: String, extraIn:Traversable[Variable]=Nil,
//                                               extraMid:Traversable[Variable]=Nil,
//                                               extraOut:Traversable[Variable]=Nil) extends Exception {
//    assert(extraIn.nonEmpty || extraMid.nonEmpty || extraOut.nonEmpty)
//  }
//  private case class UnfixableConditionException(msg: String) extends Exception


  class SimpleQeq(env: Environment) {
    private object trySwapped extends ControlThrowable
    private object noMatch extends ControlThrowable

    def unapply(arg: Term): Option[ListSet[QVariable]] = arg match {
      case QuantumEqualityFull(GIsabelle.IdOp(),q,GIsabelle.IdOp(),r) =>
        val result = ListBuffer[QVariable]()

        def parse(vt1: Term, vt2: Term): Unit = (vt1, vt2) match {
          case (GIsabelle.Variable_Unit(), GIsabelle.Variable_Unit()) =>
          case (GIsabelle.Variable_Singleton(Free(Variable.Indexed(name1, left1), typ1)),
                GIsabelle.Variable_Singleton(Free(Variable.Indexed(name2, left2), typ2))) =>
            if (name1 != name2) throw noMatch
            val v = env.qVariables.getOrElse(name1, throw noMatch)
            if (v.variableTyp != typ1) throw noMatch
            if (v.variableTyp != typ2) throw noMatch
            if (!left1 || left2)
              throw trySwapped
            result += v
          case (GIsabelle.Variable_Concat(vt1a, vt1b), GIsabelle.Variable_Concat(vt2a, vt2b)) =>
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

        val resultSet = result.to(ListSet)
        if (resultSet.size != result.size)
          throw UserException(s"Encountered a quantum equality with repreated variables: $arg")
        Some(resultSet)
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
  private def removeQeq(env: Environment, pred: RichTerm, vars: Traversable[QVariable]): Option[(RichTerm, ListSet[QVariable], RichTerm)] = {
    var qeqVars : Option[ListSet[QVariable]] = None
    var replacedQeq : Term = null
    val simpleQeq = new SimpleQeq(env)
    def replace(term: Term) : Term = term match {
      case GIsabelle.Inf(t1,t2) => GIsabelle.infOptimized(replace(t1), replace(t2))
      case `simpleQeq`(qeqVars2) =>
        logger.debug(s"qeqVars = ${qeqVars.map(varsToString)}")
        if (qeqVars.isEmpty) {
          qeqVars = Some(qeqVars2)
          replacedQeq = term
          GIsabelle.predicate_top
        } else if (qeqVars.get == qeqVars2)
          GIsabelle.predicate_top
        else term
      case term => term
    }

    val result = replace(pred.isabelleTerm)
    qeqVars match {
      case None => None
      case Some(resultVars) => Some((RichTerm(GIsabelle.predicateT, result), resultVars, RichTerm(replacedQeq)))
    }
  }

  private[tactic] /* Should be private but need access in test case */
  def removeClassicals(env: Environment, postcondition: RichTerm, remove: Set[CVariable],
                               equalities: Set[CVariable]): RichTerm = {
    // Classical variables in postcondition (indexed)
    val vars = Variable.classical(postcondition.variables(env).program)
    // x1=x2 for every x in equalities&remove that also appeard in postcondition
    val equalities2 = (equalities & remove).collect(Function.unlift { v =>
      val v1 = v.index1; val v2 = v.index2
      if (vars.contains(v1) && vars.contains(v2))
        Some(GIsabelle.mk_eq(v1.valueTerm,v2.valueTerm))
      else
        None
    })
    logger.debug(s"remove $remove, vars = ${vars}, equalities = ${equalities}, equalities2 = $equalities2")
    val postcondition2 =
      if (equalities2.isEmpty)
        postcondition.isabelleTerm
      else {
        // Cla[~ (x1=x2 /\ ...)] + postcondition (see equalities2 for which x are used)
        GIsabelle.plus(GIsabelle.classical_subspace(GIsabelle.not(GIsabelle.conj(equalities2.toSeq : _*))),
          postcondition.isabelleTerm)
      }
    // All variables in remove (indexed) that occur in vars
    val remove12 = (remove.map(_.index1) ++ remove.map(_.index2)) & vars
    val postcondition3 : Term = remove12.foldLeft(postcondition2) {
      (pc:Term, v:CVariable) =>
        logger.debug(s"${v.name}, ${v.valueTyp}")
        GIsabelle.INF(v.name, v.valueTyp, pc)
    }
    RichTerm(GIsabelle.predicateT, postcondition3)
  }

}
