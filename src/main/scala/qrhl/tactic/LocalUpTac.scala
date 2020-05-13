package qrhl.tactic

import org.log4s
import qrhl.logic.{Assign, Block, CVariable, Call, Environment, IfThenElse, Local, Measurement, QApply, QInit, QVariable, Sample, Statement, VarTerm, Variable, While}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException, Utils}

import scala.collection.immutable.ListSet
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import LocalUpTac.{VarID, _}
import qrhl.isabelle.{Isabelle, RichTerm}

case class LocalUpTac(side: Option[Boolean], varID: VarID) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case AmbientSubgoal(goal) =>
      throw UserException("Expected a qRHL subgoal")
    case QRHLSubgoal(left, right, pre, post, assumptions) =>
      val env = state.environment
//      println(s"*** Possibly unsound (not proven) tactic 'local up' applied.")
      val (left2, id) = if (side.forall(_==true)) up2(env, varID, left) else (left,varID)
      val (right2, id2) = if (side.forall(_==false)) up2(env, id, right) else (right,id)
      if (!id2.consumed)
        throw UserException(s"Not all variables found in $varID")
      List(QRHLSubgoal(left2.toBlock, right2.toBlock, pre, post, assumptions))
  }

  /**  Returns a program that initializes the given variables. */
  def init(classical: Seq[CVariable] = Nil, quantum: Seq[QVariable] = Nil): Block = {
    val statements = new ListBuffer[Statement]()
    for (c <- classical)
      statements.append(Assign(VarTerm.varlist(c), RichTerm(Isabelle.default(c.valueTyp))))
    for (q <- quantum)
      statements.append(QInit(VarTerm.varlist(q), RichTerm(Isabelle.ket(Isabelle.default(q.valueTyp)))))
    Block(statements: _*)
  }

  def up2(env: Environment, id: VarID, statement: Statement): (Statement,VarID) = {
    val (st2, cvars, qvars, id2) = up(env,id,statement)
    (Local.makeIfNeeded(cvars.toSeq,qvars.toSeq,st2), id2)
  }


  import ListSet.empty

  /** Moves the local variable declarations specified by id upwards as far as possible.
   *
   * Upwards movement stops when:
   * * A [[Local]] statement with the same variable occurs (then the variable is merged into that [[Local]])
   * * A variable cannot be moved further (then a suitable [[Local]] statement is inserted)
   *
   * Selected local variables that are not used below their declaration are simply removed.
   *
   * Upwards movements are justified with various lemmas from the paper "Local Variables and Quantum Relational Hoare Logic"
   * as mentioned in the comments inside this function.
   *
   * If upwards movement does not stop, the variable is returned
   *
   * It is guaranteed that Local(cVars,qVars,newStatement) is denotationally equivalent to statement.
   *
   * @return (newStatement,cVars,qVars,id) where newStatement is the rewritten statement, and cVars,qVars are
   *         lists of the variables that moved to the top. id is the updated [[VarID]] (in case some variables have been selected by id for moving).
   **/
  def up(env: Environment, id: VarID, statement: Statement): (Statement,ListSet[CVariable],ListSet[QVariable],VarID) = statement match {
    case _: Assign | _: Sample | _: QInit | _: QApply | _: Measurement | _: Call =>
      /* Here the statement is not changed, so no lemma is needed */
      (statement,empty,empty,id)
    case While(condition, body) =>
      /* Uses the fact (lemma:move.while):

         [[ while (e) { local V; c } ]] = [[ local Vup; while (e) { local Vddown; init Vup; c } ]]
         for Vup := V - fv(e), Vdown := V - Vup = V \cap fv(e)

       */

      val (c, class_V, quant_V, id2) = up(env, id, body)
      /** variables that can move further (Vu).  */
      val class_Vup = class_V.diff(condition.caVariables(env).classical)
      val quant_Vup = quant_V
      /** variables that have to stop here (Vd). */
      val class_Vdown = class_V.intersect(condition.caVariables(env).classical)
      val quant_Vdown = Nil
      // Add "init Vu" in front of c
      val body3 = (init(classical = class_Vup.toSeq, quantum = quant_Vup.toSeq) ++ c.toBlock).unwrapTrivialBlock
      // Put local Vd in front
      val body4 = Local.makeIfNeeded(cvars=class_Vdown.toSeq, qvars=quant_Vdown, body=body3)

      (While(condition, body4.toBlock), class_Vup, quant_Vup, id2)
    case IfThenElse(condition, thenBranch, elseBranch) =>
      /* Uses the fact (lemma:move.if):

        [[ if (e) { local Vthen; cthen } else { local Velse; celse } ]]
        =
        [[ local Vup; if (e) { local Vthendown; cthen } else { local Velsedown; celse } ]]

        Vup := (Vthen + Velse) - (fv(cthen) - Vthen) - (fv(celse) - Velse) - fv(e)
        Vthendown := Vthen - Vup
        Velsedown := Velse - Vup

       */
      val thenVarUse = thenBranch.variableUse(env)
      val elseVarUse = elseBranch.variableUse(env)
      val condVars = condition.caVariables(env).classical

      val (cthen, class_Vthen, quant_Vthen, id2) = up(env, id, thenBranch)
      val (celse, class_Velse, quant_Velse, id3) = up(env, id2, elseBranch)

      val class_Vup = (class_Vthen ++ class_Velse) -- (thenVarUse.classical -- class_Vthen) -- (elseVarUse.classical -- class_Velse) -- condVars
      val quant_Vup = (quant_Vthen ++ quant_Velse) -- (thenVarUse.quantum -- quant_Vthen) -- (elseVarUse.quantum -- quant_Velse)

      val class_Vthendown = class_Vthen -- class_Vup
      val quant_Vthendown = quant_Vthen -- quant_Vup
      val class_Velsedown = class_Velse -- class_Vup
      val quant_Velsedown = quant_Velse -- quant_Vup

      // local Vthendown; cthen
      val thenBody = Local.makeIfNeeded(class_Vthendown.toSeq, quant_Vthendown.toSeq, cthen)
      // local Velsedown; celse
      val elseBody = Local.makeIfNeeded(class_Velsedown.toSeq, quant_Velsedown.toSeq, celse)

      (IfThenElse(condition,thenBody.toBlock,elseBody.toBlock), class_Vup, quant_Vup, id3)
    case Block() => (statement, empty, empty, id)
    case Block(s) =>
      up(env, id, s)
    case Block(statements@_*) =>
      /*

        [[ c := {local V1; c1}; ...; {local Vn; cn} ]]
        =
        [[ local V; c_1'; ...; c_n' ]]

        Here V := (union V_i) - fv(c)
        and c_i' :=  init V_i'; local V_i''; c_i
        where V_i' := V_i \cap V \cap (union_{j<i} V_j)
        and V_i'' := V_i \ V

       */

      logger.debug("Operating on a block")

      // keys = variables that should be moved into the joint Local
      // true = variable has already occurred in the statements processed so far (in the loop below)
      val cCandidates = new mutable.LinkedHashMap[CVariable, Boolean]()
      val qCandidates = new mutable.LinkedHashMap[QVariable, Boolean]()

      var id2 = id
      val statements2 = for (s <- statements) yield {
        val (s2,cVars,qVars,id_) = up(env, id2, s)
        for (c <- cVars) cCandidates(c) = false
        for (q <- qVars) qCandidates(q) = false
        id2 = id_
        (s2,cVars,qVars)
      }

      logger.debug(s"Statements after inner processing: $statements2")
      logger.debug(s"VarID after inner processing: $id2")
      logger.debug(s"Candidates (preliminary): ${cCandidates.keys}; ${qCandidates.keys}")

      // Collect free variables of this block (those cannot be put under a Local)
      val varUse = statement.variableUse(env)

      for (c <- varUse.classical)
        cCandidates.remove(c)
      for (q <- varUse.quantum)
        qCandidates.remove(q)

      logger.debug(s"Candidates (cleaned):     ${cCandidates.keys}; ${qCandidates.keys}")

      val statements3 = new ListBuffer[Statement]

      for ((st, cvars, qvars) <- statements2) {
          val cvarsUp = cvars.filter(cCandidates.contains)
          val cvarsDown = cvars.filterNot(cCandidates.contains)
          val qvarsUp = qvars.filter(qCandidates.contains)
          val qvarsDown = qvars.filterNot(qCandidates.contains)

          val cvarsInit = cvarsUp.filter(cCandidates(_) == true)
          val qvarsInit = qvarsUp.filter(qCandidates(_) == true)

          statements3.append(init(cvarsInit.toSeq, qvarsInit.toSeq).statements: _*)
          for (c <- cvarsUp) cCandidates(c) = true
          for (q <- qvarsUp) qCandidates(q) = true

          statements3.append(Local.makeIfNeeded(cvarsDown.toSeq, qvarsDown.toSeq, st.toBlock).toSeq :_*)
      }

      val resultBlock = Block(statements3: _*)

      (resultBlock, ListSet(cCandidates.keys.toSeq:_*), ListSet(qCandidates.keys.toSeq:_*), id2)
    case Local(cvars, qvars, body) =>
      /* Uses fact:

         [[ local V; c ]] = [[ c ]] if V \cap fv(c) = {}

TODO check, reference lemma, and make sure that we remove unused vars

       */
      // cvars_sel, qvars_sel -- variables that are selected for moving up
      val (cvars_sel, qvars_sel, id2) = id.select(cvars, qvars)
      // cvars_body, qvars_body -- variables that are moving up from the body
      val (body2, cvars_body, qvars_body, id3) = up(env,id2,body.unwrapTrivialBlock)

      // cvars_up, qvars_up -- variables that are supposed to move further up
      // (namely: the ones selected explicitly, and the ones moving up from the body that are not shadowed by this local)
      val cvars_up = ListSet(cvars_sel:_*) ++ (cvars_body -- cvars)
      val qvars_up = ListSet(qvars_sel:_*) ++ (qvars_body -- qvars)

      val cvars_all = ListSet(cvars:_*) ++ cvars_body
      val cvars_keep = cvars_all -- cvars_up
      val qvars_all = ListSet(qvars:_*) ++ qvars_body
      val qvars_keep = qvars_all -- qvars_up

      assert(cvars_keep.intersect(cvars_up).isEmpty)
      assert(qvars_keep.intersect(qvars_up).isEmpty)
      assert(cvars_keep.union(cvars_up) == cvars_all)
      assert(qvars_keep.union(qvars_up) == qvars_all)

      val varUse2 = body2.variableUse(env)
      // Removing variables that do not occur in the body from those that should be propagated upwards
      // (justification: unused local variables can be removed)
      val cvars_up2 = cvars_up.intersect(varUse2.classical)
      val qvars_up2 = qvars_up.intersect(varUse2.quantum)

      logger.debug(s"Local: $statement, $qvars $qvars_keep $qvars_up $qvars_up2")

      val body3 = Local.makeIfNeeded(cvars_keep.toSeq, qvars_keep.toSeq, body2)
      (body3, cvars_up2, qvars_up2, id3)
  }
}

object LocalUpTac {
  private val logger = log4s.getLogger

  sealed trait VarID {
    def consumed : Boolean
    def select(cvars: List[CVariable], qvars: List[QVariable]) : (List[CVariable], List[QVariable], VarID)
  }

  final case object AllVarsConsumed extends VarID {
    override def select(cvars: List[CVariable], qvars: List[QVariable]): (List[CVariable], List[QVariable], VarID) = (cvars,qvars,AllVarsConsumed)
    override def consumed: Boolean = true
  }
  final case object AllVars extends VarID {
    override def select(cvars: List[CVariable], qvars: List[QVariable]): (List[CVariable], List[QVariable], VarID) = (cvars,qvars,AllVarsConsumed)
    override def consumed: Boolean = false
  }

  sealed trait SingleVarID {
    def consumed : Boolean
    def select : (Boolean, SingleVarID)
  }
  final case object AllOccurrences extends SingleVarID {
    override def consumed: Boolean = false
    override def select: (Boolean, SingleVarID) = (true, AllOccurrencesConsumed)
  }
  final case object AllOccurrencesConsumed extends SingleVarID {
    override def consumed: Boolean = true
    override def select: (Boolean, SingleVarID) = (true, AllOccurrencesConsumed)
  }
  final class Occurrences private (occurrences: List[Int]) extends SingleVarID {
    override def consumed: Boolean = occurrences.isEmpty

    override def select: (Boolean, Occurrences) = occurrences match {
      case Nil => (false, this)
      case 1 :: rest => (true, new Occurrences(rest.map(_-1)))
      case rest => (false, new Occurrences(rest.map(_-1)))
    }
  }
  object Occurrences {
    def apply(occurrences: List[Int]): Occurrences = {
      assert (Utils.isSortedUnique(occurrences))
      assert (occurrences.forall(_>0))
      new Occurrences(occurrences)
    }
  }

  final case class IdxVarId(cvars : Map[CVariable, SingleVarID], qvars : Map[QVariable, SingleVarID]) extends VarID {
    override def select(cvars: List[CVariable], qvars: List[QVariable]): (List[CVariable], List[QVariable], VarID) = {
      val selectedCVars = new ListBuffer[CVariable]()
      val selectedQVars = new ListBuffer[QVariable]()

      var cvarsID = this.cvars
      var qvarsID = this.qvars

      for (v <- cvars) {
        cvarsID.get(v) match {
          case None =>
          case Some(svID) =>
            val (selected, svID2) = svID.select
            if (selected) selectedCVars += v
            cvarsID = cvarsID.updated(v, svID2)
        }
      }

      for (v <- qvars) {
        qvarsID.get(v) match {
          case None =>
          case Some(svID) =>
            val (selected, svID2) = svID.select
            if (selected) selectedQVars += v
            qvarsID = qvarsID.updated(v, svID2)
        }
      }

      (selectedCVars.toList, selectedQVars.toList, new IdxVarId(cvarsID, qvarsID))
    }

    override def consumed: Boolean =
      (cvars.valuesIterator ++ qvars.valuesIterator).forall(_.consumed)
  }

  object IdxVarId {
    def apply(vars : List[(Variable,Option[Int])]) : IdxVarId = {
      val cvars = new mutable.HashMap[CVariable,List[Int]]()
      val qvars = new mutable.HashMap[QVariable,List[Int]]()

      for (vi <- vars) vi match {
        case (v : CVariable, None) =>
          if (cvars.contains(v))
            throw UserException(s"Incompatible local variable specification for ${v.name}")
          cvars.update(v,Nil)
        case (v : QVariable, None) =>
          if (qvars.contains(v))
            throw UserException(s"Incompatible local variable specification for ${v.name}")
          qvars.update(v,Nil)
        case (v : CVariable, Some(i)) =>
          val sofar = cvars.get(v) match {
            case None => Nil
            case Some(Nil) =>
              throw UserException(s"Incompatible local variable specification for ${v.name}")
            case Some(l) => l
          }
          if (sofar.contains(i))
            throw UserException(s"Incompatible local variable specification for ${v.name}")
          cvars.update(v, sofar ++ List(i))
        case (v : QVariable, Some(i)) =>
          val sofar = qvars.get(v) match {
            case None => Nil
            case Some(Nil) =>
              throw UserException(s"Incompatible local variable specification for ${v.name}")
            case Some(l) => l
          }
          if (sofar.contains(i))
            throw UserException(s"Incompatible local variable specification for ${v.name}")
          qvars.update(v, sofar ++ List(i))
      }

      def toSVID(l: List[Int]) = l match {
        case Nil => AllOccurrences
        case l => Occurrences(l.sorted)
      }

      IdxVarId(cvars.toMap.mapValues(toSVID), qvars.toMap.mapValues(toSVID))
    }
  }
}

