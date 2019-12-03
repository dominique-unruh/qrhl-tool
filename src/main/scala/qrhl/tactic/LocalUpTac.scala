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
      println(s"*** Possibly unsound (not proven) tactic 'local up' applied.")
      val (left2, id) = if (side.forall(_==true)) up2(env, varID, left) else (left,varID)
      val (right2, id2) = if (side.forall(_==false)) up2(env, id, right) else (right,id)
      if (!id2.consumed())
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
    * * A variable cannot be moved further upward due to a conflicting variable use (then a suitable [[Local]] statement is inserted)
    *
    * If upwards movement does not stop, the variable is returned
    *
    * It is guaranteed that Local(cVars,qVars,returnStatement) is denotationally equivalent to statement.
    *
    * @return (statement,cVars,qVars,id) where statement is the rewritten statement, and cVars,qVars are
    *         lists of the variables that moved to the top. id is the updated [[VarID]] (in case some variables have been selected by id for moving).
    * */
  def up(env: Environment, id: VarID, statement: Statement): (Statement,ListSet[CVariable],ListSet[QVariable],VarID) = statement match {
    case _: Assign | _: Sample | _: QInit | _: QApply | _: Measurement | _: Call => (statement,empty,empty,id)
    case While(condition, body) =>
      val (body2, cVars, qVars, id2) = up(env, id, body)
      /** classical variables that can move further */
      val upCvars = cVars.diff(condition.caVariables(env).classical)
      /** classical variables that have to stop here */
      val downCvars = cVars.intersect(condition.caVariables(env).classical)
      // Re-initialize local variables in each loop body iteration
      val body3 = (init(classical = upCvars.toSeq, quantum = qVars.toSeq) ++ body2.toBlock).unwrapTrivialBlock
      val body4 = Local.makeIfNeeded(cvars=downCvars.toSeq, qvars=Nil, body=body3)

      (While(condition, body4.toBlock), upCvars, qVars, id2)
    case IfThenElse(condition, thenBranch, elseBranch) =>
      ???
    case Block() => (statement, empty, empty, id)
    case Block(s) =>
      up(env, id, s)
    case Block(statements@_*) =>
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

          if (cvarsDown.isEmpty && qvarsDown.isEmpty)
            statements3.append(st.toBlock.statements : _*)
          else
            statements3.append(Local(cvarsDown.toSeq, qvarsDown.toSeq, st.toBlock))
      }

      val resultBlock = Block(statements3: _*)

      (resultBlock, ListSet(cCandidates.keys.toSeq:_*), ListSet(qCandidates.keys.toSeq:_*), id2)
    case Local(cvars, qvars, body) =>
      val (cvars2, qvars2, id2) = id.select(cvars, qvars)
      val (body2, cvars3, qvars3, id3) = up(env,id2,body.unwrapTrivialBlock)

      val allCVars = ListSet(cvars:_*) ++ cvars3
      val keepCVars = allCVars -- cvars2
      val allQVars = ListSet(qvars:_*) ++ qvars3
      val keepQVars = allQVars -- qvars2

      logger.debug(s"Local: $statement, ${(cvars2,qvars2)} ${(body2,cvars3,qvars3)}")

      val body3 = Local.makeIfNeeded(keepCVars.toSeq, keepQVars.toSeq, body2)
      (body3, ListSet(cvars2:_*), ListSet(qvars2:_*), id3)
  }
}

object LocalUpTac {
  private val logger = log4s.getLogger

  sealed trait VarID {
    def consumed() : Boolean
    def select(cvars: List[CVariable], qvars: List[QVariable]) : (List[CVariable], List[QVariable], VarID)
  }

  final case object AllVars extends VarID {
    override def select(cvars: List[CVariable], qvars: List[QVariable]): (List[CVariable], List[QVariable], VarID) = (cvars,qvars,AllVars)
    override def consumed(): Boolean = true
  }

  final case class IdxVarId(cvars : Map[CVariable, List[Int]], qvars : Map[QVariable, List[Int]]) extends VarID {
    for (l <- cvars.valuesIterator ++ qvars.valuesIterator) {
      assert (Utils.isSortedUnique(l))
      assert (l.forall(_>0))
    }

    override def select(cvars: List[CVariable], qvars: List[QVariable]): (List[CVariable], List[QVariable], VarID) = {
      val selectedCVars = new ListBuffer[CVariable]()
      val selectedQVars = new ListBuffer[QVariable]()

      var cvarsID = this.cvars
      var qvarsID = this.qvars

      for (v <- cvars) {
        cvarsID.get(v) match {
          case None =>
          case Some(Nil) =>
            selectedCVars += v
          case Some(List(1)) =>
            cvarsID = cvarsID - v
            selectedCVars += v
          case Some(1 :: l) =>
            cvarsID = cvarsID.updated(v, l.map(_-1))
            selectedCVars += v
          case Some(l) =>
            cvarsID = cvarsID.updated(v, l.map(_-1))
        }
      }

      for (v <- qvars) {
        qvarsID.get(v) match {
          case None =>
          case Some(Nil) =>
            selectedQVars += v
          case Some(List(1)) =>
            qvarsID = qvarsID - v
            selectedQVars += v
          case Some(1 :: l) =>
            qvarsID = qvarsID.updated(v, l.map(_-1))
            selectedQVars += v
          case Some(l) =>
            qvarsID = qvarsID.updated(v, l.map(_-1))
        }
      }

      (selectedCVars.toList, selectedQVars.toList, new IdxVarId(cvarsID, qvarsID))
    }

    override def consumed(): Boolean =
      (cvars.valuesIterator ++ qvars.valuesIterator).forall(_.isEmpty)
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

      IdxVarId(cvars.toMap.mapValues(_.sorted), qvars.toMap.mapValues(_.sorted))
    }
  }
}

