package qrhl.tactic

import org.log4s
import qrhl.logic.{Assign, Block, CVariable, Call, Environment, IfThenElse, Local, Measurement, QApply, QInit, QVariable, Sample, Statement, VarTerm, While}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException}

import scala.collection.immutable.ListSet
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import LocalUpTac.{VarID, _}
import qrhl.isabelle.{Isabelle, RichTerm}

case class LocalUpTac(varID: VarID) extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case AmbientSubgoal(goal) =>
      throw UserException("Expected a qRHL subgoal")
    case QRHLSubgoal(left, right, pre, post, assumptions) =>
      val env = state.environment
      println(s"*** Possibly unsound (not proven) tactic 'local up' applied.")
      val (left2, id) = up2(env, varID, left)
      val (right2, _) = up2(env, id, right)
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

      logger.debug(s"Local: $statement, ${(cvars2,qvars2)} ${(body2,cvars3,qvars3)}")

      val body3 = Local.makeIfNeeded((cvars3--cvars2).toSeq, (qvars3--qvars2).toSeq, body2)
      (body3, ListSet(cvars2:_*), ListSet(qvars2:_*), id2)
  }
}

object LocalUpTac {
  private val logger = log4s.getLogger

  sealed trait VarID {
    def select(cvars: List[CVariable], qvars: List[QVariable]) : (List[CVariable], List[QVariable], VarID)
  }

  final case object AllVars extends VarID {
    override def select(cvars: List[CVariable], qvars: List[QVariable]): (List[CVariable], List[QVariable], VarID) = (cvars,qvars,AllVars)
  }
}

