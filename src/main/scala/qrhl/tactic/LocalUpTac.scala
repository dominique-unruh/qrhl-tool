package qrhl.tactic

import org.log4s
import qrhl.logic.{Assign, Block, CVariable, Call, Environment, IfThenElse, Local, Measurement, QApply, QInit, QVariable, Sample, Statement, VarTerm, While}
import qrhl.{AmbientSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException}

import scala.collection.immutable.ListSet
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

case object LocalUpTac extends Tactic {
  override def apply(state: State, goal: Subgoal): List[Subgoal] = goal match {
    case AmbientSubgoal(goal) =>
      throw UserException("Expected a qRHL subgoal")
    case QRHLSubgoal(left, right, pre, post, assumptions) =>
      val env = state.environment
      List(QRHLSubgoal(up(env,left).toBlock, up(env,right).toBlock, pre, post, assumptions))
  }

  def init(classical: Seq[CVariable]=Nil, quantum: Seq[QVariable]=Nil): Block = {
    val statements = new ListBuffer[Statement]()
    for (c <- classical)
      statements.append(Assign(VarTerm.varlist(c), ???))
    for (q <- quantum)
      statements.append(QInit(VarTerm.varlist(q), ???))
    Block(statements : _*)
  }

  def up(env: Environment, statement: Statement): Statement = statement match {
    case _ : Assign | _ : Sample | _ : QInit | _ : QApply | _ : Measurement | _ : Call => statement
    case While(condition, body) =>
      up(env, body) match {
        case Local(cvars,qvars,body) => ???
          val upCvars = cvars.filterNot(condition.caVariables(env).classical.contains)
          val downCvars = cvars.filter(condition.caVariables(env).classical.contains)
          val body2 = init(classical=downCvars) ++ body
          Local(upCvars, qvars, While(condition, body2).toBlock)
        case body2 => While(condition, body2.toBlock)
      }
    case IfThenElse(condition, thenBranch, elseBranch) =>
      ???
//    case Block() => s
    case Block() => statement
    case Block(s) => Block(up(env,s))
    case Block(statements @ _*) =>
      logger.debug("Operating on a block")
      val statements2 = statements map { up(env,_) } toList;
      logger.debug(s"Statements after inner processing: ${statements2}")
      // keys = variables that should be moved into the joint Local
      // true = variable has already occurred in the statements processed so far (in the loop below)
      val cCandidates = new mutable.LinkedHashMap[CVariable,Boolean]()
      val qCandidates = new mutable.LinkedHashMap[QVariable,Boolean]()

      for (st <- statements2) st match {
        case Local(cvars, qvars, body) =>
          for (c <- cvars) cCandidates(c) = false
          for (q <- qvars) qCandidates(q) = false
        case _ =>
      }

      logger.debug(s"Candidates (preliminary): ${cCandidates.keys}; ${qCandidates.keys}")

      val varUse = Block(statements2 : _*).variableUse(env)
      for (c <- varUse.classical)
        cCandidates.remove(c)
      for (q <- varUse.quantum)
        qCandidates.remove(q)

      logger.debug(s"Candidates (cleaned):     ${cCandidates.keys}; ${qCandidates.keys}")

      if (cCandidates.isEmpty && qCandidates.isEmpty)
        return statement

      val statements3 = new ListBuffer[Statement]
      for (st <- statements2) st match {
        case Local(cvars, qvars, body) =>
          val cvarsUp = cvars.filter(cCandidates.contains)
          val cvarsDown = cvars.filterNot(cCandidates.contains)
          val qvarsUp = qvars.filter(qCandidates.contains)
          val qvarsDown = qvars.filterNot(qCandidates.contains)

          val cvarsInit = cvarsUp.filter(cCandidates(_) == true)
          val qvarsInit = qvarsUp.filter(qCandidates(_) == true)

          statements3.append(init(cvarsInit, qvarsInit).statements : _*)
          for (c <- cvarsUp) cCandidates(c) = true
          for (q <- qvarsUp) qCandidates(q) = true

          if (cvarsDown.isEmpty && qvarsDown.isEmpty)
            statements3.append(body.statements :_*)
          else
            statements3.append(Local(cvarsDown,qvarsDown,body))
        case _ => statements3.append(st)
      }

      Local(cCandidates.keys.toList, qCandidates.keys.toList, Block(statements3:_*))
    case Local(cvars, qvars, body) => up(env, body).toBlock match {
      case Block(Local(cvars2, qvars2, body2)) =>
        val cvars3 = new mutable.LinkedHashSet[CVariable]()
        for (c <- cvars) cvars3.add(c)
        for (c <- cvars2) cvars3.add(c)
        val qvars3 = new mutable.LinkedHashSet[QVariable]()
        for (q <- qvars) qvars3.add(q)
        for (q <- qvars2) qvars3.add(q)
        Local(cvars3.toList, qvars3.toList, body2)
      case _ =>
        val varUse = body.variableUse(env)
        Local(cvars.filter(varUse.classical.contains), qvars.filter(varUse.quantum.contains), body).simplifyEmpty
    }
  }
  private val logger = log4s.getLogger
}

