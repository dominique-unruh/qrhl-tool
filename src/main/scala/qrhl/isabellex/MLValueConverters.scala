package qrhl.isabellex

import isabelle.control.{Isabelle, MLFunction, MLValue}
import isabelle.control.MLValue.Converter
import qrhl.logic.{Assign, Block, CVariable, Call, IfThenElse, Local, Measurement, QApply, QInit, QVariable, Sample, Statement, VTCons, VTSingle, VTUnit, VarTerm, While}
import IsabelleX.{globalIsabelle => GIsabelle}
import GIsabelle.Ops
import isabelle.control
import qrhl.{AmbientSubgoal, QRHLSubgoal, Subgoal}

import scala.concurrent.{ExecutionContext, Future}

// Implicits
import MLValue.Implicits._
import isabelle.Term.Implicits._
import isabelle.Typ.Implicits._
import MLValueConverters.Implicits._


object MLValueConverters {
  object StatementConverter extends Converter[Statement] {
    override def store(value: Statement)(implicit isabelle: control.Isabelle, ec: ExecutionContext): MLValue[Statement] = value match {
      case local: Local =>
        Ops.makeLocal((
          VarTerm.varlist(local.vars.collect { case CVariable(name, typ) => (name,typ) } :_*),
          VarTerm.varlist(local.vars.collect { case QVariable(name, typ) => (name,typ) } :_*),
          local.body.statements))
      case block: Block =>
        Ops.listToBlock(block.statements)
      case Assign(variable, expression) =>
        Ops.makeAssign((variable.map(_.name), expression.isabelleTerm))
      case Sample(variable, expression) =>
        Ops.makeSample((variable.map(_.name), expression.isabelleTerm))
      case IfThenElse(condition, thenBranch, elseBranch) =>
        Ops.makeIfThenElse((condition.isabelleTerm,thenBranch.statements,elseBranch.statements))
      case While(condition, body) =>
        Ops.makeWhile((condition.isabelleTerm,body.statements))
      case QInit(location, expression) =>
        Ops.makeQInit((location.map(_.name), expression.isabelleTerm))
      case QApply(location, expression) =>
        Ops.makeQApply((location.map(_.name), expression.isabelleTerm))
      case Measurement(result, location, e) =>
        Ops.makeMeasurement((result.map(_.name), location.map(_.name), e.isabelleTerm))
      case call : Call =>
        Ops.makeCall(call)
    }
    override def retrieve(value: MLValue[Statement])(implicit isabelle: control.Isabelle, ec: ExecutionContext): Future[Statement] = {
      Ops.whatStatementOp(value).retrieve.flatMap {
            // Operations are already defined, Ops.destBlock etc.
        case "block" => ???
        case "local" => ???
        case "assign" => ???
        case "sample" => ???
        case "call" => ???
        case "measurement" => ???
        case "qinit" => ???
        case "qapply" => ???
        case "ifthenelse" => ???
        case "while" => ???
      }
    }

    override lazy val exnToValue: String = "fn QRHL_Operations.E_Statement s => s"
    override lazy val valueToExn: String = "QRHL_Operations.E_Statement"
  }

  object CallConverter extends Converter[Call] {
    override def retrieve(value: MLValue[Call])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Call] =
      for ((str,args) <- Ops.destCALL(value).retrieve)
        yield Call(str, args :_*)

    override def store(value: Call)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Call] =
      Ops.makeCALL((value.name, value.args.toList))

    override val exnToValue: String = "fn QRHL_Operations.E_Call x => x"
    override val valueToExn: String = "QRHL_Operations.E_Call"
  }

  class VarTermConverter[A](implicit conv: Converter[A]) extends Converter[VarTerm[A]] {
    override def retrieve(value: MLValue[VarTerm[A]])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[VarTerm[A]] = {
      val valueM = value.asInstanceOf[MLValue[VarTerm[MLValue[A]]]]
      Ops.whatVartermOp[A](valueM).retrieve.flatMap {
        case "cons" =>
          Ops.destVartermCons[A](valueM).retrieve.flatMap { case (left,right) =>
            val leftFuture = left.asInstanceOf[MLValue[VarTerm[A]]].retrieve
            val rightFuture = right.asInstanceOf[MLValue[VarTerm[A]]].retrieve
            for (leftVal <- leftFuture; rightVal <- rightFuture)
              yield VTCons(leftVal, rightVal)
          }
        case "single" =>
          for (a <- Ops.destVartermSingle[A](valueM).asInstanceOf[MLValue[A]].retrieve)
            yield VTSingle(a)
        case "unit" => Future.successful(VTUnit)
      }
    }

    override def store(value: VarTerm[A])(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[VarTerm[A]] = value match {
      case VTUnit =>
        Ops.vartermUnit.asInstanceOf[MLValue[VarTerm[A]]]
      case VTSingle(v) =>
        Ops.vartermSingle.asInstanceOf[MLFunction[MLValue[A], VarTerm[MLValue[A]]]]
          .apply(MLValue(v).mlValueOfItself)
          .asInstanceOf[MLValue[VarTerm[A]]]
      case VTCons(a, b) =>
        Ops.vartermCons[A]
          .apply(MLValue(a).asInstanceOf, MLValue(b).asInstanceOf)
          .asInstanceOf[MLValue[VarTerm[A]]]
    }
    override val exnToValue: String = s"fn QRHL_Operations.E_Varterm vt => QRHL_Operations.map_tree (${conv.exnToValue}) vt"
    override val valueToExn: String = s"QRHL_Operations.E_Varterm o QRHL_Operations.map_tree (${conv.valueToExn})"
  }

  object SubgoalConverter extends Converter[Subgoal] {
    override def retrieve(value: MLValue[Subgoal])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Subgoal] =
      Ops.isQrhlSubgoal(value).retrieve.flatMap { isQrhl =>
        if (isQrhl)
          for ((left,right,pre,post,assms) <- Ops.destQrhlSubgoal(value).retrieve)
            yield QRHLSubgoal(Block(left:_*), Block(right:_*), RichTerm(pre), RichTerm(post), assms.map(RichTerm.apply))
        else
          for (t <- Ops.destAmbientSubgoal(value).retrieve)
            yield new AmbientSubgoal(RichTerm(t))
      }

    override def store(value: Subgoal)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Subgoal] = value match {
      case QRHLSubgoal(left, right, pre, post, assumptions) =>
        Ops.makeQrhlSubgoal(left.statements, right.statements, pre.isabelleTerm, post.isabelleTerm, assumptions.map(_.isabelleTerm))
      case AmbientSubgoal(goal) => Ops.makeAmbientSubgoal(goal.isabelleTerm)
    }
    override lazy val exnToValue: String = "fn QRHL_Operations.E_Subgoal s => s"
    override lazy val valueToExn: String = "QRHL_Operations.E_Subgoal"
  }

  object Implicits {
    @inline implicit def vartermConverter[A](implicit conv: Converter[A]): VarTermConverter[A] = new VarTermConverter[A]
    implicit val statementConverter: StatementConverter.type = StatementConverter
    implicit val callConverter: CallConverter.type = CallConverter
    implicit val subgoalConverter: SubgoalConverter.type = SubgoalConverter
  }

}
