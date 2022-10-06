package qrhl.isabellex

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.MLValue.Converter
import qrhl.logic.{Assign, Block, CVariable, Call, IfThenElse, Local, Measurement, QApply, QInit, QVariable, Sample, Statement, VTCons, VTSingle, VTUnit, VarTerm, While}
import IsabelleX.{globalIsabelle => GIsabelle}
import GIsabelle.Ops
import de.unruh.isabelle.control
import de.unruh.isabelle.mlvalue.MLValue
import qrhl.{AmbientSubgoal, DenotationalEqSubgoal, QRHLSubgoal, Subgoal}
import scalaz.Id.Id

import scala.concurrent.{ExecutionContext, Future}
import GIsabelle.Ops.qrhl_ops
import de.unruh.isabelle.control.Isabelle.{DInt, DList, DObject}
import de.unruh.isabelle.pure.{MLValueTerm, Term}

// Implicits
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
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
        Ops.makeAssign((variable.map(v => (v.name,v.valueTyp)), expression.isabelleTerm))
      case Sample(variable, expression) =>
        Ops.makeSample((variable.map(v => (v.name,v.valueTyp)), expression.isabelleTerm))
      case IfThenElse(condition, thenBranch, elseBranch) =>
        Ops.makeIfThenElse((condition.isabelleTerm,thenBranch.statements,elseBranch.statements))
      case While(condition, body) =>
        Ops.makeWhile((condition.isabelleTerm,body.statements))
      case QInit(location, expression) =>
        Ops.makeQInit((location.map(v => (v.name,v.valueTyp)), expression.isabelleTerm))
      case QApply(location, expression) =>
        Ops.makeQApply((location.map(v => (v.name,v.valueTyp)), expression.isabelleTerm))
      case Measurement(result, location, e) =>
        Ops.makeMeasurement((result.map(v => (v.name,v.valueTyp)), location.map(v => (v.name,v.valueTyp)), e.isabelleTerm))
      case call : Call =>
        Ops.makeCall(call)
    }
    override def retrieve(value: MLValue[Statement])(implicit isabelle: control.Isabelle, ec: ExecutionContext): Future[Statement] = {
      Ops.whatStatementOp(value).retrieve.flatMap {
            // Operations are already defined, Ops.destBlock etc.
        case "block" =>
          for (statements <- Ops.destBlock(value).retrieve)
            yield Block(statements :_*)
        case "local" =>
          for ((cvars,qvars,stmts) <- Ops.destLocal(value).retrieve)
            yield Local(
              cvars.toList.map { case (name, typ) => CVariable(name,typ) },
              qvars.toList.map { case (name, typ) => QVariable(name,typ) },
              Block(stmts :_*))
        case "assign" =>
          for ((vars, expr) <- Ops.destAssign(value).retrieve)
            yield Assign(vars.map { case (name, typ) => CVariable(name,typ) }, RichTerm(expr))
        case "sample" =>
          for ((vars, expr) <- Ops.destSample(value).retrieve)
            yield Sample(vars.map { case (name, typ) => CVariable(name,typ) }, RichTerm(expr))
        case "call" =>
          Ops.destCall(value).retrieve
        case "measurement" =>
          for ((result, location, e) <- Ops.destMeasurement(value).retrieve)
            yield Measurement(
              result.map { case (name, typ) => CVariable(name,typ) },
              location.map { case (name, typ) => QVariable(name,typ) },
              RichTerm(e))
        case "qinit" =>
          for ((vars, expr) <- Ops.destQInit(value).retrieve)
            yield QInit(vars.map { case (name, typ) => QVariable(name,typ) }, RichTerm(expr))
        case "qapply" =>
          for ((vars, expr) <- Ops.destQApply(value).retrieve)
            yield QApply(vars.map { case (name, typ) => QVariable(name,typ) }, RichTerm(expr))
        case "ifthenelse" =>
          for ((cond,thens,elses) <- Ops.destIfThenElse(value).retrieve)
            yield IfThenElse(RichTerm(cond), Block(thens:_*), Block(elses:_*))
        case "while" =>
          for ((cond,body) <- Ops.destWhile(value).retrieve)
            yield While(RichTerm(cond), Block(body:_*))
      }
    }

    override def exnToValue(implicit isabelle: Isabelle, ec: ExecutionContext): String = s"fn ${qrhl_ops}.E_Statement s => s"
    override def valueToExn(implicit isabelle: Isabelle, ec: ExecutionContext): String = s"$qrhl_ops.E_Statement"

    override def mlType(implicit isabelle: Isabelle, ec: ExecutionContext): String = s"$qrhl_ops.statement"
  }

  object CallConverter extends Converter[Call] {
    override def retrieve(value: MLValue[Call])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Call] =
      for ((str,args) <- Ops.destCALL(value).retrieve)
        yield Call(str, args :_*)

    override def store(value: Call)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Call] =
      Ops.makeCALL((value.name, value.args.toList))

    override def exnToValue(implicit isabelle: Isabelle, ec: ExecutionContext): String = s"fn $qrhl_ops.E_Call x => x"
    override def valueToExn(implicit isabelle: Isabelle, ec: ExecutionContext): String = s"$qrhl_ops.E_Call"

    override def mlType(implicit isabelle: Isabelle, ec: ExecutionContext): String = s"$qrhl_ops.call"
  }

  class VarTermConverter[A](implicit conv: Converter[A]) extends Converter[VarTerm[A]] {
    override def retrieve(value: MLValue[VarTerm[A]])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[VarTerm[A]] = {
      val valueM = value.insertMLValue[VarTerm,A]
//        .asInstanceOf[MLValue[VarTerm[MLValue[A]]]]
      Ops.whatVartermOp[A](valueM).retrieve.flatMap {
        case "cons" =>
          type C[X] = (VarTerm[X], VarTerm[X])
          val dest = Ops.destVartermCons[A](valueM)
            .removeMLValue[C,A]
//            .asInstanceOf[MLValue[(VarTerm[A], VarTerm[A])]]
          for ((left,right) <- dest.retrieve)
            yield VTCons(left, right)
          /*dest.retrieve.flatMap { case (left,right) =>
            val leftFuture = left.asInstanceOf[MLValue[VarTerm[A]]].retrieve
            val rightFuture = right.asInstanceOf[MLValue[VarTerm[A]]].retrieve
            for (leftVal <- leftFuture; rightVal <- rightFuture)
              yield VTCons(leftVal, rightVal)
          }*/
        case "single" =>
          val dest = Ops.destVartermSingle[A](valueM).removeMLValue[Id,A]
          for (a <- dest.retrieve)
            yield VTSingle(a)
        case "unit" => Future.successful(VTUnit)
      }
    }

    override def store(value: VarTerm[A])(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[VarTerm[A]] = value match {
      case VTUnit =>
        Ops.vartermUnit[A]
      case VTSingle(v) =>
        Ops.vartermSingle[A](MLValue(v).insertMLValue[Id, A])
          .removeMLValue[VarTerm, A]
//          .asInstanceOf[MLValue[VarTerm[A]]]
      case VTCons(a, b) =>
        Ops.vartermCons[A]
          .apply(MLValue(a).insertMLValue[VarTerm,A], MLValue(b).insertMLValue[VarTerm,A])
          .removeMLValue[VarTerm,A]
    }
    override def exnToValue(implicit isabelle: Isabelle, ec: ExecutionContext): String = s"fn $qrhl_ops.E_Varterm vt => $qrhl_ops.map_tree (${conv.exnToValue}) vt"
    override def valueToExn(implicit isabelle: Isabelle, ec: ExecutionContext): String = s"$qrhl_ops.E_Varterm o $qrhl_ops.map_tree (${conv.valueToExn})"
    override def mlType(implicit isabelle: Isabelle, ec: ExecutionContext): String = s"(${conv.mlType}) $qrhl_ops.tree"
  }

  object SubgoalConverter extends Converter[Subgoal] {
    override def retrieve(value: MLValue[Subgoal])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Subgoal] = {
      for (subgoalType <- Ops.subgoalType(value).retrieve;
           subgoal <- subgoalType match {
             case 1 =>
               for ((left, right, pre, post, assms) <- Ops.destQrhlSubgoal(value).retrieve)
                 yield QRHLSubgoal(Block(left: _*), Block(right: _*), RichTerm(pre), RichTerm(post), assms.map(RichTerm.apply))
             case 2 =>
               for ((left, right, assms) <- Ops.destDenEqSubgoal(value).retrieve)
                 yield DenotationalEqSubgoal(left.toBlock, right.toBlock, assms.map(RichTerm.apply))
             case 3 =>
               for (t <- Ops.destAmbientSubgoal(value).retrieve)
                 yield new AmbientSubgoal(RichTerm(t)) })
        yield subgoal
/*      Ops.isQrhlSubgoal(value).retrieve.flatMap { isQrhl =>
        if (isQrhl)
          for ((left,right,pre,post,assms) <- Ops.destQrhlSubgoal(value).retrieve)
            yield QRHLSubgoal(Block(left:_*), Block(right:_*), RichTerm(pre), RichTerm(post), assms.map(RichTerm.apply))
        else
          for (t <- Ops.destAmbientSubgoal(value).retrieve)
            yield new AmbientSubgoal(RichTerm(t))
      }*/
    }

    override def store(value: Subgoal)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Subgoal] = value match {
      case QRHLSubgoal(left, right, pre, post, assumptions) =>
        Ops.makeQrhlSubgoal(left.statements, right.statements, pre.isabelleTerm, post.isabelleTerm, assumptions.map(_.isabelleTerm))
      case AmbientSubgoal(goal) =>
        Ops.makeAmbientSubgoal(goal.isabelleTerm)
      case DenotationalEqSubgoal(left, right, assms) =>
        Ops.makeDenotationalEqSubgoal(left, right, assms.map(_.isabelleTerm))
    }
    override def exnToValue(implicit isabelle: Isabelle, ec: ExecutionContext): String = s"fn $qrhl_ops.E_Subgoal s => s"
    override def valueToExn(implicit isabelle: Isabelle, ec: ExecutionContext): String = s"$qrhl_ops.E_Subgoal"
    override def mlType(implicit isabelle: Isabelle, ec: ExecutionContext): String = s"$qrhl_ops.subgoal"
  }

  object Implicits {
    @inline implicit def vartermConverter[A](implicit conv: Converter[A]): VarTermConverter[A] = new VarTermConverter[A]
    implicit val statementConverter: StatementConverter.type = StatementConverter
    implicit val callConverter: CallConverter.type = CallConverter
    implicit val subgoalConverter: SubgoalConverter.type = SubgoalConverter
  }

}
