package qrhl.tactic

import de.unruh.isabelle.pure.Context
import hashedcomputation.{Hash, HashTag, Hashable, HashedValue}

import java.io.PrintWriter
import org.log4s
import qrhl._
import qrhl.logic.{Assign, Block, Call, Environment, IfThenElse, Local, Measurement, QApply, QInit, Sample, Statement, Variable, While}

import scala.collection.immutable.ListSet
import hashedcomputation.Implicits._
import qrhl.Utils.pluralS
import qrhl.isabellex.IsabelleX.{ContextX, globalIsabelle}
import qrhl.tactic.SwapTac.{MiddleRange, logger}

// TODO: reference literature for this tactic
case class SwapTac(left:Boolean, range1: SwapTac.Range, range2: SwapTac.Range,
                   subprograms: List[(Statement, Option[Statement])]) extends Tactic {

  override def hash: Hash[SwapTac.this.type] = HashTag()(Hashable.hash(left), range1.hash, range2.hash,
    Hashable.hash(subprograms))

  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case QRHLSubgoal(l,r,pre,post,assms) =>
      val env = state.environment
      implicit val ctxt: Context = state.isabelle.context
      val (swapped, subgoals) = swap(env, if (left) l else r)
      val subgoals2 = subgoals map { _.addAssumptions(assms) }
      subgoals2.appended(
        QRHLSubgoal(
          if (left) swapped else l,
          if (!left) swapped else r,
          pre, post, assms))
    case _ =>
      throw UserException("Expected qRHL goal")
  }

  private def checkSwappable(ctxt: Context, env: Environment, context : Block, nonContext: Block): Unit = {
    val vars1 = context.variableUse(ctxt, env)
    val vars2 = nonContext.variableUse(ctxt, env)

    def error(msg: String) =
      throw UserException(s"Cannot swap\n    $context\nand\n    $nonContext,\n$msg")

/*    def vars(vars:ListSet[_<:Variable]) : String =
      vars.map(_.name).mkString(", ")*/

    val qshared = vars1.quantum.intersect(vars2.quantum)
    if (qshared.nonEmpty)
      error(s"they have shared quantum variables (${Variable.varsToString(qshared)})")

    val wshared = vars1.writtenClassical.intersect(vars2.writtenClassical)
    if (wshared.nonEmpty)
      error(s"they have shared written classical variables (${Variable.varsToString(wshared)})")

    val w1r2 = vars1.writtenClassical.intersect(vars2.classical)
    if (w1r2.nonEmpty)
      error(s"the first block writes classical variables that the second reads (${Variable.varsToString(w1r2)})")

    val w2r1 = vars2.writtenClassical.intersect(vars1.classical)
    if (w2r1.nonEmpty)
      error(s"the first block reads classical variables that the second writes (${Variable.varsToString(w2r1)})")

    val i1f2 = vars1.inner.intersect(vars2.freeVariables)
    if (i1f2.nonEmpty)
      error(s"the first block has inner variables that are free in the second (${Variable.varsToString(i1f2)})")
  }

  def blockSplitAt(block: Block, i: Int): (Block, Block) = {
    val (first,second) = block.statements.splitAt(i)
    (Block(first:_*), Block(second:_*))
  }

  /** @return (before,block1,block2,after,block1first) */
  def split(prog: Block): (Block, Block, Block, Block, Boolean) = {
    (range1, range2) match {
      case (MiddleRange(start1, end1), MiddleRange(start2, end2)) if start2 == end1 + 1 =>
        //noinspection DuplicatedCode
        if (end2 > prog.length)
          throw UserException(s"Range $range2 goes beyond the length of the program (${prog.length})")
        val (before, prog2) = blockSplitAt(prog, start1 - 1)
        val (block1, prog3) = blockSplitAt(prog2, end1 - start1 + 1)
        val (block2, after) = blockSplitAt(prog3, end2 - start2 + 1)
        (before, block1, block2, after, true)
      case (MiddleRange(start1, end1), MiddleRange(start2, end2)) if start1 == end2 + 1 =>
        //noinspection DuplicatedCode
        if (end1 > prog.length)
          throw UserException(s"Range $range1 goes beyond the length of the program (${prog.length})")
        val (before, prog2) = blockSplitAt(prog, start2 - 1)
        val (block2, prog3) = blockSplitAt(prog2, end2 - start2 + 1)
        val (block1, after) = blockSplitAt(prog3, end1 - start1 + 1)
        (before, block1, block2, after, false)
      case (MiddleRange(start1, end1), MiddleRange(start2, end2)) =>
        throw UserException(s"Ranges $range1 and $range2 must be consecutive in program (either can be first, though)")
    }
  }

  def swap(env:Environment, prog: Block)(implicit output: PrintWriter, ctxt : Context) : (Block, List[DenotationalEqSubgoal]) = {
    SwapTac.logger.debug(this.toString)

    if (subprograms.nonEmpty)
      output.println(s"\nHINT: The ${Utils.plural("first", subprograms.length, "subgoal")} " +
        s"(denotational equivalence${pluralS(subprograms.length)}) can usually be best handled by invoking the byqrhl tactic.\n")

    output.println(s"In ${if (left) "left" else "right"} program: swapping range $range1 with $range2.")

    /** - [[block1]]: the second block of the swap
     * - [[after]]: everything after the second block of the swap
     * - [[before]]: everything before the first block of the swap
     * - [[block2]]: the first block of the swap
     * - [[block1First]]: Whether block1 is first or second inside the program */
    val (before, block1, block2, after, block1First) = split(prog)

    output.println(s"That is,\n  range $range1: $block1\nwith\n  range $range2:  $block2")
    if (subprograms.nonEmpty)
      output.println(s"\nLooking for ${subprograms.length} specified subprogram${pluralS(subprograms.length)} in range $range1.")

    /** [[block1]] with subprograms replaced by oracles */
    val context =
      if (subprograms.nonEmpty) findOracles(block1).toBlock else block1
    logger.debug(s"Context: $context")

    if (subprograms.nonEmpty)
      checkOraclesUsed(ctxt, env, context)

    checkSwappable(ctxt, env, context, block2)

    /** [[context]] but with subprograms replaced by changed subprograms */
    val contextSubstituted = if (subprograms.forall(_._2.isEmpty)) block1 else
      context.substituteOracles(Map.from(subprograms.zipWithIndex.map({
        case ((original,changed),index) => (index.toString, changed.getOrElse(original))})))
        .toBlock

    val subgoals = subprograms map { case (original, changed) =>
      val changed2 = changed.getOrElse(original).toBlock
      val lhs = if (block1First) { original.toBlock ++ block2}
                            else { block2 ++ original.toBlock }
      val rhs = if (block1First) { block2 ++ changed2 }
                            else { changed2 ++ block2 }
      DenotationalEqSubgoal(lhs, rhs, Nil)
    }

    val swappedProgram =
      if (block1First) before ++ block2 ++ contextSubstituted ++ after
      else before ++ contextSubstituted ++ block2 ++ after

    (swappedProgram, subgoals)
  }

  private def checkOraclesUsed(ctxt: Context, env: Environment, block: Block)(implicit output: PrintWriter): Unit = {
    val oracles = block.variableUse(ctxt, env).oracles
    for (i <- subprograms.indices)
      if (!oracles.contains(i.toString))
        output.println(s"\nWARNING: Did not find any occurrences of the subprogram ${subprograms(i)._1}.\n" +
          s"Note: subprograms are only searched for in the first range ($range1), but you are allowed to specify the ranges in opposite order ($range2 $range1).")
  }

  private def findOracles(statement: Statement): Statement =
    subprograms.zipWithIndex.find({ case ((original, changed), index) => statement == original }) match {
    case Some(((original, changed), index)) =>
      Call(s"@$index")
    case None => statement match {
      case Local(vars, body) =>
        Local(vars, findOracles(body).toBlock)
      case Block(statements @_*) =>
        Block(statements.map(findOracles) :_*)
      case _: Assign | _: Sample | _: QInit | _: QApply | _: Measurement =>
        statement
      case IfThenElse(condition, thenBranch, elseBranch) =>
        IfThenElse(condition, findOracles(thenBranch).toBlock, findOracles(elseBranch).toBlock)
      case While(condition, body) =>
        While(condition, findOracles(body).toBlock)
      case Call(name, args@_*) =>
        Call(name, args map { call => findOracles(call).asInstanceOf[Call] } :_*)
    }
  }
}


object SwapTac {
  private val logger = log4s.getLogger

  sealed trait Range extends HashedValue

  final case class MiddleRange(start:Int, end:Int) extends Range {
    if (start <= 0)
      throw UserException(s"Start of range must be >=1 (not $start)")
    if (start > end)
      throw UserException(s"Start of range ($start) > end of range ($end)")

    override def toString: String = s"$start–$end"

/*    override def split(prog: Block): (Block, Block, Block) = {
      if (end>prog.length)
        throw UserException(s"End of range is $end, but program has only ${prog.length} statements")
      val (before,rangeEnd) = prog.statements.splitAt(start-1)
      val (range,endBlock) = rangeEnd.splitAt(end-start+1)
      (Block(before:_*), Block(range:_*), Block(endBlock:_*))
    }*/

    override def hash: Hash[MiddleRange.this.type] = HashTag()(Hashable.hash(start,end))
  }
}
