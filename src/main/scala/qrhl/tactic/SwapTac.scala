package qrhl.tactic

import hashedcomputation.{Hash, HashTag, Hashable, HashedValue}

import java.io.PrintWriter
import org.log4s
import qrhl._
import qrhl.logic.{Assign, Block, Call, Environment, IfThenElse, Local, Measurement, QApply, QInit, Sample, Statement, Variable, While}

import scala.collection.immutable.ListSet
import hashedcomputation.Implicits._
import qrhl.Utils.pluralS
import qrhl.isabellex.IsabelleX.{ContextX, globalIsabelle}
import qrhl.tactic.SwapTac.logger

// TODO: reference literature for this tactic
case class SwapTac(left:Boolean, range:SwapTac.Range, steps:Int,
                   subprograms: List[(Statement, Option[Statement])],
                   subprogramsInFirst: Boolean) extends Tactic {
  if (steps < 1)
    throw UserException(s"swap tactic must get numeric argument >=1, not $steps")

  override def hash: Hash[SwapTac.this.type] = HashTag()(Hashable.hash(left), range.hash, Hashable.hash(steps),
    Hashable.hash(subprograms), Hashable.hash(subprogramsInFirst))

  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case QRHLSubgoal(l,r,pre,post,assms) =>
      val env = state.environment
      implicit val ctxt: ContextX = state.isabelle
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

  private def checkSwappable(env: Environment, context : Block, nonContext: Block): Unit = {
    val vars1 = context.variableUse(env)
    val vars2 = nonContext.variableUse(env)

    def error(msg: String) =
      throw UserException(s"Cannot swap\n    $context\nand\n    $nonContext,\n$msg")

    def vars(vars:ListSet[_<:Variable]) : String =
      vars.map(_.name).mkString(", ")

    val qshared = vars1.quantum.intersect(vars2.quantum)
    if (qshared.nonEmpty)
      error(s"they have shared quantum variables (${vars(qshared)})")

    val wshared = vars1.writtenClassical.intersect(vars2.writtenClassical)
    if (wshared.nonEmpty)
      error(s"they have shared written classical variables (${vars(wshared)})")

    val w1r2 = vars1.writtenClassical.intersect(vars2.classical)
    if (w1r2.nonEmpty)
      error(s"the first block writes classical variables that the second reads (${vars(w1r2)})")

    val w2r1 = vars2.writtenClassical.intersect(vars1.classical)
    if (w2r1.nonEmpty)
      error(s"the first block reads classical variables that the second writes (${vars(w2r1)})")

    val i1f2 = vars1.inner.intersect(vars2.freeVariables)
    if (i1f2.nonEmpty)
      error(s"the first block has inner variables that are free in the second (${vars(i1f2)})")
  }

  def blockSplitAt(block: Block, i: Int): (Block, Block) = {
    val (first,second) = block.statements.splitAt(i)
    (Block(first:_*), Block(second:_*))
  }

  def swap(env:Environment, prog: Block)(implicit output: PrintWriter, ctxt : ContextX) : (Block, List[DenotationalEqSubgoal]) = {
    SwapTac.logger.debug(this.toString)

    if (subprograms.nonEmpty)
      output.println(s"\nHINT: The ${Utils.plural("first", subprograms.length, "subgoal")} " +
        s"(denotational equivalence${pluralS(subprograms.length)}) can usually be best handled by invoking the byqrhl tactic.\n")

    /** - [[beforeSecond]]: everything before the second block of the swap
     * - [[secondBlock]]: the second block of the swap
     * - [[after]]: everything after the second block of the swap */
    val (beforeSecond,secondBlock,after) = range.split(prog)

    output.println(s"In ${if (left) "left" else "right"} program: swapping $range with $steps statement${pluralS(steps)} before that.")

    if (beforeSecond.length<steps)
      throw UserException(s"Program must have at least ${steps+1} statements before the specified range (not ${beforeSecond.length})")

    /** - [[before]]: everything before the first block of the swap
     * - [[firstBlock]]: the first block of the swap */
    val (before, firstBlock) = blockSplitAt(beforeSecond, beforeSecond.length-steps)
    output.println(s"That is,\n  SECOND: $secondBlock\nwith\n  FIRST:  $firstBlock")
    if (subprograms.nonEmpty)
      output.println(s"\nLooking for ${subprograms.length} specified subprogram${pluralS(subprograms.length)} in ${if (subprogramsInFirst) "FIRST" else "SECOND"}.")

    /** [[firstBlock]]/[[secondBlock]], depending on which one has the subprograms */
    val blockWithSubs = if (subprogramsInFirst) firstBlock else secondBlock

    /** [[firstBlock]]/[[secondBlock]] with subprograms replaced by oracles (depending on [[subprogramsInFirst]]) */
    val context =
      if (subprograms.nonEmpty) findOracles(blockWithSubs).toBlock else blockWithSubs
    logger.debug(s"Context: $context")

    /** The one of [[firstBlock]]/[[secondBlock]] that does not have the subprograms (i.e., not [[context]]) */
    val blockWithoutSubs = if (subprogramsInFirst) secondBlock else firstBlock

    if (subprograms.nonEmpty)
      checkOraclesUsed(env, context)

    checkSwappable(env, context, blockWithoutSubs)

    /** [[context]] but with subprograms replaced by changed subprograms */
    val contextSubstituted = if (subprograms.forall(_._2.isEmpty)) blockWithSubs else
      context.substituteOracles(Map.from(subprograms.zipWithIndex.map({
        case ((original,changed),index) => (index.toString, changed.getOrElse(original))})))
        .toBlock

    /** [[firstBlock]] with substitutions done (if necessary). */
    val firstBlockSubstituted = if (subprogramsInFirst) contextSubstituted else firstBlock
    /** [[secondBlock]] with substitutions done (if necessary). */
    val secondBlockSubstituted = if (subprogramsInFirst) secondBlock else contextSubstituted

    val subgoals = subprograms map { case (original, changed) =>
      val changed2 = changed.getOrElse(original).toBlock
      val lhs = if (subprogramsInFirst) { original.toBlock ++ secondBlock}
                                   else { firstBlock ++ original.toBlock }
      val rhs = if (subprogramsInFirst) { secondBlock ++ changed2 }
                                   else { changed2 ++ firstBlock }
      DenotationalEqSubgoal(lhs, rhs, Nil)
    }

    (before ++ secondBlockSubstituted ++ firstBlockSubstituted ++ after,
      subgoals)
  }

  private def checkOraclesUsed(env: Environment, block: Block)(implicit output: PrintWriter): Unit = {
    val oracles = block.variableUse(env).oracles
    for (i <- subprograms.indices)
      if (!oracles.contains(i.toString))
        output.println(s"\nWARNING: Did not find any occurrences of the subprogram ${subprograms(i)._1}.")
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

  sealed trait Range extends HashedValue {
    def split(prog:Block) : (Block, Block, Block)
  }
  final case class FinalRange(numStatements:Int) extends Range {
    override def toString: String = s"last $numStatements statement${pluralS(numStatements)}"
    assert(numStatements>0)

    override def split(prog: Block): (Block, Block, Block) = {
      if (prog.length < numStatements)
        throw UserException(s"You are trying to move the last $numStatements but program has only ${prog.length} statements")
      val (before,range) = prog.statements.splitAt(prog.length-numStatements)
      (Block(before:_*), Block(range:_*), Block.empty)
    }

    override def hash: Hash[FinalRange.this.type] = HashTag()(Hashable.hash(numStatements))
  }

  final case class MiddleRange(start:Int, end:Int) extends Range {
    if (start<=0)
      throw UserException(s"Start of range must be >=1 (not $start)")
    if (end<start)
      throw UserException(s"Start of range ($start) < end of range ($end)")

    override def toString: String = s"statements $start–$end"

    override def split(prog: Block): (Block, Block, Block) = {
      if (end>prog.length)
        throw UserException(s"End of range is $end, but program has only ${prog.length} statements")
      val (before,rangeEnd) = prog.statements.splitAt(start-1)
      val (range,endBlock) = rangeEnd.splitAt(end-start+1)
      (Block(before:_*), Block(range:_*), Block(endBlock:_*))
    }

    override def hash: Hash[MiddleRange.this.type] = HashTag()(Hashable.hash(start,end))
  }
}
