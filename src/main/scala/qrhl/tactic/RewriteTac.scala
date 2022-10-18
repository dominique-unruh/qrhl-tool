package qrhl.tactic

import hashedcomputation.{Hash, HashTag, Hashable, HashedValue}
import qrhl.{AmbientSubgoal, DenotationalEqSubgoal, QRHLSubgoal, State, Subgoal, Tactic, UserException}
import qrhl.logic.Block
import hashedcomputation.Implicits._
import qrhl.tactic.RewriteTac.Code

import java.io.PrintWriter

case class RewriteTac(input: RewriteTac.Range, replacement: RewriteTac.Replacement) extends Tactic {
  override def hash: Hash[RewriteTac.this.type] = HashTag()(input.hash, replacement.hash)

  override def apply(state: State, goal: Subgoal)(implicit output: PrintWriter): List[Subgoal] = goal match {
    case QRHLSubgoal(left, right, pre, post, assumptions) =>
      val (denEq, newLeft, newRight) = doRewrite(state, left, right)
      List(denEq.addAssumptions(assumptions),
        QRHLSubgoal(newLeft, newRight, pre, post, assumptions))
    case DenotationalEqSubgoal(left, right, assumptions) =>
      val (denEq, newLeft, newRight) = doRewrite(state, left, right)
      List(denEq.addAssumptions(assumptions),
        DenotationalEqSubgoal(newLeft, newRight, assumptions))
    case AmbientSubgoal(goal) =>
      throw UserException("Expected qRHL goal")
  }

  private def doRewrite(state: State, left: Block, right: Block)(implicit output: PrintWriter) : (DenotationalEqSubgoal, Block, Block) = {
    val (before, main, after) = input.split(left, right)
    output.println(s"We replace $input, that is the following lines:")
    output.println(s"    $main")

    val newMain = replacement.extract(left, right)
    replacement match {
      case _ : Code =>
        output.println(s"We replace it by:")
      case _ =>
        output.println(s"We replace it by $replacement, that is the following lines:")
    }
    output.println(s"    $newMain")

    val denEq = DenotationalEqSubgoal(main, newMain, Nil)

    val result = before ++ newMain ++ after

    if (input.left)
      (denEq, result, right)
    else
      (denEq, left, result)
  }
}

object RewriteTac {
  sealed trait Replacement extends HashedValue {
    def extract(left: Block, right: Block): Block
  }

  sealed trait Range extends Replacement {
    val left: Boolean
    def split(left: Block, right: Block): (Block, Block, Block)
    override def extract(left: Block, right: Block): Block = split(left, right)._2
  }

  final case class Subseq(left: Boolean, start: Int, end: Int) extends Range {
    assert(start >= 1, s"Start of range must be a positive integer (not $start)")
    assert(end >= end, s"End of range ($end) must be >= start of range ($start)")
    override def hash: Hash[Subseq.this.type] = HashTag()(Hashable.hash(left), Hashable.hash(start), Hashable.hash(end))
    override def toString: String = s"${if (left) "left" else "right"} $start-$end"
    override def split(left: Block, right: Block): (Block, Block, Block) = {
      val block = if (this.left) left else right
      if (block.length < end)
        throw UserException(s"Cannot rewrite lines $start-$end in left program. The left program has only ${block.length} lines.")
      val (before, mainAfter) = block.statements.splitAt(start - 1)
      val (main, after) = mainAfter.splitAt(end - start + 1)
      (Block(before :_*), Block(main :_*), Block(after :_*))
    }
  }

  final case class All(left: Boolean) extends Range {
    override def hash: Hash[All.this.type] = HashTag()(Hashable.hash(left))
    override def toString: String = if (left) "left" else "right"
    override def split(left: Block, right: Block): (Block, Block, Block) =
      (Block.empty, if (this.left) left else right, Block.empty)
  }

  final case class Code(block: Block) extends Replacement {
    override def hash: Hash[Code.this.type] = HashTag()(block.hash)
    override def toString: String = block.toString
    override def extract(left: Block, right: Block): Block = block
  }
}