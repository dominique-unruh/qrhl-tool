package isabelle.control

import org.log4s
import org.log4s.Logger

import scala.annotation.tailrec
import scala.concurrent.ExecutionContext

trait OperationCollection {

  import OperationCollection._

  protected type Ops

  protected def newOps(implicit isabelle: Isabelle, ec: ExecutionContext): Ops

  /** Data structure optimized for very few (usually exactly 1) entries */
  private var opsInstances: List[(Isabelle, Ops)] = Nil

  private def addInstance(isabelle: Isabelle, ec: ExecutionContext): Ops = synchronized {
    def add() = {
      logger.debug(s"Adding Ops instance in ${getClass.getName} for $isabelle")
      assert(isabelle != null)
      assert(ec != null)
      assert(!isabelle.isDestroyed)
      val ops = newOps(isabelle, ec)
      opsInstances = (isabelle, ops) :: opsInstances.filterNot(_._1.isDestroyed)
      ops
    }

    // Searching again, in case of a race condition that added this instance while we did not have a lock
    @tailrec
    def get(instances: List[(Isabelle, Ops)]): Ops = instances match {
      case Nil => add()
      case (isabelle2, ops) :: rest =>
        if (isabelle2 == isabelle) ops
        else get(rest)
    }

    get(opsInstances)
  }

  def Ops(implicit isabelle: Isabelle, ec: ExecutionContext): Ops = {
    @tailrec
    def get(instances: List[(Isabelle, Ops)]): Ops = instances match {
      case (isabelle2, ops) :: rest =>
        if (isabelle2 == isabelle) ops
        else get(rest)
      case Nil => addInstance(isabelle, ec)
    }

    get(opsInstances)
  }

  def init()(implicit isabelle: Isabelle, executionContext: ExecutionContext): Unit =
    Ops
}

object OperationCollection {
  val logger: Logger = log4s.getLogger
}