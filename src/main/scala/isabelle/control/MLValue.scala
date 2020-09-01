package isabelle.control

import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.util.{Failure, Success}

class MLValue[A] private[isabelle](private val id: Future[Isabelle.ID]) {
  def stateString: String = id.value match {
    case Some(Success(_)) => ""
    case Some(Failure(_)) => " (failed)"
    case None => " (loading)"
  }

  //  @inline val isabelle : Isabelle.this.type = Isabelle.this

  def isReady: Boolean = id.isCompleted

  @inline def retrieve(implicit retriever: MLValue.Retriever[A], isabelle: Isabelle, ec: ExecutionContext): Future[A] =
    retriever.retrieve(this)

  @inline def retrieveNow(implicit retriever: MLValue.Retriever[A], isabelle: Isabelle, ec: ExecutionContext): A =
    Await.result(retrieve, Duration.Inf)

  def apply[D, R](arg: MLValue[D])
                 (implicit ev: MLValue[A] =:= MLValue[D => R], isabelle: Isabelle, ec: ExecutionContext): MLValue[R] = {
    new MLValue(
      for (fVal <- ev(this).id;
           xVal <- arg.id;
           fx <- isabelle.applyFunction(fVal, xVal).future)
        yield fx
    )
  }

  def apply[D1, D2, R](arg1: MLValue[D1], arg2: MLValue[D2])
                      (implicit ev: MLValue[A] =:= MLValue[D1 => D2 => R], isabelle: Isabelle, ec: ExecutionContext): MLValue[R] =
    ev(this).apply[D1, D2 => R](arg1).apply[D2, R](arg2)

  def apply[D1, D2, D3, R](arg1: MLValue[D1], arg2: MLValue[D2], arg3: MLValue[D3])
                          (implicit ev: MLValue[A] =:= MLValue[D1 => D2 => D3 => R], isabelle: Isabelle, ec: ExecutionContext): MLValue[R] =
    ev(this).apply[D1, D2 => D3 => R](arg1).apply[D2, D3 => R](arg2).apply[D3, R](arg3)
}

object MLValue {

  abstract class Retriever[A] {
    protected[MLValue] def retrieve(value: MLValue[A])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[A]
  }

  implicit object IntRetriever extends Retriever[Int] {
    override protected[MLValue] def retrieve(value: MLValue[Int])
                                            (implicit isabelle: Isabelle, ec: ExecutionContext): Future[Int] =
      value.id.flatMap(isabelle.retrieveInteger(_).future)
  }

  implicit object StringRetriever extends Retriever[String] {
    override protected[MLValue] def retrieve(value: MLValue[String])
                                            (implicit isabelle: Isabelle, ec: ExecutionContext): Future[String] =
      value.id.flatMap(isabelle.retrieveString(_).future)
  }

  def apply(i: Int)(implicit isabelle: Isabelle): MLValue[Int] =
    new MLValue(isabelle.storeInteger(i).future)

  def apply(str: String)(implicit isabelle: Isabelle): MLValue[String] =
    new MLValue(isabelle.storeString(str).future)

  // TODO: Automatically add wrapping and unwrapping of exceptions
  def compileFunction[A, B](ml: String)(implicit isabelle: Isabelle): MLValue[A => B] =
    new MLValue(isabelle.storeFunction(ml).future)
}