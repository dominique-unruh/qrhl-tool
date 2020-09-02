package isabelle.control

import cats.Show

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


  abstract class Storer[A] {
    protected[MLValue] def store(value: A)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[A]
  }

  @inline def apply[A](value: A)(implicit storer: Storer[A], isabelle: Isabelle, executionContext: ExecutionContext) : MLValue[A] =
    storer.store(value)


  // TODO: Automatically add wrapping and unwrapping of exceptions
  def compileFunction[A, B](ml: String)(implicit isabelle: Isabelle): MLValue[A => B] =
    new MLValue(isabelle.storeFunction(ml).future)

  object IntStorer extends Storer[Int] {
    @inline override protected[MLValue] def store(value: Int)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Int] =
      new MLValue(isabelle.storeInteger(value).future)
  }

  object StringStorer extends Storer[String] {
    @inline override protected[MLValue] def store(value: String)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[String] =
      new MLValue(isabelle.storeString(value).future)
  }

  @inline class ListStorer[A](storer: Storer[A]) extends Storer[List[A]] {
    @inline override protected[MLValue] def store(value: List[A])(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[List[A]] = ???
  }

  object IntRetriever extends Retriever[Int] {
    @inline override protected[MLValue] def retrieve(value: MLValue[Int])
                                            (implicit isabelle: Isabelle, ec: ExecutionContext): Future[Int] =
      value.id.flatMap(isabelle.retrieveInteger(_).future)
  }

  object StringRetriever extends Retriever[String] {
    @inline override protected[MLValue] def retrieve(value: MLValue[String])
                                            (implicit isabelle: Isabelle, ec: ExecutionContext): Future[String] =
      value.id.flatMap(isabelle.retrieveString(_).future)
  }

  @inline class ListRetriever[A](a: Retriever[A]) extends Retriever[List[A]] {
    @inline override protected[MLValue] def retrieve(value: MLValue[List[A]])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[List[A]] = ???
  }

  @inline class PairRetriever[A,B](a: Retriever[A], b: Retriever[B]) extends Retriever[(A,B)] {
    @inline override protected[MLValue] def retrieve(value: MLValue[(A, B)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B)] = ???
  }

  @inline class PairStorer[A,B](a: Storer[A], b: Storer[B]) extends Storer[(A,B)] {
    @inline override protected[MLValue] def store(value: (A,B))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B)] = ???
  }

  object Implicits {
    @inline implicit val intStorer: IntStorer.type = IntStorer
    @inline implicit val stringStorer: StringStorer.type = StringStorer
    @inline implicit def listStorer[A](implicit storer: Storer[A]): ListStorer[A] = new ListStorer(storer)
    @inline implicit def pairStorer[A,B](implicit a: Storer[A], b: Storer[B]): PairStorer[A, B] = new PairStorer(a,b)
    @inline implicit val intRetriever: IntRetriever.type = IntRetriever
    @inline implicit val stringRetriever: StringRetriever.type = StringRetriever
    @inline implicit def listRetriever[A](implicit Retriever: Retriever[A]): ListRetriever[A] = new ListRetriever(Retriever)
    @inline implicit def pairRetriever[A,B](implicit a: Retriever[A], b: Retriever[B]): PairRetriever[A, B] = new PairRetriever(a,b)
  }
}