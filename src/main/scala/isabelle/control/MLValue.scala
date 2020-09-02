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

  @inline class Tuple2Retriever[A,B](a: Retriever[A], b: Retriever[B]) extends Retriever[(A,B)] {
    @inline override protected[MLValue] def retrieve(value: MLValue[(A, B)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B)] = ???
  }
  @inline class Tuple3Retriever[A,B,C](a: Retriever[A], b: Retriever[B], c: Retriever[C]) extends Retriever[(A,B,C)] {
    @inline override protected[MLValue] def retrieve(value: MLValue[(A, B, C)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B, C)] = ???
  }
  @inline class Tuple4Retriever[A,B,C,D](a: Retriever[A], b: Retriever[B], c: Retriever[C], d: Retriever[D]) extends Retriever[(A,B,C,D)] {
    @inline override protected[MLValue] def retrieve(value: MLValue[(A, B, C, D)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D)] = ???
  }
  @inline class Tuple5Retriever[A,B,C,D,E](a: Retriever[A], b: Retriever[B], c: Retriever[C], d: Retriever[D], e: Retriever[E]) extends Retriever[(A,B,C,D,E)] {
    @inline override protected[MLValue] def retrieve(value: MLValue[(A, B, C, D, E)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D,E)] = ???
  }
  @inline class Tuple6Retriever[A,B,C,D,E,F](a: Retriever[A], b: Retriever[B], c: Retriever[C], d: Retriever[D], e: Retriever[E], f: Retriever[F]) extends Retriever[(A,B,C,D,E,F)] {
    @inline override protected[MLValue] def retrieve(value: MLValue[(A,B,C,D,E,F)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D,E,F)] = ???
  }

  @inline class Tuple2Storer[A,B](a: Storer[A], b: Storer[B]) extends Storer[(A,B)] {
    @inline override protected[MLValue] def store(value: (A,B))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B)] = ???
  }

  @inline class Tuple3Storer[A,B,C](a: Storer[A], b: Storer[B], c: Storer[C]) extends Storer[(A,B,C)] {
    @inline override protected[MLValue] def store(value: (A,B,C))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C)] = ???
  }

  @inline class Tuple4Storer[A,B,C,D](a: Storer[A], b: Storer[B], c: Storer[C], d: Storer[D]) extends Storer[(A,B,C,D)] {
    @inline override protected[MLValue] def store(value: (A,B,C,D))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D)] = ???
  }

  @inline class Tuple5Storer[A,B,C,D,E](a: Storer[A], b: Storer[B], c: Storer[C], d: Storer[D], e: Storer[E]) extends Storer[(A,B,C,D,E)] {
    @inline override protected[MLValue] def store(value: (A,B,C,D,E))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D,E)] = ???
  }

  @inline class Tuple6Storer[A,B,C,D,E,F](a: Storer[A], b: Storer[B], c: Storer[C], d: Storer[D], e: Storer[E], f: Storer[F]) extends Storer[(A,B,C,D,E,F)] {
    @inline override protected[MLValue] def store(value: (A,B,C,D,E,F))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D,E,F)] = ???
  }

  object Implicits {
    @inline implicit val intStorer: IntStorer.type = IntStorer
    @inline implicit val stringStorer: StringStorer.type = StringStorer
    @inline implicit def listStorer[A](implicit storer: Storer[A]): ListStorer[A] = new ListStorer(storer)
    @inline implicit def tuple2Storer[A,B](implicit a: Storer[A], b: Storer[B]): Tuple2Storer[A, B] = new Tuple2Storer(a,b)
    @inline implicit def tuple3Storer[A,B,C](implicit a: Storer[A], b: Storer[B], c: Storer[C]): Tuple3Storer[A, B, C] = new Tuple3Storer(a,b,c)
    @inline implicit def tuple4Storer[A,B,C,D](implicit a: Storer[A], b: Storer[B], c: Storer[C], d: Storer[D]): Tuple4Storer[A, B, C, D] = new Tuple4Storer(a,b,c,d)
    @inline implicit def tuple5Storer[A,B,C,D,E](implicit a: Storer[A], b: Storer[B], c: Storer[C], d: Storer[D], e: Storer[E]): Tuple5Storer[A, B, C, D, E] = new Tuple5Storer(a,b,c,d,e)
    @inline implicit def tuple6Storer[A,B,C,D,E,F](implicit a: Storer[A], b: Storer[B], c: Storer[C], d: Storer[D], e: Storer[E], f: Storer[F]): Tuple6Storer[A, B, C, D, E, F] = new Tuple6Storer(a,b,c,d,e,f)
    @inline implicit val intRetriever: IntRetriever.type = IntRetriever
    @inline implicit val stringRetriever: StringRetriever.type = StringRetriever
    @inline implicit def listRetriever[A](implicit Retriever: Retriever[A]): ListRetriever[A] = new ListRetriever(Retriever)
    @inline implicit def tuple2Retriever[A,B](implicit a: Retriever[A], b: Retriever[B]): Tuple2Retriever[A, B] = new Tuple2Retriever(a,b)
    @inline implicit def tuple3Retriever[A,B,C](implicit a: Retriever[A], b: Retriever[B], c: Retriever[C]): Tuple3Retriever[A,B,C] = new Tuple3Retriever(a,b,c)
    @inline implicit def tuple4Retriever[A,B,C,D](implicit a: Retriever[A], b: Retriever[B], c: Retriever[C], d: Retriever[D]): Tuple4Retriever[A,B,C,D] = new Tuple4Retriever(a,b,c,d)
    @inline implicit def tuple5Retriever[A,B,C,D,E](implicit a: Retriever[A], b: Retriever[B], c: Retriever[C], d: Retriever[D], e: Retriever[E]): Tuple5Retriever[A,B,C,D,E] = new Tuple5Retriever(a,b,c,d,e)
    @inline implicit def tuple6Retriever[A,B,C,D,E,F](implicit a: Retriever[A], b: Retriever[B], c: Retriever[C], d: Retriever[D], e: Retriever[E], f: Retriever[F]): Tuple6Retriever[A,B,C,D,E,F] = new Tuple6Retriever(a,b,c,d,e,f)
  }
}