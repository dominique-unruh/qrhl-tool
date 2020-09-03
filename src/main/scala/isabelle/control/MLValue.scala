package isabelle.control

import cats.Show
import isabelle.control.MLValue.Converter

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

  @inline def retrieve(implicit converter: Converter[A], isabelle: Isabelle, ec: ExecutionContext): Future[A] =
    converter.retrieve(this)

  @inline def retrieveNow(implicit converter: Converter[A], isabelle: Isabelle, ec: ExecutionContext): A =
    Await.result(retrieve, Duration.Inf)

  @inline def retrieveOrElse(default: => A)(implicit converter: Converter[A], isabelle: Isabelle, ec: ExecutionContext): Future[A] =
    retrieve.recover { case _ => default }
  @inline def retrieveNowOrElse(default: => A)(implicit converter: Converter[A], isabelle: Isabelle, ec: ExecutionContext): A =
    Await.result(retrieveOrElse(default), Duration.Inf)

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

  abstract class Converter[A] {
    protected[MLValue] def retrieve(value: MLValue[A])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[A]
    protected[MLValue] def store(value: A)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[A]
    val exnToValue : String
    val valueToExn : String
  }

  @inline def apply[A](value: A)(implicit conv: Converter[A], isabelle: Isabelle, executionContext: ExecutionContext) : MLValue[A] =
    conv.store(value)

  // TODO: Automatically add wrapping and unwrapping of exceptions
  def compileFunction[A, B](ml: String)(implicit isabelle: Isabelle): MLValue[A => B] =
    new MLValue(isabelle.storeFunction(ml).future)

  object UnitConverter extends Converter[Unit] {
    override protected[MLValue] def retrieve(value: MLValue[Unit])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Unit] =
      Future.successful(())
    override protected[MLValue] def store(value: Unit)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Unit] =
      new MLValue(isabelle.storeInteger(0).future)

    override val exnToValue: String = "(K())"
    override val valueToExn: String = "(E_Int 0)"
  }
  object IntConverter extends Converter[Int] {
    @inline override protected[MLValue] def store(value: Int)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Int] =
      new MLValue(isabelle.storeInteger(value).future)
    @inline override protected[MLValue] def retrieve(value: MLValue[Int])
                                                    (implicit isabelle: Isabelle, ec: ExecutionContext): Future[Int] =
      value.id.flatMap(isabelle.retrieveInteger(_).future)
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }

  object BooleanConverter extends Converter[Boolean] {
    override protected[MLValue] def retrieve(value: MLValue[Boolean])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Boolean] = ???
    override protected[MLValue] def store(value: Boolean)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Boolean] = ???
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }

  object StringConverter extends Converter[String] {
    @inline override protected[MLValue] def store(value: String)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[String] =
      new MLValue(isabelle.storeString(value).future)
    @inline override protected[MLValue] def retrieve(value: MLValue[String])
                                                    (implicit isabelle: Isabelle, ec: ExecutionContext): Future[String] =
      value.id.flatMap(isabelle.retrieveString(_).future)
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }

  @inline class ListConverter[A](storer: Converter[A]) extends Converter[List[A]] {
    @inline override protected[MLValue] def store(value: List[A])(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[List[A]] = ???
    @inline override protected[MLValue] def retrieve(value: MLValue[List[A]])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[List[A]] = ???
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }

  @inline class Tuple2Converter[A,B](a: Converter[A], b: Converter[B]) extends Converter[(A,B)] {
    @inline override protected[MLValue] def retrieve(value: MLValue[(A, B)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B)] = ???
    @inline override protected[MLValue] def store(value: (A,B))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B)] = ???
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }
  @inline class Tuple3Converter[A,B,C](a: Converter[A], b: Converter[B], c: Converter[C]) extends Converter[(A,B,C)] {
    @inline override protected[MLValue] def retrieve(value: MLValue[(A, B, C)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B, C)] = ???
    @inline override protected[MLValue] def store(value: (A,B,C))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C)] = ???
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }
  @inline class Tuple4Converter[A,B,C,D](a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D]) extends Converter[(A,B,C,D)] {
    @inline override protected[MLValue] def retrieve(value: MLValue[(A, B, C, D)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D)] = ???
    @inline override protected[MLValue] def store(value: (A,B,C,D))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D)] = ???
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }
  @inline class Tuple5Converter[A,B,C,D,E](a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E]) extends Converter[(A,B,C,D,E)] {
    @inline override protected[MLValue] def retrieve(value: MLValue[(A, B, C, D, E)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D,E)] = ???
    @inline override protected[MLValue] def store(value: (A,B,C,D,E))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D,E)] = ???
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }
  @inline class Tuple6Converter[A,B,C,D,E,F](a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E], f: Converter[F]) extends Converter[(A,B,C,D,E,F)] {
    @inline override protected[MLValue] def retrieve(value: MLValue[(A,B,C,D,E,F)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D,E,F)] = ???
    @inline override protected[MLValue] def store(value: (A,B,C,D,E,F))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D,E,F)] = ???
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }

  object Implicits {
    @inline implicit val booleanConverter: BooleanConverter.type = BooleanConverter
    @inline implicit val intConverter: IntConverter.type = IntConverter
    @inline implicit val unitConverter: UnitConverter.type = UnitConverter
    @inline implicit val stringConverter: StringConverter.type = StringConverter
    @inline implicit def listConverter[A](implicit Converter: Converter[A]): ListConverter[A] = new ListConverter(Converter)
    @inline implicit def tuple2Converter[A,B](implicit a: Converter[A], b: Converter[B]): Tuple2Converter[A, B] = new Tuple2Converter(a,b)
    @inline implicit def tuple3Converter[A,B,C](implicit a: Converter[A], b: Converter[B], c: Converter[C]): Tuple3Converter[A, B, C] = new Tuple3Converter(a,b,c)
    @inline implicit def tuple4Converter[A,B,C,D](implicit a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D]): Tuple4Converter[A, B, C, D] = new Tuple4Converter(a,b,c,d)
    @inline implicit def tuple5Converter[A,B,C,D,E](implicit a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E]): Tuple5Converter[A, B, C, D, E] = new Tuple5Converter(a,b,c,d,e)
    @inline implicit def tuple6Converter[A,B,C,D,E,F](implicit a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E], f: Converter[F]): Tuple6Converter[A, B, C, D, E, F] = new Tuple6Converter(a,b,c,d,e,f)
  }
}