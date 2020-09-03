package isabelle.control

import isabelle.control.MLValue.Converter

import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.util.{Failure, Success}

import MLValue.Implicits._

class MLValue[A] private[isabelle](val id: Future[Isabelle.ID]) {
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
  // TODO: UGLY HACK (make compatible with several instances of Isabelle, avoid need to call MLValue.init)
  private var isabelle : Isabelle = _
  private var listCons : MLValue[((_,List[_])) => List[_]] = _
  private var listNil : MLValue[List[_]] = _
  private var listIsNil : MLValue[List[_] => Boolean] = _
  private var destCons : MLValue[List[_] => (_,List[_])] = _
  private var boolToInt : MLValue[Boolean => Int] = _
  private var boolTrue : MLValue[Boolean] = _
  private var boolFalse : MLValue[Boolean] = _
  def init(isabelle: Isabelle)(implicit ec: ExecutionContext): Unit = synchronized {
    if (this.isabelle == null) {
      this.isabelle = isabelle
      implicit val isa = isabelle
      isabelle.executeMLCodeNow("exception E_List of exn list;; exception E_Bool of bool")
      listCons = MLValue.compileFunctionRaw[(_,List[_]), List[_]]("fn E_Pair (x, E_List xs) => E_List (x::xs)")
      listNil = MLValue.compileFunctionRaw[Int, List[_]]("K (E_List [])").apply[Int, List[_]](MLValue(0))
      listIsNil = MLValue.compileFunctionRaw[List[_], Boolean]("fn E_List [] => E_Bool true | E_List _ => E_Bool false")
      destCons = MLValue.compileFunctionRaw[List[_], (_,List[_])]("fn E_List (x::xs) => x")
      boolToInt = MLValue.compileFunction[Boolean, Int]("fn true => 1 | false => 0")
      val intToBool = MLValue.compileFunction[Int, Boolean]("fn 0 => false | _ => true")
      boolTrue = intToBool[Int, Boolean](MLValue(1))
      boolFalse = intToBool[Int, Boolean](MLValue(0))
    }
  }

    abstract class Converter[A] {
    def retrieve(value: MLValue[A])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[A]
    def store(value: A)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[A]
    val exnToValue : String
    val valueToExn : String
  }

  @inline def apply[A](value: A)(implicit conv: Converter[A], isabelle: Isabelle, executionContext: ExecutionContext) : MLValue[A] =
    conv.store(value)

  def compileFunctionRaw[A, B](ml: String)(implicit isabelle: Isabelle): MLValue[A => B] =
    new MLValue(isabelle.storeFunction(ml).future)

  def compileFunction[A, B](ml: String)(implicit isabelle: Isabelle, converterA: Converter[A], converterB: Converter[B]): MLValue[A => B] =
    compileFunctionRaw(s"(${converterB.valueToExn}) o ($ml) o (${converterA.exnToValue})")

  object UnitConverter extends Converter[Unit] {
    override def retrieve(value: MLValue[Unit])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Unit] =
      Future.successful(())
    override def store(value: Unit)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Unit] =
      new MLValue(isabelle.storeInteger(0).future)

    override val exnToValue: String = "(K())"
    override val valueToExn: String = "(E_Int 0)"
  }
  object IntConverter extends Converter[Int] {
    @inline override def store(value: Int)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Int] =
      new MLValue(isabelle.storeInteger(value).future)
    @inline override def retrieve(value: MLValue[Int])
                                                    (implicit isabelle: Isabelle, ec: ExecutionContext): Future[Int] =
      value.id.flatMap(isabelle.retrieveInteger(_).future)
    override lazy val exnToValue: String = "fn E_Int i => i"
    override lazy val valueToExn: String = "E_Int"
  }

  object BooleanConverter extends Converter[Boolean] {
    override def retrieve(value: MLValue[Boolean])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Boolean] =
      for (i <- boolToInt[Boolean, Int](value).retrieve)
        yield (i != 0)
    override def store(value: Boolean)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Boolean] =
      if (value) boolTrue else boolFalse
    override lazy val exnToValue: String = "fn E_Bool b => b"
    override lazy val valueToExn: String = "E_Bool"
  }

  object StringConverter extends Converter[String] {
    @inline override def store(value: String)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[String] =
      new MLValue(isabelle.storeString(value).future)
    @inline override def retrieve(value: MLValue[String])
                                                    (implicit isabelle: Isabelle, ec: ExecutionContext): Future[String] =
      value.id.flatMap(isabelle.retrieveString(_).future)
    override lazy val exnToValue: String = "fn E_String str => str"
    override lazy val valueToExn: String = "E_String"
  }

  @inline class ListConverter[A](converter: Converter[A]) extends Converter[List[A]] {
    @inline override def store(value: List[A])(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[List[A]] = ???
    @inline override def retrieve(value: MLValue[List[A]])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[List[A]] = {
      implicit val conv: Converter[A] = converter
      listIsNil.asInstanceOf[MLValue[List[A] => Boolean]].apply[List[A], Boolean](value).retrieve.flatMap {
        case true => Future.successful(Nil)
        case false => for ((hd,tail) <- destCons.asInstanceOf[MLValue[List[A] => (A,List[A])]].apply[List[A], (A,List[A])](value).retrieve)
          yield hd::tail
      }
    }
    override lazy val exnToValue: String = s"fn E_List list => map (${converter.exnToValue}) list"
    override lazy val valueToExn: String = s"E_List o map (${converter.valueToExn})"
  }

  @inline class Tuple2Converter[A,B](converterA: Converter[A], converterB: Converter[B]) extends Converter[(A,B)] {
    @inline override def retrieve(value: MLValue[(A, B)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B)] = {
      val aIDbID = for (id <- value.id; ab <- isabelle.splitPair(id).future) yield ab
      val aID = for ((a, _) <- aIDbID) yield a
      val bID = for ((_, b) <- aIDbID) yield b
      val a = converterA.retrieve(new MLValue[A](aID))
      val b = converterB.retrieve(new MLValue[B](bID))
      for (x <- a; y <- b) yield (x, y)
    }
    @inline override def store(value: (A,B))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B)] = {
      val (a,b) = value
      val mlA = converterA.store(a)
      val mlB = converterB.store(b)
      val idAB1 =
        for (aID <- mlA.id;
             bID <- mlB.id)
          yield isabelle.makePair(aID, bID).future
      val idAB = idAB1.flatten
      new MLValue(idAB)
    }

    override lazy val exnToValue: String = s"fn E_Pair (a,b) => ((${converterA.exnToValue}) a, (${converterB.exnToValue}) b)"
    override lazy val valueToExn: String = s"fn (a,b) => E_Pair ((${converterA.valueToExn}) a, (${converterB.valueToExn}) b)"
  }
  @inline class Tuple3Converter[A,B,C](a: Converter[A], b: Converter[B], c: Converter[C]) extends Converter[(A,B,C)] {
    @inline override def retrieve(value: MLValue[(A, B, C)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B, C)] = ???
    @inline override def store(value: (A,B,C))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C)] = ???
    override lazy val exnToValue: String = "fn E_Pair (x, E_Pair (y, z)) => (x,y,z)"
    override lazy val valueToExn: String = ???
  }
  @inline class Tuple4Converter[A,B,C,D](a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D]) extends Converter[(A,B,C,D)] {
    @inline override def retrieve(value: MLValue[(A, B, C, D)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D)] = ???
    @inline override def store(value: (A,B,C,D))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D)] = ???
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }
  @inline class Tuple5Converter[A,B,C,D,E](a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E]) extends Converter[(A,B,C,D,E)] {
    @inline override def retrieve(value: MLValue[(A, B, C, D, E)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D,E)] = ???
    @inline override def store(value: (A,B,C,D,E))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D,E)] = ???
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }
  @inline class Tuple6Converter[A,B,C,D,E,F](a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E], f: Converter[F]) extends Converter[(A,B,C,D,E,F)] {
    @inline override def retrieve(value: MLValue[(A,B,C,D,E,F)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D,E,F)] = ???
    @inline override def store(value: (A,B,C,D,E,F))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D,E,F)] = ???
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }
  @inline class Tuple7Converter[A,B,C,D,E,F,G](a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E], f: Converter[F], g: Converter[G]) extends Converter[(A,B,C,D,E,F,G)] {
    @inline override def retrieve(value: MLValue[(A,B,C,D,E,F,G)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D,E,F,G)] = ???
    @inline override def store(value: (A,B,C,D,E,F,G))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D,E,F,G)] = ???
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
    @inline implicit def tuple7Converter[A,B,C,D,E,F,G](implicit a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E], f: Converter[F], g: Converter[G]): Tuple7Converter[A,B,C,D,E,F,G] = new Tuple7Converter(a,b,c,d,e,f,g)
  }
}