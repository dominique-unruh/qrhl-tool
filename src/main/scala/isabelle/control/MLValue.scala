package isabelle.control

import isabelle.control.MLValue.{Converter, logger}

import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.util.{Failure, Success}
import MLValue.Implicits._
import MLValue.Ops
import isabelle.control.Isabelle.ID
import org.log4s
import scalaz.Id
import scalaz.Id.Id

import scala.language.higherKinds

class MLValue[A] private[isabelle](val id: Future[Isabelle.ID]) {
  def logError(message: => String)(implicit executionContext: ExecutionContext): this.type = {
    id.onComplete {
      case Success(_) =>
      case Failure(exception) => logger.error(exception)(message)
    }
    this
  }

//  def mlValueOfItself: MLValue[MLValue[A]] = this.asInstanceOf[MLValue[MLValue[A]]]

  def debugInfo(implicit isabelle: Isabelle, ec: ExecutionContext): String = {
    Ops.debugInfo[A](this).retrieveNow
//    Ops.debugInfo.asInstanceOf[MLFunction[MLValue[A], String]].apply(mlValueOfItself).retrieveNow
  }

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

  def function[D, R](implicit ev: MLValue[A] =:= MLValue[D => R]): MLFunction[D, R] =
    new MLFunction(id)

  def function2[D1, D2, R](implicit ev: MLValue[A] =:= MLValue[((D1, D2)) => R]): MLFunction2[D1, D2, R] =
    new MLFunction2(id)

  def function3[D1, D2, D3, R](implicit ev: MLValue[A] =:= MLValue[((D1, D2, D3)) => R]): MLFunction3[D1, D2, D3, R] =
    new MLFunction3(id)

  def function4[D1, D2, D3, D4, R](implicit ev: MLValue[A] =:= MLValue[((D1, D2, D3, D4)) => R]): MLFunction4[D1, D2, D3, D4, R] =
    new MLFunction4(id)

  def function5[D1, D2, D3, D4, D5, R](implicit ev: MLValue[A] =:= MLValue[((D1, D2, D3, D4, D5)) => R]): MLFunction5[D1, D2, D3, D4, D5, R] =
    new MLFunction5(id)

  def function6[D1, D2, D3, D4, D5, D6, R](implicit ev: MLValue[A] =:= MLValue[((D1, D2, D3, D4, D5, D6)) => R]): MLFunction6[D1, D2, D3, D4, D5, D6, R] =
    new MLFunction6(id)

  def function7[D1, D2, D3, D4, D5, D6, D7, R](implicit ev: MLValue[A] =:= MLValue[((D1, D2, D3, D4, D5, D6, D7)) => R]): MLFunction7[D1, D2, D3, D4, D5, D6, D7, R] =
    new MLFunction7(id)

  /*  @deprecated("Convert to MLFunction instead (using .function)","")
      def applyOld[D, R](arg: MLValue[D])
                     (implicit ev: MLValue[A] =:= MLValue[D => R], isabelle: Isabelle, ec: ExecutionContext): MLValue[R] = {
        new MLValue(
          for (fVal <- ev(this).id;
               xVal <- arg.id;
               fx <- isabelle.applyFunction(fVal, xVal).future)
            yield fx
        )
      }*/

/*  @deprecated("Convert to MLFunction instead using .function","")
  def apply[D1, D2, R](arg1: MLValue[D1], arg2: MLValue[D2])
                      (implicit ev: MLValue[A] =:= MLValue[D1 => D2 => R], isabelle: Isabelle, ec: ExecutionContext): MLValue[R] =
    ev(this).applyOld[D1, D2 => R](arg1).applyOld[D2, R](arg2)

  @deprecated("Convert to MLFunction instead using .function","")
  def apply[D1, D2, D3, R](arg1: MLValue[D1], arg2: MLValue[D2], arg3: MLValue[D3])
                          (implicit ev: MLValue[A] =:= MLValue[D1 => D2 => D3 => R], isabelle: Isabelle, ec: ExecutionContext): MLValue[R] =
    ev(this).applyOld[D1, D2 => D3 => R](arg1).applyOld[D2, D3 => R](arg2).applyOld[D3, R](arg3)*/

  @inline def insertMLValue[C[_],B](implicit ev: A =:= C[B]): MLValue[C[MLValue[B]]] = this.asInstanceOf[MLValue[C[MLValue[B]]]]
  @inline def removeMLValue[C[_],B](implicit ev: A =:= C[MLValue[B]]): MLValue[C[B]] = this.asInstanceOf[MLValue[C[B]]]
}

class MLFunction[D,R] private[isabelle] (id: Future[ID]) extends MLValue[D => R](id) {
  def apply(arg: MLValue[D])
           (implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[R] = {
    new MLValue(
      for (fVal <- this.id;
           xVal <- arg.id;
           fx <- isabelle.applyFunction(fVal, xVal).future)
        yield fx
    )
  }

  def apply(arg: D)(implicit isabelle: Isabelle, ec: ExecutionContext, converter: Converter[D]): MLValue[R] =
    apply(MLValue(arg))
}

class MLFunction2[D1, D2, R] private[isabelle] (id: Future[ID]) extends MLFunction[(D1, D2), R](id) {
  def apply(arg1: D1, arg2: D2)
           (implicit isabelle: Isabelle, ec: ExecutionContext, converter1: Converter[D1], converter2: Converter[D2]): MLValue[R] =
    apply((arg1,arg2))
  def apply(arg1: MLValue[D1], arg2: MLValue[D2])
           (implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[R] = {
    type C1[X] = Tuple2[X,MLValue[D2]]
    type C2[X] = Tuple2[D1,X]
    apply(MLValue((arg1, arg2)).removeMLValue[C1, D1].removeMLValue[C2, D2])
  }
}

class MLFunction3[D1, D2, D3, R] private[isabelle] (id: Future[ID]) extends MLFunction[(D1, D2, D3), R](id) {
  def apply(arg1: D1, arg2: D2, arg3: D3)
           (implicit isabelle: Isabelle, ec: ExecutionContext,
            converter1: Converter[D1], converter2: Converter[D2], converter3: Converter[D3]): MLValue[R] =
    apply((arg1,arg2,arg3))
  def apply(arg1: MLValue[D1], arg2: MLValue[D2], arg3: MLValue[D3])
           (implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[R] = {
    apply(MLValue((arg1,arg2,arg3)).asInstanceOf[MLValue[(D1,D2,D3)]])
  }
}

class MLFunction4[D1, D2, D3, D4, R] private[isabelle] (id: Future[ID]) extends MLFunction[(D1, D2, D3, D4), R](id) {
  def apply(arg1: D1, arg2: D2, arg3: D3, arg4: D4)
           (implicit isabelle: Isabelle, ec: ExecutionContext,
            converter1: Converter[D1], converter2: Converter[D2], converter3: Converter[D3], converter4: Converter[D4]): MLValue[R] =
    apply((arg1,arg2,arg3,arg4))
  def apply(arg1: MLValue[D1], arg2: MLValue[D2], arg3: MLValue[D3], arg4: MLValue[D4])
           (implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[R] = {
    apply(MLValue((arg1,arg2,arg3,arg4)).asInstanceOf[MLValue[(D1,D2,D3,D4)]])
  }
}

class MLFunction5[D1, D2, D3, D4, D5, R] private[isabelle] (id: Future[ID]) extends MLFunction[(D1, D2, D3, D4, D5), R](id) {
  def apply(arg1: D1, arg2: D2, arg3: D3, arg4: D4, arg5: D5)
           (implicit isabelle: Isabelle, ec: ExecutionContext,
            converter1: Converter[D1], converter2: Converter[D2], converter3: Converter[D3], converter4: Converter[D4],
            converter5: Converter[D5]): MLValue[R] =
    apply((arg1,arg2,arg3,arg4,arg5))
  def apply(arg1: MLValue[D1], arg2: MLValue[D2], arg3: MLValue[D3], arg4: MLValue[D4], arg5: MLValue[D5])
           (implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[R] = {
    apply(MLValue((arg1,arg2,arg3,arg4,arg5)).asInstanceOf[MLValue[(D1,D2,D3,D4,D5)]])
  }
}

class MLFunction6[D1, D2, D3, D4, D5, D6, R] private[isabelle] (id: Future[ID]) extends MLFunction[(D1, D2, D3, D4, D5, D6), R](id) {
  def apply(arg1: D1, arg2: D2, arg3: D3, arg4: D4, arg5: D5, arg6: D6)
           (implicit isabelle: Isabelle, ec: ExecutionContext,
            converter1: Converter[D1], converter2: Converter[D2], converter3: Converter[D3], converter4: Converter[D4],
            converter5: Converter[D5], converter6: Converter[D6]): MLValue[R] =
    apply((arg1,arg2,arg3,arg4,arg5,arg6))
  def apply(arg1: MLValue[D1], arg2: MLValue[D2], arg3: MLValue[D3], arg4: MLValue[D4], arg5: MLValue[D5], arg6: MLValue[D6])
           (implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[R] = {
    apply(MLValue((arg1,arg2,arg3,arg4,arg5,arg6)).asInstanceOf[MLValue[(D1,D2,D3,D4,D5,D6)]])
  }
}

class MLFunction7[D1, D2, D3, D4, D5, D6, D7, R] private[isabelle] (id: Future[ID]) extends MLFunction[(D1, D2, D3, D4, D5, D6, D7), R](id) {
  def apply(arg1: D1, arg2: D2, arg3: D3, arg4: D4, arg5: D5, arg6: D6, arg7: D7)
           (implicit isabelle: Isabelle, ec: ExecutionContext,
            converter1: Converter[D1], converter2: Converter[D2], converter3: Converter[D3], converter4: Converter[D4],
            converter5: Converter[D5], converter6: Converter[D6], converter7: Converter[D7]): MLValue[R] =
    apply((arg1,arg2,arg3,arg4,arg5,arg6,arg7))
  def apply(arg1: MLValue[D1], arg2: MLValue[D2], arg3: MLValue[D3], arg4: MLValue[D4], arg5: MLValue[D5], arg6: MLValue[D6], arg7: MLValue[D7])
           (implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[R] = {
    apply(MLValue((arg1,arg2,arg3,arg4,arg5,arg6,arg7)).asInstanceOf[MLValue[(D1,D2,D3,D4,D5,D6,D7)]])
  }
}

object MLValue extends OperationCollection {
  private val logger = log4s.getLogger

  override protected def newOps(implicit isabelle: Isabelle, ec: ExecutionContext) : Ops = new Ops()
  protected[control] class Ops(implicit val isabelle: Isabelle, ec: ExecutionContext) {
    isabelle.executeMLCodeNow("exception E_List of exn list; exception E_Bool of bool; exception E_Option of exn option")

    private val optionNone_ = MLValue.compileValueRaw[Option[_]]("E_Option NONE")
    def optionNone[A]: MLValue[Option[A]] = optionNone_.asInstanceOf[MLValue[Option[A]]]
    private val optionSome_ = MLValue.compileFunctionRaw[Nothing, Option[Nothing]]("E_Option o SOME")
    def optionSome[A]: MLFunction[A, Option[A]] = optionSome_.asInstanceOf[MLFunction[A, Option[A]]]
    private val optionIsNone_ = MLValue.compileFunctionRaw[Option[Nothing], Boolean]("fn E_Option NONE => E_Bool true | E_Option _ => E_Bool false")
    def optionIsNone[A]: MLFunction[Option[A], Boolean] = optionIsNone_.asInstanceOf[MLFunction[Option[A], Boolean]]
    private val destSome_ = MLValue.compileFunctionRaw[Option[Nothing], Nothing]("fn E_Option (SOME x) => x")
    def destSome[A]: MLFunction[Option[A], A] = destSome_.asInstanceOf[MLFunction[Option[A], A]]

    private val listCons_  =
      MLValue.compileFunctionRaw[(Nothing,List[Nothing]), List[Nothing]]("fn E_Pair (x, E_List xs) => E_List (x::xs)")
        .function2[Nothing, List[Nothing], List[Nothing]]
    def listCons[A]: MLFunction2[A, List[A], List[A]] =
      listCons_.asInstanceOf[MLFunction2[A, List[A], List[A]]]
    private val listNil_ : MLValue[List[_]] = MLValue.compileValueRaw("E_List []")
    def listNil[A]: MLValue[List[A]] = listNil_.asInstanceOf[MLValue[List[A]]]
    val listIsNil_ : MLFunction[List[_], Boolean] =
      MLValue.compileFunctionRaw[List[_], Boolean]("fn E_List [] => E_Bool true | E_List _ => E_Bool false")
    def listIsNil[A]: MLFunction[List[A], Boolean] = listIsNil_.asInstanceOf[MLFunction[List[A], Boolean]]
    val destCons_ : MLFunction[List[_], (_,List[_])] = MLValue.compileFunctionRaw[List[_], (_,List[_])]("fn E_List (x::xs) => E_Pair (x, E_List xs)")
    def destCons[A]: MLFunction[List[A], (A, List[A])] = destCons_.asInstanceOf[MLFunction[List[A], (A,List[A])]]

    val boolToInt : MLFunction[Boolean, Int] = MLValue.compileFunction[Boolean, Int]("fn true => 1 | false => 0")
    val boolTrue : MLValue[Boolean] = MLValue.compileValue("true")
    val boolFalse : MLValue[Boolean] = MLValue.compileValue("false")

    val debugInfo_ : MLFunction[MLValue[Nothing], String] =
      compileFunctionRaw[MLValue[Nothing], String]("E_String o Pretty.unformatted_string_of o Runtime.pretty_exn")
    def debugInfo[A]: MLFunction[MLValue[A], String] = debugInfo_.asInstanceOf[MLFunction[MLValue[A], String]]
  }

  abstract class Converter[A] {
    def retrieve(value: MLValue[A])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[A]
    def store(value: A)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[A]
    val exnToValue : String
    val valueToExn : String
  }

  @inline def apply[A](value: A)(implicit conv: Converter[A], isabelle: Isabelle, executionContext: ExecutionContext) : MLValue[A] =
    conv.store(value)

  def compileValueRaw[A](ml: String)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[A] =
    new MLValue[A](isabelle.storeValue(ml).future).logError(s"""Error while compiling value "$ml":""")

  def compileValue[A](ml: String)(implicit isabelle: Isabelle, ec: ExecutionContext, converter: Converter[A]): MLValue[A] =
    compileValueRaw[A](s"(${converter.valueToExn}) ($ml)")

  def compileFunctionRaw[D, R](ml: String)(implicit isabelle: Isabelle, ec: ExecutionContext): MLFunction[D, R] =
    new MLFunction[D,R](isabelle.storeValue(s"E_ExnExn ($ml)").future).logError(s"""Error while compiling function "$ml":""")

  def compileFunction[D, R](ml: String)(implicit isabelle: Isabelle, ec: ExecutionContext, converterA: Converter[D], converterB: Converter[R]): MLFunction[D, R] =
    compileFunctionRaw(s"(${converterB.valueToExn}) o ($ml) o (${converterA.exnToValue})")

  def compileFunction[D1, D2, R](ml: String)
                                 (implicit isabelle: Isabelle, ec: ExecutionContext,
                                 converter1: Converter[D1], converter2: Converter[D2], converterR: Converter[R]): MLFunction2[D1, D2, R] =
    compileFunction[(D1,D2), R](ml).function2

  def compileFunction[D1, D2, D3, R](ml: String)
                                    (implicit isabelle: Isabelle, ec: ExecutionContext,
                                     converter1: Converter[D1], converter2: Converter[D2], converter3: Converter[D3], converterR: Converter[R]): MLFunction3[D1, D2, D3, R] =
    compileFunction[(D1,D2,D3), R](ml).function3

  def compileFunction[D1, D2, D3, D4, R](ml: String)
                                    (implicit isabelle: Isabelle, ec: ExecutionContext,
                                     converter1: Converter[D1], converter2: Converter[D2], converter3: Converter[D3], converter4: Converter[D4], converterR: Converter[R]): MLFunction4[D1, D2, D3, D4, R] =
    compileFunction[(D1,D2,D3,D4), R](ml).function4

  def compileFunction[D1, D2, D3, D4, D5, R](ml: String)
                                        (implicit isabelle: Isabelle, ec: ExecutionContext,
                                         converter1: Converter[D1], converter2: Converter[D2], converter3: Converter[D3],
                                         converter4: Converter[D4], converter5: Converter[D5], converterR: Converter[R]): MLFunction5[D1, D2, D3, D4, D5, R] =
    compileFunction[(D1,D2,D3,D4,D5), R](ml).function5

  def compileFunction[D1, D2, D3, D4, D5, D6, R](ml: String)
                                                (implicit isabelle: Isabelle, ec: ExecutionContext,
                                                 converter1: Converter[D1], converter2: Converter[D2], converter3: Converter[D3],
                                                 converter4: Converter[D4], converter5: Converter[D5], converter6: Converter[D6], converterR: Converter[R]): MLFunction6[D1, D2, D3, D4, D5, D6, R] =
    compileFunction[(D1,D2,D3,D4,D5,D6), R](ml).function6

  def compileFunction[D1, D2, D3, D4, D5, D6, D7, R](ml: String)
                                                    (implicit isabelle: Isabelle, ec: ExecutionContext,
                                                     converter1: Converter[D1], converter2: Converter[D2], converter3: Converter[D3],
                                                     converter4: Converter[D4], converter5: Converter[D5], converter6: Converter[D6],
                                                     converter7: Converter[D7], converterR: Converter[R]): MLFunction7[D1, D2, D3, D4, D5, D6, D7, R] =
    compileFunction[(D1,D2,D3,D4,D5,D6,D7), R](ml).function7

  object UnitConverter extends Converter[Unit] {
    override def retrieve(value: MLValue[Unit])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Unit] =
      for (_ <- value.id) yield ()

    override def store(value: Unit)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Unit] =
      new MLValue(isabelle.storeInteger(0).future)

    override val exnToValue: String = "K()"
    override val valueToExn: String = "K(E_Int 0)"
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
      for (i <- Ops.boolToInt(value).retrieve)
        yield i != 0
    override def store(value: Boolean)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Boolean] =
      if (value) Ops.boolTrue else Ops.boolFalse
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

  @inline class MLValueConverter[A] extends Converter[MLValue[A]] {
    override def retrieve(value: MLValue[MLValue[A]])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[MLValue[A]] =
      Future.successful(value.removeMLValue[Id, A])
    override def store(value: MLValue[A])(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[MLValue[A]] =
      value.insertMLValue[Id, A]
    override lazy val exnToValue: String = "fn x => x"
    override lazy val valueToExn: String = "fn x => x"
  }

  @inline class ListConverter[A](implicit converter: Converter[A]) extends Converter[List[A]] {
    @inline override def store(value: List[A])(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[List[A]] = value match {
      case Nil => Ops.listNil
      case x::xs => Ops.listCons(x, xs)
    }
    @inline override def retrieve(value: MLValue[List[A]])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[List[A]] = {
      Ops.listIsNil(value).retrieve.flatMap {
        case true => Future.successful(Nil)
        case false => for ((hd,tail) <- Ops.destCons(value).retrieve)
          yield hd::tail
      }
    }
    override lazy val exnToValue: String = s"fn E_List list => map (${converter.exnToValue}) list"
    override lazy val valueToExn: String = s"E_List o map (${converter.valueToExn})"
  }

  @inline class OptionConverter[A](implicit converter: Converter[A]) extends Converter[Option[A]] {
    @inline override def store(value: Option[A])(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Option[A]] = value match {
      case None => Ops.optionNone
      case Some(x) =>
        Ops.optionSome(x)
    }
    @inline override def retrieve(value: MLValue[Option[A]])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Option[A]] = {
      Ops.optionIsNone[A].apply(value).retrieve.flatMap {
        case true => Future.successful(None)
        case false => for (x <- Ops.destSome(value).retrieve) yield Some(x)
      }
    }
    override lazy val exnToValue: String = s"fn E_Option x => Option.map (${converter.exnToValue}) x"
    override lazy val valueToExn: String = s"E_Option o Option.map (${converter.valueToExn})"
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
    @inline override def retrieve(value: MLValue[(A, B, C)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B, C)] = {
      value.asInstanceOf[MLValue[(A,(B,C))]]
        .retrieve(tuple2Converter(a, tuple2Converter(b,c)), implicitly, implicitly)
        .map { case (a,(b,c)) => (a,b,c) }
    }
    @inline override def store(value: (A,B,C))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C)] = {
      implicit val (aI,bI,cI) = (a,b,c)
      val (aV,bV,cV) = value
      val mlvalue = MLValue((aV,(bV,cV))) (tuple2Converter(aI,implicitly), implicitly, implicitly)
      mlvalue.asInstanceOf[MLValue[(A,B,C)]]
    }
    override lazy val exnToValue: String = s"fn E_Pair (a, E_Pair (b, c)) => ((${a.exnToValue}) a, (${b.exnToValue}) b, (${c.exnToValue}) c)"
    override lazy val valueToExn: String = s"fn (a,b,c) => E_Pair ((${a.valueToExn}) a, E_Pair ((${b.valueToExn}) b, (${c.valueToExn}) c))"
  }
  @inline class Tuple4Converter[A,B,C,D](a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D]) extends Converter[(A,B,C,D)] {
    @inline override def retrieve(value: MLValue[(A, B, C, D)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D)] = {
      value.asInstanceOf[MLValue[(A,(B,(C,D)))]]
        .retrieve(tuple2Converter(a, tuple2Converter(b, tuple2Converter(c, d))), implicitly, implicitly)
        .map { case (a,(b,(c,d))) => (a,b,c,d) }
    }

    @inline override def store(value: (A,B,C,D))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D)] = {
      val (aV,bV,cV,dV) = value
      val mlvalue = MLValue((aV,(bV,(cV,dV)))) (
        tuple2Converter(a, tuple2Converter(b, tuple2Converter(c, d))),
        implicitly, implicitly)
      mlvalue.asInstanceOf[MLValue[(A,B,C,D)]]
    }
    override lazy val exnToValue: String = s"fn E_Pair (a, E_Pair (b, E_Pair (c, d))) => ((${a.exnToValue}) a, (${b.exnToValue}) b, (${c.exnToValue}) c, (${d.exnToValue}) d)"
    override lazy val valueToExn: String = s"fn (a,b,c,d) => E_Pair ((${a.valueToExn}) a, E_Pair ((${b.valueToExn}) b, E_Pair ((${c.valueToExn}) c, (${d.valueToExn}) d)))"
  }
  @inline class Tuple5Converter[A,B,C,D,E](a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E]) extends Converter[(A,B,C,D,E)] {
    @inline override def retrieve(value: MLValue[(A, B, C, D, E)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D,E)] = {
      value.asInstanceOf[MLValue[(A,(B,(C,(D,E))))]]
        .retrieve(tuple2Converter(a, tuple2Converter(b, tuple2Converter(c, tuple2Converter(d, e)))), implicitly, implicitly)
        .map { case (a,(b,(c,(d,e)))) => (a,b,c,d,e) }
    }

    @inline override def store(value: (A,B,C,D,E))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D,E)] = {
      val (aV,bV,cV,dV,eV) = value
      val mlvalue = MLValue((aV,(bV,(cV,(dV,eV))))) (
        tuple2Converter(a, tuple2Converter(b, tuple2Converter(c, tuple2Converter(d, e)))),
        implicitly, implicitly)
      mlvalue.asInstanceOf[MLValue[(A,B,C,D,E)]]
    }

    override lazy val exnToValue: String = s"fn E_Pair (a, E_Pair (b, E_Pair (c, E_Pair (d, e)))) => ((${a.exnToValue}) a, (${b.exnToValue}) b, (${c.exnToValue}) c, (${d.exnToValue}) d, (${e.exnToValue}) e)"
    override lazy val valueToExn: String = s"fn (a,b,c,d,e) => E_Pair ((${a.valueToExn}) a, E_Pair ((${b.valueToExn}) b, E_Pair ((${c.valueToExn}) c, E_Pair ((${d.valueToExn}) d, (${e.valueToExn}) e))))"
  }
  @inline class Tuple6Converter[A,B,C,D,E,F](a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E], f: Converter[F]) extends Converter[(A,B,C,D,E,F)] {
    @inline override def retrieve(value: MLValue[(A,B,C,D,E,F)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D,E,F)] = {
      value.asInstanceOf[MLValue[(A,(B,(C,(D,(E,F)))))]]
        .retrieve(tuple2Converter(a, tuple2Converter(b, tuple2Converter(c, tuple2Converter(d, tuple2Converter(e, f))))), implicitly, implicitly)
        .map { case (a,(b,(c,(d,(e,f))))) => (a,b,c,d,e,f) }
    }

    @inline override def store(value: (A,B,C,D,E,F))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D,E,F)] = {
      val (aV,bV,cV,dV,eV,fV) = value
      val mlvalue = MLValue((aV,(bV,(cV,(dV,(eV,fV)))))) (
        tuple2Converter(a, tuple2Converter(b, tuple2Converter(c, tuple2Converter(d, tuple2Converter(e, f))))),
        implicitly, implicitly)
      mlvalue.asInstanceOf[MLValue[(A,B,C,D,E,F)]]
    }

    override lazy val exnToValue: String = s"fn E_Pair (a, E_Pair (b, E_Pair (c, E_Pair (d, E_Pair (e,f))))) => ((${a.exnToValue}) a, (${b.exnToValue}) b, (${c.exnToValue}) c, (${d.exnToValue}) d, (${e.exnToValue}) e, (${f.exnToValue}) f)"
    override lazy val valueToExn: String = s"fn (a,b,c,d,e,f) => E_Pair ((${a.valueToExn}) a, E_Pair ((${b.valueToExn}) b, E_Pair ((${c.valueToExn}) c, E_Pair ((${d.valueToExn}) d, E_Pair ((${e.valueToExn}) e, (${f.valueToExn}) f)))))"
  }
  @inline class Tuple7Converter[A,B,C,D,E,F,G](a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E], f: Converter[F], g: Converter[G]) extends Converter[(A,B,C,D,E,F,G)] {
    @inline override def retrieve(value: MLValue[(A,B,C,D,E,F,G)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A,B,C,D,E,F,G)] = {
      value.asInstanceOf[MLValue[(A,(B,(C,(D,(E,(F,G))))))]]
        .retrieve(tuple2Converter(a, tuple2Converter(b, tuple2Converter(c, tuple2Converter(d, tuple2Converter(e, tuple2Converter(f, g)))))), implicitly, implicitly)
        .map { case (a,(b,(c,(d,(e,(f,g)))))) => (a,b,c,d,e,f,g) }
    }

    @inline override def store(value: (A,B,C,D,E,F,G))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D,E,F,G)] = {
      val (aV,bV,cV,dV,eV,fV,gV) = value
      val mlvalue = MLValue((aV,(bV,(cV,(dV,(eV,(fV,gV))))))) (
        tuple2Converter(a,tuple2Converter(b,tuple2Converter(c,tuple2Converter(d,tuple2Converter(e,tuple2Converter(f,g)))))),
        implicitly, implicitly)
      mlvalue.asInstanceOf[MLValue[(A,B,C,D,E,F,G)]]
    }

    override lazy val exnToValue: String = s"fn E_Pair (a, E_Pair (b, E_Pair (c, E_Pair (d, E_Pair (e, E_Pair (f, g)))))) => ((${a.exnToValue}) a, (${b.exnToValue}) b, (${c.exnToValue}) c, (${d.exnToValue}) d, (${e.exnToValue}) e, (${f.exnToValue}) f, (${g.exnToValue}) g)"
    override lazy val valueToExn: String = s"fn (a,b,c,d,e,f,g) => E_Pair ((${a.valueToExn}) a, E_Pair ((${b.valueToExn}) b, E_Pair ((${c.valueToExn}) c, E_Pair ((${d.valueToExn}) d, E_Pair ((${e.valueToExn}) e, E_Pair (${f.valueToExn}) f, (${g.valueToExn}) g))))))"
  }

  object Implicits {
    @inline implicit val booleanConverter: BooleanConverter.type = BooleanConverter
    @inline implicit val intConverter: IntConverter.type = IntConverter
    @inline implicit val unitConverter: UnitConverter.type = UnitConverter
    @inline implicit val stringConverter: StringConverter.type = StringConverter
    @inline implicit def listConverter[A](implicit converter: Converter[A]): ListConverter[A] = new ListConverter()(converter)
    @inline implicit def optionConverter[A](implicit converter: Converter[A]): OptionConverter[A] = new OptionConverter()(converter)
    @inline implicit def tuple2Converter[A,B](implicit a: Converter[A], b: Converter[B]): Tuple2Converter[A, B] = new Tuple2Converter(a,b)
    @inline implicit def tuple3Converter[A,B,C](implicit a: Converter[A], b: Converter[B], c: Converter[C]): Tuple3Converter[A, B, C] = new Tuple3Converter(a,b,c)
    @inline implicit def tuple4Converter[A,B,C,D](implicit a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D]): Tuple4Converter[A, B, C, D] = new Tuple4Converter(a,b,c,d)
    @inline implicit def tuple5Converter[A,B,C,D,E](implicit a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E]): Tuple5Converter[A, B, C, D, E] = new Tuple5Converter(a,b,c,d,e)
    @inline implicit def tuple6Converter[A,B,C,D,E,F](implicit a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E], f: Converter[F]): Tuple6Converter[A, B, C, D, E, F] = new Tuple6Converter(a,b,c,d,e,f)
    @inline implicit def tuple7Converter[A,B,C,D,E,F,G](implicit a: Converter[A], b: Converter[B], c: Converter[C], d: Converter[D], e: Converter[E], f: Converter[F], g: Converter[G]): Tuple7Converter[A,B,C,D,E,F,G] = new Tuple7Converter(a,b,c,d,e,f,g)
    @inline implicit def mlValueConverter[A]: MLValueConverter[A] = new MLValueConverter[A]
  }
}