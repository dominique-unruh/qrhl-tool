package isabelle.mlvalue

import isabelle.control.Isabelle.{DInt, DObject, DString, DTree, Data, ID}
import isabelle.control.{Isabelle, OperationCollection}
import isabelle.mlvalue.MLValue.Implicits.{booleanConverter, intConverter, longConverter, listConverter,
  mlValueConverter, stringConverter, optionConverter,
  tuple2Converter, tuple3Converter, tuple4Converter, tuple5Converter, tuple6Converter, tuple7Converter}
import MLValue.{Converter, Ops, logger, matchFailData}
import org.log4s
import scalaz.Id.Id

import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.util.{Failure, Success}

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
           fx <- isabelle.applyFunctionOld(fVal, xVal))
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

class MLStoreFunction[A](val id: Future[ID]) {
  def apply(data: Data)(implicit isabelle: Isabelle, ec: ExecutionContext, converter: Converter[A]): MLValue[A] =
    new MLValue(isabelle.applyFunction(this.id, data).map { case DObject(id) => id})
  def apply(data: Future[Data])(implicit isabelle: Isabelle, ec: ExecutionContext, converter: Converter[A]): MLValue[A] =
    new MLValue(for (data <- data; DObject(id) <- isabelle.applyFunction(this.id, data)) yield id)
}

object MLStoreFunction {
  def apply[A](ml: String)(implicit isabelle: Isabelle, converter: Converter[A]) : MLStoreFunction[A] =
    new MLStoreFunction(isabelle.storeValue(s"E_Function (D_Object o (${converter.valueToExn}) o ($ml))"))
}

class MLRetrieveFunction[A](val id: Future[ID]) {
  def apply(id: ID)(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Isabelle.Data] =
    isabelle.applyFunction(this.id, DObject(id))
  def apply(id: Future[ID])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Isabelle.Data] =
    for (id <- id; data <- apply(id)) yield data
  def apply(value: MLValue[A])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Data] =
    apply(value.id)
}
object MLRetrieveFunction {
  def apply[A](ml: String)(implicit isabelle: Isabelle, converter: Converter[A]) : MLRetrieveFunction[A] =
    new MLRetrieveFunction(isabelle.storeValue(s"E_Function (fn D_Object x => ($ml) ((${converter.exnToValueProtected}) x))"))
}

object MLValue extends OperationCollection {
  def matchFailExn(name: String) =
    s""" exn => error ("Match failed in ML code generated for $name: " ^ string_of_exn exn)"""

  def matchFailData(name: String) =
    s""" data => error ("Match failed in ML code generated for $name: " ^ string_of_data data)"""

  private val logger = log4s.getLogger

  override protected def newOps(implicit isabelle: Isabelle, ec: ExecutionContext) : Ops = new Ops()
  //noinspection TypeAnnotation
  protected[mlvalue] class Ops(implicit val isabelle: Isabelle, ec: ExecutionContext) {
    isabelle.executeMLCodeNow("exception E_List of exn list; exception E_Bool of bool; exception E_Option of exn option")

    val unitValue = MLValue.compileValueRaw[Unit]("E_Int 0")

    val retrieveTuple2 =
      MLRetrieveFunction[(MLValue[Nothing], MLValue[Nothing])]("fn (a,b) => D_Tree [D_Object a, D_Object b]")
    /*@inline def retrieveTuple2[A,B]: MLRetrieveFunction[(MLValue[A], MLValue[B])] =
      retrieveTuple2_.asInstanceOf[MLRetrieveFunction[(MLValue[A], MLValue[B])]]*/
    private val storeTuple2_ =
      MLStoreFunction[(MLValue[Nothing], MLValue[Nothing])](s"fn D_Tree [D_Object a, D_Object b] => (a,b) | ${matchFailData("storeTuple2")}")
    @inline def storeTuple2[A,B]: MLStoreFunction[(MLValue[A], MLValue[B])] =
      storeTuple2_.asInstanceOf[MLStoreFunction[(MLValue[A], MLValue[B])]]

    val retrieveTuple3: MLRetrieveFunction[(MLValue[Nothing], MLValue[Nothing], MLValue[Nothing])] =
      MLRetrieveFunction[(MLValue[Nothing], MLValue[Nothing], MLValue[Nothing])](s"fn (a,b,c) => D_Tree [D_Object a, D_Object b, D_Object c]")
    private val storeTuple3_ =
      MLStoreFunction[(MLValue[Nothing], MLValue[Nothing], MLValue[Nothing])](s"fn D_Tree [D_Object a, D_Object b, D_Object c] => (a,b,c) | ${matchFailData("storeTuple3")}")
    @inline def storeTuple3[A,B,C]: MLStoreFunction[(MLValue[A], MLValue[B], MLValue[C])] =
      storeTuple3_.asInstanceOf[MLStoreFunction[(MLValue[A], MLValue[B], MLValue[C])]]

    val retrieveTuple4: MLRetrieveFunction[(MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing])] =
      MLRetrieveFunction(s"fn (a,b,c,d) => D_Tree [D_Object a, D_Object b, D_Object c, D_Object d]")
    private val storeTuple4_ =
      MLStoreFunction[(MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing])](s"fn D_Tree [D_Object a, D_Object b, D_Object c, D_Object d] => (a,b,c,d) | ${matchFailData("storeTuple4")}")
    @inline def storeTuple4[A,B,C,D] =
      storeTuple4_.asInstanceOf[MLStoreFunction[(MLValue[A], MLValue[B], MLValue[C], MLValue[D])]]

    val retrieveTuple5: MLRetrieveFunction[(MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing])] =
      MLRetrieveFunction(s"fn (a,b,c,d,e) => D_Tree [D_Object a, D_Object b, D_Object c, D_Object d, D_Object e]")
    private val storeTuple5_ =
      MLStoreFunction[(MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing])](
        s"fn D_Tree [D_Object a, D_Object b, D_Object c, D_Object d, D_Object e] => (a,b,c,d,e) | ${matchFailData("storeTuple5")}")
    @inline def storeTuple5[A,B,C,D,E] =
      storeTuple5_.asInstanceOf[MLStoreFunction[(MLValue[A], MLValue[B], MLValue[C], MLValue[D], MLValue[E])]]

    val retrieveTuple6: MLRetrieveFunction[(MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing])] =
      MLRetrieveFunction(s"fn (a,b,c,d,e,f) => D_Tree [D_Object a, D_Object b, D_Object c, D_Object d, D_Object e, D_Object f]")
    private val storeTuple6_ =
      MLStoreFunction[(MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing])](
        s"fn D_Tree [D_Object a, D_Object b, D_Object c, D_Object d, D_Object e, D_Object f] => (a,b,c,d,e,f) | ${matchFailData("storeTuple6")}")
    @inline def storeTuple6[A,B,C,D,E,F] =
      storeTuple6_.asInstanceOf[MLStoreFunction[(MLValue[A], MLValue[B], MLValue[C], MLValue[D], MLValue[E], MLValue[F])]]

    val retrieveTuple7: MLRetrieveFunction[(MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing])] =
      MLRetrieveFunction(s"fn (a,b,c,d,e,f,g) => D_Tree [D_Object a, D_Object b, D_Object c, D_Object d, D_Object e, D_Object f, D_Object g]")
    private val storeTuple7_ =
      MLStoreFunction[(MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing], MLValue[Nothing])](
        s"fn D_Tree [D_Object a, D_Object b, D_Object c, D_Object d, D_Object e, D_Object f, D_Object g] => (a,b,c,d,e,f,g) | ${matchFailData("storeTuple7")}")
    @inline def storeTuple7[A,B,C,D,E,F,G] =
      storeTuple7_.asInstanceOf[MLStoreFunction[(MLValue[A], MLValue[B], MLValue[C], MLValue[D], MLValue[E], MLValue[F], MLValue[G])]]

    val retrieveInt = MLRetrieveFunction[Int]("D_Int")
    val storeInt = MLStoreFunction[Int]("fn D_Int i => i")
    val retrieveLong = MLRetrieveFunction[Long]("D_Int")
    val storeLong = MLStoreFunction[Long]("fn D_Int i => i")

    val retrieveString: MLRetrieveFunction[String] = MLRetrieveFunction[String]("D_String")
    val storeString: MLStoreFunction[String] = MLStoreFunction[String]("fn D_String str => str")

//    val boolToInt : MLFunction[Boolean, Int] = MLValue.compileFunction[Boolean, Int]("fn true => 1 | false => 0")
    val boolTrue : MLValue[Boolean] = MLValue.compileValue("true")
    val boolFalse : MLValue[Boolean] = MLValue.compileValue("false")
    val retrieveBool : MLRetrieveFunction[Boolean] =
      MLRetrieveFunction("fn true => D_Int 1 | false => D_Int 0")

    private val optionNone_ = MLValue.compileValueRaw[Option[_]]("E_Option NONE")
    def optionNone[A]: MLValue[Option[A]] = optionNone_.asInstanceOf[MLValue[Option[A]]]
    private val optionSome_ = MLValue.compileFunctionRaw[Nothing, Option[Nothing]]("E_Option o SOME")
    def optionSome[A]: MLFunction[A, Option[A]] = optionSome_.asInstanceOf[MLFunction[A, Option[A]]]
    val retrieveOption : MLRetrieveFunction[Option[MLValue[Nothing]]] =
      MLRetrieveFunction("fn NONE => D_Tree [] | SOME x => D_Tree [D_Object x]")


    val retrieveList : MLRetrieveFunction[List[MLValue[Nothing]]] =
      MLRetrieveFunction("D_Tree o map D_Object")
    val storeList : MLStoreFunction[List[MLValue[Nothing]]] =
      MLStoreFunction(s"fn D_Tree list => map (fn D_Object obj => obj | ${matchFailData("storeList.map")}) list | ${matchFailData("storeList")}")

/*    private val listCons_  =
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
    def destCons[A]: MLFunction[List[A], (A, List[A])] = destCons_.asInstanceOf[MLFunction[List[A], (A,List[A])]]*/

    val debugInfo_ : MLFunction[MLValue[Nothing], String] =
      compileFunctionRaw[MLValue[Nothing], String]("E_String o string_of_exn")
    def debugInfo[A]: MLFunction[MLValue[A], String] = debugInfo_.asInstanceOf[MLFunction[MLValue[A], String]]
  }

  abstract class Converter[A] {
    def retrieve(value: MLValue[A])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[A]
    def store(value: A)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[A]
    val exnToValue : String
    val valueToExn : String
    final def exnToValueProtected = s"""fn e => (($exnToValue) e handle Match => error ("Match failed in exnToValue (" ^ string_of_exn e ^ ")"))"""
  }

  @inline def apply[A](value: A)(implicit conv: Converter[A], isabelle: Isabelle, executionContext: ExecutionContext) : MLValue[A] =
    conv.store(value)

  def compileValueRaw[A](ml: String)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[A] =
    new MLValue[A](isabelle.storeValue(ml)).logError(s"""Error while compiling value "$ml":""")

  def compileValue[A](ml: String)(implicit isabelle: Isabelle, ec: ExecutionContext, converter: Converter[A]): MLValue[A] =
    compileValueRaw[A](s"(${converter.valueToExn}) ($ml)")

  def compileFunctionRaw[D, R](ml: String)(implicit isabelle: Isabelle, ec: ExecutionContext): MLFunction[D, R] =
    new MLFunction[D,R](isabelle.storeValue(s"E_Function (fn D_Object x => ($ml) x |> D_Object)")).logError(s"""Error while compiling function "$ml":""")

  def compileFunction[D, R](ml: String)(implicit isabelle: Isabelle, ec: ExecutionContext, converterA: Converter[D], converterB: Converter[R]): MLFunction[D, R] =
    compileFunctionRaw(s"(${converterB.valueToExn}) o ($ml) o (${converterA.exnToValueProtected})")

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

    override def store(value: Unit)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Unit] = {
      Ops.unitValue
    }

    override val exnToValue: String = "K()"
    override val valueToExn: String = "K(E_Int 0)"
  }
  object IntConverter extends Converter[Int] {
    @inline override def store(value: Int)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Int] =
      Ops.storeInt(DInt(value))
    @inline override def retrieve(value: MLValue[Int])
                                 (implicit isabelle: Isabelle, ec: ExecutionContext): Future[Int] =
      for (DInt(i) <- Ops.retrieveInt(value.id)) yield i.toInt

    override lazy val exnToValue: String = s"fn E_Int i => i | ${matchFailExn("IntConverter.exnToValue")}"
    override lazy val valueToExn: String = "E_Int"
  }
  object LongConverter extends Converter[Long] {
    @inline override def store(value: Long)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Long] =
      Ops.storeLong(DInt(value))
    @inline override def retrieve(value: MLValue[Long])
                                 (implicit isabelle: Isabelle, ec: ExecutionContext): Future[Long] =
      for (DInt(i) <- Ops.retrieveLong(value.id)) yield i
    override lazy val exnToValue: String = s"fn E_Int i => i | ${matchFailExn("LongConverter.exnToValue")}"
    override lazy val valueToExn: String = "E_Int"
  }

  object BooleanConverter extends Converter[Boolean] {
    override def retrieve(value: MLValue[Boolean])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Boolean] =
      for (DInt(i) <- Ops.retrieveBool(value))
        yield i != 0
    override def store(value: Boolean)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Boolean] =
      if (value) Ops.boolTrue else Ops.boolFalse
    override lazy val exnToValue: String = s"fn E_Bool b => b | ${matchFailExn("BooleanConverter.exnToValue")}"
    override lazy val valueToExn: String = "E_Bool"
  }

  object StringConverter extends Converter[String] {
    @inline override def store(value: String)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[String] =
      Ops.storeString(DString(value))

    @inline override def retrieve(value: MLValue[String])
                                 (implicit isabelle: Isabelle, ec: ExecutionContext): Future[String] =
      for (DString(str) <- Ops.retrieveString(value.id))
        yield str

    override lazy val exnToValue: String = s"fn E_String str => str | ${matchFailExn("BooleanConverter.exnToValue")}"
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
    @inline override def store(value: List[A])(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[List[A]] = {
      val listID : Future[List[ID]] = Future.traverse(value) { converter.store(_).id }
      val data : Future[Data] = for (listID <- listID) yield DTree(listID map DObject :_*)
      val result : MLValue[List[MLValue[Nothing]]] = Ops.storeList(data)
      result.asInstanceOf[MLValue[List[A]]]
    }
    @inline override def retrieve(value: MLValue[List[A]])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[List[A]] = {
      for (DTree(listObj@_*) <- Ops.retrieveList(value.asInstanceOf[MLValue[List[MLValue[Nothing]]]]);
           listMLValue = listObj map { case DObject(id) => new MLValue[A](Future.successful(id)) };
           list <- Future.traverse(listMLValue) { converter.retrieve(_) })
        yield list.toList
    }
    override lazy val exnToValue: String = s"fn E_List list => map (${converter.exnToValue}) list | ${matchFailExn("ListConverter.exnToValue")}"
    override lazy val valueToExn: String = s"E_List o map (${converter.valueToExn})"
  }

  @inline class OptionConverter[A](implicit converter: Converter[A]) extends Converter[Option[A]] {
    @inline override def store(value: Option[A])(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Option[A]] = value match {
      case None => Ops.optionNone
      case Some(x) =>
        Ops.optionSome(x)
    }
    @inline override def retrieve(value: MLValue[Option[A]])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Option[A]] = {
      for (data <- Ops.retrieveOption(value.id);
           option <- data match {
             case DTree() => Future.successful(None) : Future[Option[A]]
             case DTree(DObject(id)) => converter.retrieve(new MLValue[A](Future.successful(id))).map(Some(_)) : Future[Option[A]]
           })
        yield option
    }
    override lazy val exnToValue: String = s"fn E_Option x => Option.map (${converter.exnToValue}) x | ${matchFailExn("OptionConverter.exnToValue")}"
    override lazy val valueToExn: String = s"E_Option o Option.map (${converter.valueToExn})"
  }

  @inline class Tuple2Converter[A,B](converterA: Converter[A], converterB: Converter[B]) extends Converter[(A,B)] {
    @inline override def retrieve(value: MLValue[(A, B)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B)] = {
      for (DTree(DObject(aID), DObject(bID)) <- Ops.retrieveTuple2(value.id);
           a <- converterA.retrieve(new MLValue[A](Future.successful(aID)));
           b <- converterB.retrieve(new MLValue[B](Future.successful(bID))))
        yield (a,b)
    }
    @inline override def store(value: (A,B))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B)] = {
      val (a,b) = value
      val mlA = converterA.store(a)
      val mlB = converterB.store(b)
      Ops.storeTuple2[A,B](for (idA <- mlA.id; idB <- mlB.id) yield (DTree(DObject(idA), DObject(idB))))
        .asInstanceOf[MLValue[(A,B)]]
    }

    override lazy val exnToValue: String = s"fn E_Pair (a,b) => ((${converterA.exnToValue}) a, (${converterB.exnToValue}) b) | ${MLValue.matchFailExn("Tuple2Converter.exnToValue")}"
    override lazy val valueToExn: String = s"fn (a,b) => E_Pair ((${converterA.valueToExn}) a, (${converterB.valueToExn}) b)"
  }
  
  @inline class Tuple3Converter[A,B,C](converterA: Converter[A], converterB: Converter[B], converterC: Converter[C]) extends Converter[(A,B,C)] {
    @inline override def retrieve(value: MLValue[(A, B, C)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B, C)] = {
      for (DTree(DObject(aID), DObject(bID), DObject(cID)) <- Ops.retrieveTuple3(value.id);
           a <- converterA.retrieve(new MLValue[A](Future.successful(aID)));
           b <- converterB.retrieve(new MLValue[B](Future.successful(bID)));
           c <- converterC.retrieve(new MLValue[C](Future.successful(cID))))
        yield (a,b,c)
    }
    @inline override def store(value: (A,B,C))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C)] = {
      val (a,b,c) = value
      val mlA = converterA.store(a)
      val mlB = converterB.store(b)
      val mlC = converterC.store(c)
      Ops.storeTuple3[A,B,C](for (idA <- mlA.id; idB <- mlB.id; idC <- mlC.id) yield (DTree(DObject(idA), DObject(idB), DObject(idC))))
        .asInstanceOf[MLValue[(A,B,C)]]
    }
    override lazy val exnToValue: String = s"fn E_Pair (a, E_Pair (b, c)) => ((${converterA.exnToValue}) a, (${converterB.exnToValue}) b, (${converterC.exnToValue}) c)"
    override lazy val valueToExn: String = s"fn (a,b,c) => E_Pair ((${converterA.valueToExn}) a, E_Pair ((${converterB.valueToExn}) b, (${converterC.valueToExn}) c))"
  }
  @inline class Tuple4Converter[A,B,C,D](converterA: Converter[A], converterB: Converter[B], converterC: Converter[C], converterD: Converter[D]) extends Converter[(A,B,C,D)] {
    @inline override def retrieve(value: MLValue[(A, B, C, D)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B, C, D)] = {
      for (DTree(DObject(aID), DObject(bID), DObject(cID), DObject(dID)) <- Ops.retrieveTuple4(value.id);
           a <- converterA.retrieve(new MLValue[A](Future.successful(aID)));
           b <- converterB.retrieve(new MLValue[B](Future.successful(bID)));
           c <- converterC.retrieve(new MLValue[C](Future.successful(cID)));
           d <- converterD.retrieve(new MLValue[D](Future.successful(dID))))
        yield (a,b,c,d)
    }
    @inline override def store(value: (A,B,C,D))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D)] = {
      val (a,b,c,d) = value
      val mlA = converterA.store(a)
      val mlB = converterB.store(b)
      val mlC = converterC.store(c)
      val mlD = converterD.store(d)
      Ops.storeTuple4[A,B,C,D](for (idA <- mlA.id; idB <- mlB.id; idC <- mlC.id; idD <- mlD.id) yield (DTree(DObject(idA), DObject(idB), DObject(idC), DObject(idD))))
        .asInstanceOf[MLValue[(A,B,C,D)]]
    }

    override lazy val exnToValue: String = s"fn E_Pair (a, E_Pair (b, E_Pair (c, d))) => ((${converterA.exnToValue}) a, (${converterB.exnToValue}) b, (${converterC.exnToValue}) c, (${converterD.exnToValue}) d)"
    override lazy val valueToExn: String = s"fn (a,b,c,d) => E_Pair ((${converterA.valueToExn}) a, E_Pair ((${converterB.valueToExn}) b, E_Pair ((${converterC.valueToExn}) c, (${converterD.valueToExn}) d)))"
  }
  @inline class Tuple5Converter[A,B,C,D,E](converterA: Converter[A], converterB: Converter[B], converterC: Converter[C], converterD: Converter[D], converterE: Converter[E])
    extends Converter[(A,B,C,D,E)] {
    @inline override def retrieve(value: MLValue[(A, B, C, D, E)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B, C, D, E)] = {
      for (DTree(DObject(aID), DObject(bID), DObject(cID), DObject(dID), DObject(eID)) <- Ops.retrieveTuple5(value.id);
           a <- converterA.retrieve(new MLValue[A](Future.successful(aID)));
           b <- converterB.retrieve(new MLValue[B](Future.successful(bID)));
           c <- converterC.retrieve(new MLValue[C](Future.successful(cID)));
           d <- converterD.retrieve(new MLValue[D](Future.successful(dID)));
           e <- converterE.retrieve(new MLValue[E](Future.successful(eID))))
        yield (a,b,c,d,e)
    }
    @inline override def store(value: (A,B,C,D,E))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D,E)] = {
      val (a,b,c,d,e) = value
      val mlA = converterA.store(a)
      val mlB = converterB.store(b)
      val mlC = converterC.store(c)
      val mlD = converterD.store(d)
      val mlE = converterE.store(e)
      Ops.storeTuple5[A,B,C,D,E](for (idA <- mlA.id; idB <- mlB.id; idC <- mlC.id; idD <- mlD.id; idE <- mlE.id)
        yield (DTree(DObject(idA), DObject(idB), DObject(idC), DObject(idD), DObject(idE))))
        .asInstanceOf[MLValue[(A,B,C,D,E)]]
    }

    override lazy val exnToValue: String = s"fn E_Pair (a, E_Pair (b, E_Pair (c, E_Pair (d, e)))) => ((${converterA.exnToValue}) a, (${converterB.exnToValue}) b, (${converterC.exnToValue}) c, (${converterD.exnToValue}) d, (${converterE.exnToValue}) e)"
    override lazy val valueToExn: String = s"fn (a,b,c,d,e) => E_Pair ((${converterA.valueToExn}) a, E_Pair ((${converterB.valueToExn}) b, E_Pair ((${converterC.valueToExn}) c, E_Pair ((${converterD.valueToExn}) d, (${converterE.valueToExn}) e))))"
  }
  @inline class Tuple6Converter[A,B,C,D,E,F](converterA: Converter[A], converterB: Converter[B], converterC: Converter[C], converterD: Converter[D],
                                             converterE: Converter[E], converterF: Converter[F]) extends Converter[(A,B,C,D,E,F)] {
    @inline override def retrieve(value: MLValue[(A, B, C, D, E, F)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B, C, D, E, F)] = {
      for (DTree(DObject(aID), DObject(bID), DObject(cID), DObject(dID), DObject(eID), DObject(fID)) <- Ops.retrieveTuple6(value.id);
           a <- converterA.retrieve(new MLValue[A](Future.successful(aID)));
           b <- converterB.retrieve(new MLValue[B](Future.successful(bID)));
           c <- converterC.retrieve(new MLValue[C](Future.successful(cID)));
           d <- converterD.retrieve(new MLValue[D](Future.successful(dID)));
           e <- converterE.retrieve(new MLValue[E](Future.successful(eID)));
           f <- converterF.retrieve(new MLValue[F](Future.successful(fID))))
        yield (a,b,c,d,e,f)
    }
    @inline override def store(value: (A,B,C,D,E,F))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D,E,F)] = {
      val (a,b,c,d,e,f) = value
      val mlA = converterA.store(a)
      val mlB = converterB.store(b)
      val mlC = converterC.store(c)
      val mlD = converterD.store(d)
      val mlE = converterE.store(e)
      val mlF = converterF.store(f)
      Ops.storeTuple6[A,B,C,D,E,F](for (idA <- mlA.id; idB <- mlB.id; idC <- mlC.id; idD <- mlD.id; idE <- mlE.id; idF <- mlF.id)
        yield (DTree(DObject(idA), DObject(idB), DObject(idC), DObject(idD), DObject(idE), DObject(idF))))
        .asInstanceOf[MLValue[(A,B,C,D,E,F)]]
    }

    override lazy val exnToValue: String = s"fn E_Pair (a, E_Pair (b, E_Pair (c, E_Pair (d, E_Pair (e,f))))) => ((${converterA.exnToValue}) a, (${converterB.exnToValue}) b, (${converterC.exnToValue}) c, (${converterD.exnToValue}) d, (${converterE.exnToValue}) e, (${converterF.exnToValue}) f)"
    override lazy val valueToExn: String = s"fn (a,b,c,d,e,f) => E_Pair ((${converterA.valueToExn}) a, E_Pair ((${converterB.valueToExn}) b, E_Pair ((${converterC.valueToExn}) c, E_Pair ((${converterD.valueToExn}) d, E_Pair ((${converterE.valueToExn}) e, (${converterF.valueToExn}) f)))))"
  }
  @inline class Tuple7Converter[A,B,C,D,E,F,G](converterA: Converter[A], converterB: Converter[B], converterC: Converter[C],
                                               converterD: Converter[D], converterE: Converter[E], converterF: Converter[F],
                                               converterG: Converter[G]) extends Converter[(A,B,C,D,E,F,G)] {
    @inline override def retrieve(value: MLValue[(A, B, C, D, E, F, G)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B, C, D, E, F, G)] = {
      for (DTree(DObject(aID), DObject(bID), DObject(cID), DObject(dID), DObject(eID), DObject(fID), DObject(gID)) <- Ops.retrieveTuple7(value.id);
           a <- converterA.retrieve(new MLValue[A](Future.successful(aID)));
           b <- converterB.retrieve(new MLValue[B](Future.successful(bID)));
           c <- converterC.retrieve(new MLValue[C](Future.successful(cID)));
           d <- converterD.retrieve(new MLValue[D](Future.successful(dID)));
           e <- converterE.retrieve(new MLValue[E](Future.successful(eID)));
           f <- converterF.retrieve(new MLValue[F](Future.successful(fID)));
           g <- converterG.retrieve(new MLValue[G](Future.successful(gID))))
        yield (a,b,c,d,e,f,g)
    }
    @inline override def store(value: (A,B,C,D,E,F,G))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A,B,C,D,E,F,G)] = {
      val (a,b,c,d,e,f,g) = value
      val mlA = converterA.store(a)
      val mlB = converterB.store(b)
      val mlC = converterC.store(c)
      val mlD = converterD.store(d)
      val mlE = converterE.store(e)
      val mlF = converterF.store(f)
      val mlG = converterG.store(g)
      Ops.storeTuple7[A,B,C,D,E,F,G](for (idA <- mlA.id; idB <- mlB.id; idC <- mlC.id; idD <- mlD.id; idE <- mlE.id; idF <- mlF.id; idG <- mlG.id)
        yield (DTree(DObject(idA), DObject(idB), DObject(idC), DObject(idD), DObject(idE), DObject(idF), DObject(idG))))
        .asInstanceOf[MLValue[(A,B,C,D,E,F,G)]]
    }

    override lazy val exnToValue: String = s"fn E_Pair (a, E_Pair (b, E_Pair (c, E_Pair (d, E_Pair (e, E_Pair (f, g)))))) => ((${converterA.exnToValue}) a, (${converterB.exnToValue}) b, (${converterC.exnToValue}) c, (${converterD.exnToValue}) d, (${converterE.exnToValue}) e, (${converterF.exnToValue}) f, (${converterG.exnToValue}) g)"
    override lazy val valueToExn: String = s"fn (a,b,c,d,e,f,g) => E_Pair ((${converterA.valueToExn}) a, E_Pair ((${converterB.valueToExn}) b, E_Pair ((${converterC.valueToExn}) c, E_Pair ((${converterD.valueToExn}) d, E_Pair ((${converterE.valueToExn}) e, E_Pair ((${converterF.valueToExn}) f, (${converterG.valueToExn}) g))))))"
  }

  object Implicits {
    @inline implicit val booleanConverter: BooleanConverter.type = BooleanConverter
    @inline implicit val intConverter: IntConverter.type = IntConverter
    @inline implicit val longConverter: LongConverter.type = LongConverter
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
