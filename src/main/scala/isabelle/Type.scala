package isabelle

import isabelle.control.{Isabelle, MLValue}

import scala.annotation.tailrec
import scala.concurrent.{ExecutionContext, Future}
import MLValue.Implicits._
import Typ.Implicits._
import isabelle.control.MLValue.Converter

sealed abstract class Typ {
  val mlValue : MLValue[Typ]
  implicit val isabelle : Isabelle
  def pretty(ctxt: Context)(implicit ec: ExecutionContext): String =
    Typ.stringOfType[Context,Typ,String](ctxt.mlValue, mlValue).retrieveNow
  val concrete : Typ

  def -->:(that: Typ)(implicit ec: ExecutionContext): Type = Type("fun", that, this)
//  def --->:(thats: List[Typ])(implicit ec: ExecutionContext): Typ = thats.foldRight(this)(_ -->: _)

  override def equals(that: Any): Boolean = (this, that) match {
    case (t1, t2: AnyRef) if t1 eq t2 => true
    case (t1: Type, t2: Type) => t1.name == t2.name && t1.args == t2.args
    case (t1: TVar, t2: TVar) => ???
    case (t1: TFree, t2: TFree) => ???
    case (t1: MLValueTyp, t2: Typ) =>
      import ExecutionContext.Implicits.global
      if (t1.concreteComputed)
        t1.concrete == t2
      else
        Typ.equalsTyp[(Typ,Typ), Boolean](MLValue((t1,t2))).retrieveNow
    case (t1: Typ, t2: MLValueTyp) => ???
    case _ => false
  }
}

final class MLValueTyp(val mlValue: MLValue[Typ])(implicit val isabelle: Isabelle, ec: ExecutionContext) extends Typ {
  def concreteComputed: Boolean = concreteLoaded
  @volatile private var concreteLoaded = false

  lazy val concrete : Typ = {
    val typ = Typ.whatTyp[Typ,Int](mlValue).retrieveNow match {
      case 1 =>
        val (name,args) = Typ.destType[Typ, (String,List[Typ])](mlValue).retrieveNow
        new Type(name, args.toList, mlValue)
      case 2 => ??? // TFree
      case 3 => ??? // TVar
    }
    concreteLoaded = true
    typ
  }

  override def toString: String =
    if (concreteLoaded) concrete.toString
    else s"‹term${mlValue.stateString}›"
}

final class Type private[isabelle] (val name: String, val args: List[Typ], val initialMlValue: MLValue[Typ]=null)
                                  (implicit val isabelle: Isabelle, ec: ExecutionContext) extends Typ {
  lazy val mlValue : MLValue[Typ] =
    if (initialMlValue!=null) initialMlValue
    else Typ.makeType[(String,List[Typ]),Typ](MLValue(name,args))
  @inline override val concrete: Type = this
  override def toString: String =
    if (args.isEmpty) name
    else s"$name(${args.mkString(", ")})"
}

object Type {
  def apply(name: String, args: Typ*)(implicit isabelle: Isabelle, ec: ExecutionContext) = new Type(name, args.toList)

  @tailrec
  def unapply(typ: Typ): Option[(String, List[Typ])] = typ match {
    case typ : Type => Some((typ.name,typ.args))
    case typ : MLValueTyp => unapply(typ.concrete)
    case _ => None
  }
}

final class TFree private (val name: String, val sort: List[String], val initialMlValue: MLValue[Typ]=null)(implicit val isabelle: Isabelle) extends Typ {
  lazy val mlValue : MLValue[Typ] = if (initialMlValue!=null) initialMlValue else ???
  @inline override val concrete: TFree = this
  override def toString: String = sort match {
    case List(clazz) => s"$name::$clazz"
    case _ => s"$name::{${sort.mkString(",")}}"
  }
}

object TFree {
  def apply(name: String, sort: String*)(implicit isabelle: Isabelle) = new TFree(name, sort.toList)

  @tailrec
  def unapply(typ: Typ): Option[(String, List[String])] = typ match {
    case typ : TFree => Some((typ.name,typ.sort))
    case typ : MLValueTyp => unapply(typ.concrete)
    case _ => None
  }
}

final class TVar private (val name: String, val index: Int, val sort: List[String], val initialMlValue: MLValue[Typ]=null)(implicit val isabelle: Isabelle) extends Typ {
  lazy val mlValue : MLValue[Typ] = if (initialMlValue!=null) initialMlValue else ???
  @inline override val concrete: TVar = this
  override def toString: String = sort match {
    case List(clazz) => s"?$name$index::$clazz"
    case _ => s"?$name$index::{${sort.mkString(",")}}"
  }
}

object TVar {
  def apply(name: String, index: Int, sort: String*)(implicit isabelle: Isabelle) = new TVar(name, index, sort.toList)

  @tailrec
  def unapply(typ: Typ): Option[(String, Int, List[String])] = typ match {
    case typ : TVar => Some((typ.name,typ.index,typ.sort))
    case typ : MLValueTyp => unapply(typ.concrete)
    case _ => None
  }
}

object Typ {
  private implicit var isabelle: Isabelle = _
  private var readType: MLValue[Context => String => Typ] = _
  private var stringOfType: MLValue[Context => Typ => String] = _
  private[isabelle] var makeType: MLValue[((String, List[Typ])) => Typ] = _
  private[isabelle] var whatTyp: MLValue[Typ => Int] = _
  private[isabelle] var destType: MLValue[Typ => (String, List[Typ])] = _
  private var equalsTyp: MLValue[((Typ,Typ)) => Boolean] = _

  // TODO Ugly hack, fails if there are several Isabelle objects
  def init(isabelle: Isabelle)(implicit ec: ExecutionContext): Unit = synchronized {
    if (this.isabelle == null) {
      this.isabelle = isabelle
      implicit val _ = isabelle
      Context.init(isabelle)
      isabelle.executeMLCodeNow("exception E_Typ of typ") // ;; exception E_TypList of typ list
      readType = MLValue.compileFunctionRaw[Context, String => Typ]("fn (E_Context ctxt) => E_ExnExn (fn (E_String str) => Syntax.read_typ ctxt str |> E_Typ)")
      stringOfType = MLValue.compileFunctionRaw[Context, Typ => String]("fn (E_Context ctxt) => E_ExnExn (fn (E_Typ typ) => Syntax.string_of_typ ctxt typ |> E_String)")
      whatTyp = MLValue.compileFunctionRaw[Typ, Int]("fn (E_Typ typ) => (case typ of Type _ => 1 | TFree _ => 2 | TVar _ => 3) |> E_Int")
      destType = MLValue.compileFunction[Typ, (String, List[Typ])]("Term.dest_Type")
      makeType = MLValue.compileFunction[(String, List[Typ]), Typ]("Term.Type")
      equalsTyp = MLValue.compileFunction[(Typ,Typ), Boolean]("op=")
    }
  }

  def apply(context: Context, string: String)(implicit ec: ExecutionContext): MLValueTyp = {
    new MLValueTyp(readType[Context, String, Typ](context.mlValue, MLValue(string)))
  }

  object TypConverter extends Converter[Typ] {
    override def retrieve(value: MLValue[Typ])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Typ] =
      Future.successful(new MLValueTyp(mlValue = value))
    override def store(value: Typ)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Typ] =
      value.mlValue
    override lazy val exnToValue: String = "fn E_Typ typ => typ"
    override lazy val valueToExn: String = "E_Typ"
  }

  object Implicits {
    implicit val typConverter: TypConverter.type = TypConverter
  }
}

