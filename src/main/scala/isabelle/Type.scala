package isabelle

import isabelle.control.{Isabelle, MLValue}

import scala.annotation.tailrec
import scala.concurrent.ExecutionContext

sealed abstract class Typ {
  val mlValue : MLValue[Typ]
  implicit val isabelle : Isabelle
  def pretty(ctxt: Context)(implicit ec: ExecutionContext): String =
    Typ.stringOfType[Context,Typ,String](ctxt.mlValue, mlValue).retrieveNow
  val concrete : Typ
}

final class MLValueTyp(val mlValue: MLValue[Typ])(implicit val isabelle: Isabelle, ec: ExecutionContext) extends Typ {
  lazy val concrete : Typ =
    Typ.whatType[Typ,Int](mlValue).retrieveNow match {
      case 1 =>
        val name = Typ.typeName[Typ, String](mlValue).retrieveNow
        val numArgs = Typ.numArgs[Typ,Int](mlValue).retrieveNow
        println(s"Type name: $name, numArgs: $numArgs")
        val args = for (i <- 0 until numArgs) yield new MLValueTyp(Typ.getArg[Typ,Int,Typ](mlValue,MLValue(i)))
        new Type(name, args.toList, mlValue)
      case 2 => ??? // TFree
      case 3 => ??? // TVar
    }

  // TODO: should check if concrete has already been loaded, and if so, print the concrete type
  override def toString: String = s"‹type${mlValue.stateString}›"
}

final class Type private[isabelle] (val name: String, val args: List[Typ], val initialMlValue: MLValue[Typ]=null)
                                  (implicit val isabelle: Isabelle, ec: ExecutionContext) extends Typ {
  lazy val mlValue : MLValue[Typ] =
    if (initialMlValue!=null) initialMlValue
    else Typ.makeType[String,List[Typ],Typ](MLValue(name),Typ.makeTypList(args))
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
  }
}

object Typ {
  private implicit var isabelle: Isabelle = _
  private var readType: MLValue[Context => String => Typ] = _
  private var stringOfType: MLValue[Context => Typ => String] = _
  private var typeListNil: MLValue[List[Typ]] = _
  private var typeListCons: MLValue[Typ => List[Typ] => List[Typ]] = _
  private[isabelle] var makeType: MLValue[String => List[Typ] => Typ] = _
  private[isabelle] var whatType: MLValue[Typ => Int] = _
  private[isabelle] var numArgs: MLValue[Typ => Int] = _
  private[isabelle] var typeName: MLValue[Typ => String] = _
  private[isabelle] var getArg: MLValue[Typ => Int => Typ] = _

  // TODO Ugly hack, fails if there are several Isabelle objects
  def init(isabelle: Isabelle)(implicit ec: ExecutionContext): Unit = synchronized {
    if (this.isabelle == null) {
      this.isabelle = isabelle
      implicit val _ = isabelle
      Context.init(isabelle)
      isabelle.executeMLCodeNow("exception E_Typ of typ;; exception E_TypList of typ list")
      readType = MLValue.compileFunction[Context, String => Typ]("fn (E_Context ctxt) => E_ExnExn (fn (E_String str) => Syntax.read_typ ctxt str |> E_Typ)")
      stringOfType = MLValue.compileFunction[Context, Typ => String]("fn (E_Context ctxt) => E_ExnExn (fn (E_Typ typ) => Syntax.string_of_typ ctxt typ |> E_String)")
      whatType = MLValue.compileFunction[Typ, Int]("fn (E_Typ typ) => (case typ of Type _ => 1 | TFree _ => 2 | TVar _ => 3) |> E_Int")
      typeName = MLValue.compileFunction[Typ, String]("fn (E_Typ typ) => (case typ of Type (name,_) => name | TFree (name,_) => name | TVar ((name,_),_) => name) |> E_String")
      numArgs = MLValue.compileFunction[Typ, Int]("fn (E_Typ typ) => (case typ of Type (_,args) => length args | TFree (_,sort) => length sort | TVar (_,sort) => length sort) |> E_Int")
      getArg = MLValue.compileFunction[Typ, Int => Typ]("fn (E_Typ (Type (_,args))) => E_ExnExn (fn (E_Int i) => nth args i |> E_Typ)")
      typeListNil = MLValue.compileFunction[Int, List[Typ]]("fn _ => E_TypList []").apply[Int, List[Typ]](MLValue(0))
      typeListCons = MLValue.compileFunction[Typ, List[Typ] => List[Typ]]("fn (E_Typ typ) => E_ExnExn (fn (E_TypList typs) => E_TypList (typ::typs))")
      makeType = MLValue.compileFunction[String, List[Typ] => Typ]("fn (E_String name) => E_ExnExn (fn (E_TypList typs) => E_Typ (Type(name,typs)))")
    }
  }

  def makeTypList(typs: List[Typ])(implicit ec: ExecutionContext) : MLValue[List[Typ]] = typs match {
    case Nil => typeListNil
    case typ::typs =>
      val typsMLVal = makeTypList(typs)
      typeListCons[Typ, List[Typ], List[Typ]](typ.mlValue, typsMLVal)
  }


  def apply(context: Context, string: String)(implicit ec: ExecutionContext): MLValueTyp = {
//    implicit val _ = =:=.tpEquals[MLValue[Context => String => Typ]]
    new MLValueTyp(readType[Context, String, Typ](context.mlValue, MLValue(string)))
  }
}

object TestType {
  import ExecutionContext.Implicits.global

  def main(args: Array[String]): Unit = {
    implicit val isabelle : Isabelle = new Isabelle
    Typ.init(isabelle)
    val ctxt = Context("Main")
    val typ = Typ(ctxt, "nat list")
    typ match {
      case Type(listName,List(Type(natName,List()))) => println(s"XXXX ${(listName, natName)}")

    }

    println("****",typ.pretty(ctxt))
    val typ2 = typ.concrete.asInstanceOf[Type]
    println("****", typ2)
    val typ3 = typ2.args.head.concrete
    println("****", typ3.pretty(ctxt))
  }
}
