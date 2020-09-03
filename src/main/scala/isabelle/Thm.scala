package isabelle

import isabelle.control.{Isabelle, MLValue}

import scala.concurrent.{ExecutionContext, ExecutionContextExecutor, Future}
import MLValue.Implicits._
import isabelle.control.MLValue.Converter

final class Thm private [Thm](val mlValue : MLValue[Thm])(implicit ec: ExecutionContext, isabelle: Isabelle) {
  override def toString: String = s"thm${mlValue.stateString}"
  lazy val cterm : CTerm = CTerm(Thm.cpropOf[Thm,CTerm](mlValue))
  def pretty(ctxt: Context)(implicit ec: ExecutionContext): String =
    Thm.stringOfThm[Context,Thm,String](ctxt.mlValue, mlValue).retrieveNow
}

object Thm {
  private var getThm : MLValue[Context => String => Thm] = _
  private var cpropOf : MLValue[Thm => CTerm] = _
  private var stringOfThm: MLValue[Context => Thm => String] = _
  private implicit var isabelle : Isabelle = _

  // TODO Ugly hack, fails if there are several Isabelle objects
  def init(isabelle: Isabelle)(implicit ec: ExecutionContext): Unit = synchronized {
    if (this.isabelle == null) {
      this.isabelle = isabelle
      implicit val _ = isabelle
      Term.init(isabelle)
      isabelle.executeMLCodeNow("exception E_Thm of thm")
      getThm = MLValue.compileFunction[Context, String => Thm]("fn (E_Context ctxt) => E_ExnExn (fn (E_String name) => Proof_Context.get_thm ctxt name |> E_Thm)")
      cpropOf = MLValue.compileFunction[Thm, CTerm]("fn (E_Thm thm) => Thm.cprop_of thm |> E_CTerm")
      stringOfThm = MLValue.compileFunction[Context, Thm => String]("fn (E_Context ctxt) => E_ExnExn (fn (E_Thm thm) => Thm.string_of_thm ctxt thm |> E_String)")
    }
  }

  def apply(context: Context, name: String)(implicit ec: ExecutionContext): Thm = {
    val mlName = MLValue(name)
    val mlThm : MLValue[Thm] = getThm[Context,String,Thm](context.mlValue, mlName)
    new Thm(mlThm)
  }

  object ThmConverter extends Converter[Thm] {
    override protected def retrieve(value: MLValue[Thm])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Thm] =
      Future.successful(new Thm(mlValue = value))
    override protected def store(value: Thm)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Thm] = ???
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }

  object Implicits {
    implicit val thmConverter: ThmConverter.type = ThmConverter
  }
}

