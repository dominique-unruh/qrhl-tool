package isabelle

import isabelle.control.{Isabelle, MLFunction, MLValue}

import scala.concurrent.{ExecutionContext, ExecutionContextExecutor, Future}
import MLValue.Implicits._
import Thm.Implicits._
import Cterm.Implicits._
import Context.Implicits._
import isabelle.control.MLValue.Converter

final class Thm private [Thm](val mlValue : MLValue[Thm])(implicit ec: ExecutionContext, isabelle: Isabelle) {
  override def toString: String = s"thm${mlValue.stateString}"
  lazy val cterm : Cterm = Cterm(Thm.cpropOf(mlValue))
  def pretty(ctxt: Context)(implicit ec: ExecutionContext): String =
    Thm.stringOfThm(MLValue(ctxt, this)).retrieveNow
}

object Thm {
  private var getThm : MLFunction[(Context, String), Thm] = _
  private var cpropOf : MLFunction[Thm, Cterm] = _
  private var stringOfThm: MLFunction[(Context, Thm), String] = _
  private implicit var isabelle : Isabelle = _

  // TODO Ugly hack, fails if there are several Isabelle objects
  def init(isabelle: Isabelle)(implicit ec: ExecutionContext): Unit = synchronized {
    if (this.isabelle == null) {
      this.isabelle = isabelle
      implicit val _ = isabelle
      Term.init(isabelle)
      isabelle.executeMLCodeNow("exception E_Thm of thm")
      getThm = MLValue.compileFunction[(Context, String), Thm]("fn (ctxt, name) => Proof_Context.get_thm ctxt name")
      cpropOf = MLValue.compileFunction[Thm, Cterm]("Thm.cprop_of")
      stringOfThm = MLValue.compileFunction[(Context, Thm), String]("fn (ctxt, thm) => Thm.string_of_thm ctxt thm")
    }
  }

  def apply(context: Context, name: String)(implicit ec: ExecutionContext): Thm = {
    val mlThm : MLValue[Thm] = getThm(MLValue((context, name)))
    new Thm(mlThm)
  }

  object ThmConverter extends Converter[Thm] {
    override def retrieve(value: MLValue[Thm])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Thm] =
      for (_ <- value.id)
        yield new Thm(mlValue = value)
    override def store(value: Thm)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Thm] =
      value.mlValue
    override val exnToValue: String = "fn E_Thm thm => thm"
    override val valueToExn: String = "E_Thm"
  }

  object Implicits {
    implicit val thmConverter: ThmConverter.type = ThmConverter
  }
}

