package isabelle

import isabelle.control.MLValue.Converter
import isabelle.control.{Isabelle, MLValue}

import scala.concurrent.{ExecutionContext, Future}

final class Context private [Context](val mlValue : MLValue[Context]) {
  override def toString: String =
    if (mlValue.isReady) "context (loaded)" else "context"
}

object Context {
  private var contextFromTheory : MLValue[Theory => Context] = _
  private implicit var isabelle : Isabelle = _

  // TODO Ugly hack, fails if there are several Isabelle objects
  def init(isabelle: Isabelle): Unit = synchronized {
    if (this.isabelle == null) {
      this.isabelle = isabelle
      implicit val _ = isabelle
      Theory.init(isabelle)
      isabelle.executeMLCodeNow("exception E_Context of Proof.context")
      contextFromTheory = MLValue.compileFunction[Theory, Context]("fn (E_Theory thy) => Proof_Context.init_global thy |> E_Context")
    }
  }

  def apply(theory: Theory)(implicit ec: ExecutionContext): Context = {
    val mlCtxt : MLValue[Context] = contextFromTheory[Theory,Context](theory.mlValue)
    new Context(mlCtxt)
  }

  def apply(name: String)(implicit ec: ExecutionContext) : Context =
    Context(Theory(name))

  object ContextConverter extends Converter[Context] {
    override protected def retrieve(value: MLValue[Context])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Context] =
      Future.successful(new Context(mlValue = value))
    override protected def store(value: Context)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Context] = ???
    override lazy val exnToValue: String = ???
    override lazy val valueToExn: String = ???
  }

  object Implicits {
    implicit val contextConverter: ContextConverter.type = ContextConverter
  }
}
