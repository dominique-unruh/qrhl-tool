package isabelle

import isabelle.control.MLValue.Converter
import isabelle.control.{Isabelle, MLFunction, MLValue}

import scala.concurrent.{ExecutionContext, Future}

final class Context private [Context](val mlValue : MLValue[Context]) {
  override def toString: String =
    if (mlValue.isReady) "context (loaded)" else "context"
}

object Context {
  private var contextFromTheory : MLFunction[Theory, Context] = _
  private implicit var isabelle : Isabelle = _

  // TODO Ugly hack, fails if there are several Isabelle objects
  def init(isabelle: Isabelle)(implicit ec: ExecutionContext): Unit = synchronized {
    if (this.isabelle == null) {
      this.isabelle = isabelle
      implicit val _ = isabelle
      Theory.init(isabelle)
      isabelle.executeMLCodeNow("exception E_Context of Proof.context")
      contextFromTheory = MLValue.compileFunctionRaw[Theory, Context]("fn (E_Theory thy) => Proof_Context.init_global thy |> E_Context")
    }
  }

  def apply(theory: Theory)(implicit ec: ExecutionContext): Context = {
    val mlCtxt : MLValue[Context] = contextFromTheory(theory.mlValue)
    new Context(mlCtxt)
  }

  def apply(name: String)(implicit ec: ExecutionContext) : Context =
    Context(Theory(name))

  object ContextConverter extends Converter[Context] {
    override def retrieve(value: MLValue[Context])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Context] = {
      for (_ <- value.id)
        yield new Context(mlValue = value)
    }

    override def store(value: Context)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Context] =
      value.mlValue
    override lazy val exnToValue: String = "fn E_Context ctxt => ctxt"
    override lazy val valueToExn: String = "E_Context"
  }

  object Implicits {
    implicit val contextConverter: ContextConverter.type = ContextConverter
  }
}
