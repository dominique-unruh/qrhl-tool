package isabelle

import isabelle.control.MLValue.Converter
import isabelle.control.{Isabelle, MLFunction, MLValue}

import scala.concurrent.{ExecutionContext, Future}

final class Context private [Context](val mlValue : MLValue[Context]) {
  override def toString: String =
    if (mlValue.isReady) "context (loaded)" else "context"
}

object Context {
  private[isabelle] class Ops(implicit val isabelle: Isabelle, ec: ExecutionContext) {
    import MLValue.compileFunctionRaw
    Theory.init(isabelle)
    isabelle.executeMLCodeNow("exception E_Context of Proof.context")
    val contextFromTheory : MLFunction[Theory, Context] =
      compileFunctionRaw[Theory, Context]("fn (E_Theory thy) => Proof_Context.init_global thy |> E_Context")
  }

  var Ops : Ops = _

  // TODO Ugly hack, fails if there are several Isabelle objects
  def init(isabelle: Isabelle)(implicit ec: ExecutionContext): Unit = synchronized {
    if (Ops == null)
      Ops = new Ops()(isabelle, ec)
  }

  def apply(theory: Theory)(implicit isabelle: Isabelle, ec: ExecutionContext): Context = {
    val mlCtxt : MLValue[Context] = Ops.contextFromTheory(theory.mlValue)
    new Context(mlCtxt)
  }

  def apply(name: String)(implicit isabelle: Isabelle, ec: ExecutionContext) : Context =
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
