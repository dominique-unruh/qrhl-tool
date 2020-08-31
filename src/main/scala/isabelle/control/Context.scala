package isabelle.control

import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}

final class Context private [Context] (val mlValue : MLValue[Context]) {
  override def toString: String =
    if (mlValue.isReady) "context (loaded)" else "context"
}

object Context {
  private var contextFromTheory : MLValue[Theory => Context] = _
  private implicit var isabelle : Isabelle = _

  // TODO Ugly hack, fails if there are several Isabelle objects
  def init(isabelle: Isabelle): Unit = synchronized {
    if (contextFromTheory == null) {
      Theory.init(isabelle)
      implicit val _ = isabelle
      isabelle.executeMLCodeNow("exception E_Context of Proof.context")
      contextFromTheory = MLValue.compileFunction[Theory, Context]("fn (E_Theory thy) => Proof_Context.init_global thy |> E_Context")
      this.isabelle = isabelle
    }
  }

  def apply(theory: Theory)(implicit ec: ExecutionContext): Context = {
    val mlCtxt : MLValue[Context] = contextFromTheory[Theory,Context](theory.mlValue)
    new Context(mlCtxt)
  }

  def apply(name: String)(implicit ec: ExecutionContext) : Context =
    Context(Theory(name))
}

object ContextTest {
  def main(args: Array[String]): Unit = {
    implicit val ec: ExecutionContextExecutor = ExecutionContext.global
    val isabelle = new Isabelle()
    Context.init(isabelle)
    val ctxt = Context("QRHL.QRHL")
    println(ctxt)
    Thread.sleep(1000)
    println(ctxt)
    Thread.sleep(1000)
  }
}