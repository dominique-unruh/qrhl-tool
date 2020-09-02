package isabelle

import isabelle.control.{Isabelle, MLValue}

import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}

import MLValue.Implicits._

final class Theory private [Theory](val name: String, val mlValue : MLValue[Theory]) {
  override def toString: String = s"theory $name${if (mlValue.isReady) " (loaded)" else ""}"
}

object Theory {
  private var loadTheory : MLValue[String => Theory] = _
  private implicit var isabelle : Isabelle = _

  // TODO Ugly hack, fails if there are several Isabelle objects
  def init(isabelle: Isabelle): Unit = synchronized {
    if (this.isabelle == null) {
      this.isabelle = isabelle
      implicit val _ = isabelle
      isabelle.executeMLCodeNow("exception E_Theory of theory")
      loadTheory = MLValue.compileFunction[String, Theory]("fn (E_String name) => (Thy_Info.use_thy name; Thy_Info.get_theory name |> E_Theory)")
    }
  }

  def apply(name: String)(implicit ec: ExecutionContext): Theory = {
    val mlName = MLValue(name)
    val mlThy : MLValue[Theory] = loadTheory[String,Theory](mlName)
    new Theory(name, mlThy)
  }
}
