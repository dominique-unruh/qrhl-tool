package isabelle

import isabelle.control.{Isabelle, MLValue}

import scala.concurrent.{ExecutionContext, ExecutionContextExecutor, Future}
import isabelle.control.MLValue.Converter

// Implicits
import MLValue.Implicits._
import Theory.Implicits._

final class Theory private [Theory](val name: String, val mlValue : MLValue[Theory]) {
  override def toString: String = s"theory $name${if (mlValue.isReady) " (loaded)" else ""}"
  def importMLStructure(name: String, newName: String)
                       (implicit isabelle: Isabelle, executionContext: ExecutionContext): Unit =
    Theory.importMLStructure[(Theory,String,String), Unit](MLValue((this, name, newName))).retrieveNow
}

object Theory {
  private var loadTheory : MLValue[String => Theory] = _
  private var importMLStructure : MLValue[((Theory,String,String)) => Unit] = _
  private implicit var isabelle : Isabelle = _

  // TODO Ugly hack, fails if there are several Isabelle objects
  def init(isabelle: Isabelle)(implicit ec: ExecutionContext): Unit = synchronized {
    if (this.isabelle == null) {
      this.isabelle = isabelle
      implicit val _ = isabelle
      MLValue.init(isabelle)
      isabelle.executeMLCodeNow("exception E_Theory of theory")
      loadTheory = MLValue.compileFunction[String, Theory]("fn name => (Thy_Info.use_thy name; Thy_Info.get_theory name)")
      importMLStructure = MLValue.compileFunction[(Theory,String,String), Unit](
        """fn (thy,theirName,hereStruct) => let
                  val theirAllStruct = Context.setmp_generic_context (SOME (Context.Theory thy))
                                       (#allStruct ML_Env.name_space) ()
                  val theirStruct = case List.find (fn (n,_) => n=theirName) theirAllStruct of
                           NONE => error ("Structure " ^ theirName ^ " not declared in given context")
                           | SOME (_,s) => s
                  val _ = #enterStruct ML_Env.name_space (hereStruct, theirStruct)
                  in () end""".replace('\n', ' '))
    }
  }

  def apply(name: String)(implicit ec: ExecutionContext): Theory = {
    val mlName = MLValue(name)
    val mlThy : MLValue[Theory] = loadTheory[String,Theory](mlName)
    new Theory(name, mlThy)
  }


  object TheoryConverter extends Converter[Theory] {
    override def retrieve(value: MLValue[Theory])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[Theory] =
      for (_ <- value.id)
        yield new Theory(mlValue = value, name="‹theory›")
    override def store(value: Theory)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Theory] =
      value.mlValue
    override lazy val exnToValue: String = "fn E_Theory thy => thy"
    override lazy val valueToExn: String = "E_Theory"
  }

  object Implicits {
    implicit val theoryConverter: TheoryConverter.type = TheoryConverter
  }
}
