package isabelle.mlvalue

import isabelle.control.Isabelle
import isabelle.mlvalue.MLValue.Converter
import scalaz.Id.Id

import scala.concurrent.{ExecutionContext, Future}

@inline class MLValueConverter[A] extends Converter[MLValue[A]] {
  override def retrieve(value: MLValue[MLValue[A]])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[MLValue[A]] =
    Future.successful(value.removeMLValue[Id, A])

  override def store(value: MLValue[A])(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[MLValue[A]] =
    value.insertMLValue[Id, A]

  override lazy val exnToValue: String = "fn x => x"
  override lazy val valueToExn: String = "fn x => x"
}
