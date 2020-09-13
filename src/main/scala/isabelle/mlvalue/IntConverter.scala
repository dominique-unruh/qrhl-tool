package isabelle.mlvalue

import isabelle.control.Isabelle
import isabelle.control.Isabelle.DInt
import isabelle.mlvalue.MLValue.{Converter, Ops, matchFailExn}

import scala.concurrent.{ExecutionContext, Future}

import MLValue.Implicits._

object IntConverter extends Converter[Int] {
  @inline override def store(value: Int)(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[Int] =
    Ops.storeInt(DInt(value))

  @inline override def retrieve(value: MLValue[Int])
                               (implicit isabelle: Isabelle, ec: ExecutionContext): Future[Int] =
    for (DInt(i) <- Ops.retrieveInt(value.id)) yield i.toInt

  override lazy val exnToValue: String = s"fn E_Int i => i | ${matchFailExn("IntConverter.exnToValue")}"
  override lazy val valueToExn: String = "E_Int"
}
