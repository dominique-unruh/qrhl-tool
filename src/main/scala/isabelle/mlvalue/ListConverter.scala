package isabelle.mlvalue

import isabelle.control.Isabelle
import isabelle.control.Isabelle.{DList, DObject, Data, ID}
import isabelle.mlvalue.MLValue.{Converter, Ops, matchFailExn}

import scala.concurrent.{ExecutionContext, Future}

import MLValue.Implicits._

@inline class ListConverter[A](implicit converter: Converter[A]) extends Converter[List[A]] {
  @inline override def store(value: List[A])(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[List[A]] = {
    val listID: Future[List[ID]] = Future.traverse(value) {
      converter.store(_).id
    }
    val data: Future[Data] = for (listID <- listID) yield DList(listID map DObject: _*)
    val result: MLValue[List[MLValue[Nothing]]] = Ops.storeList(data)
    result.asInstanceOf[MLValue[List[A]]]
  }

  @inline override def retrieve(value: MLValue[List[A]])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[List[A]] = {
    for (DList(listObj@_*) <- Ops.retrieveList(value.asInstanceOf[MLValue[List[MLValue[Nothing]]]]);
         listMLValue = listObj map { case DObject(id) => new MLValue[A](Future.successful(id)) };
         list <- Future.traverse(listMLValue) {
           converter.retrieve(_)
         })
      yield list.toList
  }

  override lazy val exnToValue: String = s"fn E_List list => map (${converter.exnToValue}) list | ${matchFailExn("ListConverter.exnToValue")}"
  override lazy val valueToExn: String = s"E_List o map (${converter.valueToExn})"
}
