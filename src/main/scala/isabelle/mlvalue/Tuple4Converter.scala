package isabelle.mlvalue

import isabelle.control.Isabelle
import isabelle.control.Isabelle.{DList, DObject}
import isabelle.mlvalue.MLValue.{Converter, Ops}

import scala.concurrent.{ExecutionContext, Future}

import MLValue.Implicits._

@inline class Tuple4Converter[A, B, C, D](converterA: Converter[A], converterB: Converter[B], converterC: Converter[C], converterD: Converter[D]) extends Converter[(A, B, C, D)] {
  @inline override def retrieve(value: MLValue[(A, B, C, D)])(implicit isabelle: Isabelle, ec: ExecutionContext): Future[(A, B, C, D)] = {
    for (DList(DObject(aID), DObject(bID), DObject(cID), DObject(dID)) <- Ops.retrieveTuple4(value.id);
         a <- converterA.retrieve(new MLValue[A](Future.successful(aID)));
         b <- converterB.retrieve(new MLValue[B](Future.successful(bID)));
         c <- converterC.retrieve(new MLValue[C](Future.successful(cID)));
         d <- converterD.retrieve(new MLValue[D](Future.successful(dID))))
      yield (a, b, c, d)
  }

  @inline override def store(value: (A, B, C, D))(implicit isabelle: Isabelle, ec: ExecutionContext): MLValue[(A, B, C, D)] = {
    val (a, b, c, d) = value
    val mlA = converterA.store(a)
    val mlB = converterB.store(b)
    val mlC = converterC.store(c)
    val mlD = converterD.store(d)
    Ops.storeTuple4[A, B, C, D](for (idA <- mlA.id; idB <- mlB.id; idC <- mlC.id; idD <- mlD.id) yield (DList(DObject(idA), DObject(idB), DObject(idC), DObject(idD))))
      .asInstanceOf[MLValue[(A, B, C, D)]]
  }

  override lazy val exnToValue: String = s"fn E_Pair (a, E_Pair (b, E_Pair (c, d))) => ((${converterA.exnToValue}) a, (${converterB.exnToValue}) b, (${converterC.exnToValue}) c, (${converterD.exnToValue}) d)"
  override lazy val valueToExn: String = s"fn (a,b,c,d) => E_Pair ((${converterA.valueToExn}) a, E_Pair ((${converterB.valueToExn}) b, E_Pair ((${converterC.valueToExn}) c, (${converterD.valueToExn}) d)))"
}
