package qrhl.tactic

import info.hupel.isabelle.ml.Expr
import info.hupel.isabelle.pure.{Term, Typ=>ITyp}
import qrhl.isabelle.Isabelle
import qrhl.{UserException, State}
import qrhl.logic._

//@deprecated
//case class SampleTac(left:Boolean) extends WpStyleTac(left=left) {
//  override def getWP(state: State, left: Boolean, statement: Statement, post: Expression): Expression = statement match {
//    case Sample(x, e) =>
//      val isabelle = post.isabelle
//      val env = state.environment
//      val e1 = e.index(env, left=left)
//      val x1 = x.index(left=left)
//
//
//      val wpExpr = SampleTac.ml(x1.name)(implicitly) (x1.typ.isabelleTyp)(implicitly) (e1.isabelleTerm)(implicitly) (post.isabelleTerm)
//      val wp = post.isabelle.runExpr(wpExpr)
//      Expression(post.isabelle,wp)
//    case _ => throw UserException(s"Expected am sample statement as last expression on the ${if (left) "left" else "right"} side")
//  }
//
//  override val toString: String = if (left) "sample(left)" else "sample(right)"
//}
//
//object SampleTac {
//
//  private val ml = Expr.uncheckedLiteral[String => ITyp => Term => Term => Term](
//    """(fn v => fn T => fn e => fn B =>
//      |    let val distrT = Type(@{type_name distr},[T])
//      |        val _ = if fastype_of e = distrT then ()
//      |                else raise(TYPE("variable and expression, type mismatch",[T,fastype_of e],[e]))
//      |        val _ = if fastype_of B = @{typ predicate} then ()
//      |                else raise(TYPE("predicate has wrong type",[fastype_of B],[B]))
//      |        val setT = Type(@{type_name set},[T])
//      |        val supp = Const(@{const_name supp}, distrT --> setT) $ e
//      |        val absB = Term.absfree (v,T) B
//      |        val B2 = @{const Inf(predicate)} $
//      |                      (Const(@{const_name image}, (T --> @{typ predicate}) --> setT -->  @{typ "predicate set"})
//      |                         $ absB $ supp)
//      |        val total = @{const classical_subspace} $
//      |             HOLogic.mk_eq (Const(@{const_name weight}, distrT --> @{typ real}) $ e, @{term "1::real"})
//      |    in
//      |      @{term "inf::predicate=>predicate=>predicate"} $ total $ B2
//      |    end)
//    """.stripMargin)
//
//}