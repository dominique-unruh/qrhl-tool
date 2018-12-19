package qrhl.tactic
import info.hupel.isabelle.pure.{Term, Typ}
import info.hupel.isabelle.{Operation, pure}
import qrhl.isabelle.{Isabelle, RichTerm}
import qrhl.logic.{CVariable, Sample, Statement}
import qrhl.{State, UserException}

import RichTerm.typ_tight_codec
import RichTerm.term_tight_codec

case class RndTac(map:Option[(CVariable,CVariable,RichTerm)]=None) extends WpBothStyleTac {
  override def getWP(state: State, left: Statement, right: Statement, post: RichTerm): (RichTerm,Nil.type) = (left,right) match {
    case (Sample(x,e), Sample(y,f)) =>
//      val isabelle = post.isabelle
      val env = state.environment
      val e1 = e.index1(env)
      val x1 = x.index1
      val f2 = f.index2(env)
      val y2 = y.index2

      map match {
      case None =>
        if (x.valueTyp != y.valueTyp)
          throw UserException(s"The assigned variables ${x.name} and ${y.name} must have the same type (they have types ${Isabelle.pretty(x.valueTyp)} and ${Isabelle.pretty(y.valueTyp)})")

        val wp = state.isabelle.isabelle.invoke(rndWpOp,
            (state.isabelle.contextId, (x1.name,e1.isabelleTerm, y2.name), (f2.isabelleTerm, x1.valueTyp, post.isabelleTerm)))
        (wp, Nil)
      case Some((xx,yy,distr)) =>

        if (! ((xx==x || xx==x1) && (yy==y || yy==y2)))
          throw UserException(s"You specified variables ${xx.name},${yy.name} in the rnd-command, but the assigned variables are ${x.name},${y.name}")

        val wp = state.isabelle.isabelle.invoke(rndWp2Op,
           ((x1.name,x1.valueTyp,e1.isabelleTerm),
            (y2.name,y2.valueTyp,f2.isabelleTerm),
            (distr.isabelleTerm,post.isabelleTerm, state.isabelle.contextId)))

        (wp, Nil)
    }
    case _ =>
      throw UserException("Expected sampling statement as last statement on both sides")
  }

  val rndWpOp: Operation[(BigInt, (String, Term, String), (Term, Typ, Term)), RichTerm] =
    Operation.implicitly[(BigInt, (String, pure.Term, String), (pure.Term, pure.Typ, pure.Term)), RichTerm]("rndWp")
  val rndWp2Op: Operation[((String, Typ, Term), (String, Typ, Term), (Term, Term, BigInt)), RichTerm] =
    Operation.implicitly[((String, pure.Typ, pure.Term), (String, pure.Typ, pure.Term), (pure.Term, pure.Term, BigInt)), RichTerm]("rndWp2")
}