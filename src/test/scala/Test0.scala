// This file is for temporary experiments only

import java.util.Date

import info.hupel.isabelle.api.XML.Tree
import info.hupel.isabelle.{Codec, Operation, XMLResult, pure}
import info.hupel.isabelle.pure.{Indexname, Typ}
import qrhl.State
import qrhl.toplevel.{Toplevel, ToplevelTest}

import scala.language.implicitConversions
import scala.math.BigInt

sealed abstract class HashTerm {
  val hash: BigInt
  protected def updateHash(hash: BigInt) : HashTerm
  def $(that: HashTerm): HashTerm = App(this, that)
}

final class Const private (val name: String, val typ: Typ, val hash: BigInt) extends HashTerm {
  override protected def updateHash(hash: BigInt) = ???
}
object Const {
  def unapply(arg: Const): Some[(String, Typ)] = Some(arg.name,arg.typ)
  def apply(name: String, typ: Typ) = new Const(name,typ,HashTerm.noHash)
}
final class Free private (val name: String, val typ: Typ, val hash: BigInt) extends HashTerm {
  override protected def updateHash(hash: BigInt): HashTerm = ???
}
object Free {
  def unapply(arg: Free): Some[(String, Typ)] = Some(arg.name,arg.typ)
  def apply(name: String, typ: Typ) = new Free(name,typ,HashTerm.noHash)
}
final class Var private (val name: Indexname, val typ: Typ, val hash: BigInt) extends HashTerm {
  override protected def updateHash(hash: BigInt): HashTerm = ???
}
object Var {
  def unapply(arg: Var): Some[(Indexname, Typ)] = Some(arg.name,arg.typ)
  def apply(name: Indexname, typ: Typ) = new Var(name,typ,HashTerm.noHash)
}
final class Bound private (val index: BigInt, val hash: BigInt) extends HashTerm {
  override protected def updateHash(hash: BigInt): HashTerm = ???
}
object Bound {
  def unapply(arg: Bound): Some[BigInt] = Some(arg.index)
  def apply(index: BigInt) = new Bound(index,HashTerm.noHash)
}
final class Abs private (val name: String, val typ: Typ, val body: HashTerm, val hash: BigInt) extends HashTerm {
  override protected def updateHash(hash: BigInt): HashTerm = ???
}
object Abs {
  def unapply(arg: Abs): Some[(String, Typ, HashTerm)] = Some((arg.name,arg.typ,arg.body))
  def apply(name: String, typ: Typ, body: HashTerm) = new Abs(name,typ,body,HashTerm.noHash)
}
final class App private (val fun: HashTerm, val arg: HashTerm, val hash: BigInt) extends HashTerm {
  override protected def updateHash(hash: BigInt): HashTerm = ???
}
object App {
  def apply(fun: HashTerm, arg: HashTerm) = new App(fun, arg, HashTerm.noHash)
  def unapply(arg: App): Some[(HashTerm, HashTerm)] = Some((arg.fun,arg.arg))
}

object HashTermWithHash {
  def unapply(term: HashTerm): Option[BigInt] =
    if (term.hash==HashTerm.noHash)
      None
    else Some(term.hash)
}

object HashTerm {
  val noHash = 0

  implicit val codec: Codec[HashTerm] = Codec.tuple[BigInt,HashTerm](Codec.integer,codec0).transform({case (hash,term) => term.updateHash(hash)}, {term => (term.hash,term)}, "term")

  lazy val codec0: Codec[HashTerm] = new Codec.Variant[HashTerm]("hterm'") {
    val mlType = "term"

    val termConst = Codec[(String, Typ)]
    val termFree = Codec[(String, Typ)]
    val termVar = Codec[(Indexname, Typ)]
    val termBound = Codec[BigInt]
    lazy val termAbs = Codec[(String, Typ, HashTerm)](Codec.triple(Codec.string,Typ.typCodec,codec0))
    lazy val termApp = Codec[(HashTerm, HashTerm)](Codec.tuple(codec0,codec0))

    def enc(term: HashTerm) = term match {
//      case HashTermWithHash(hash) => (6, Codec[BigInt].encode(hash))
      case Const(name, typ) => (0, termConst.encode((name, typ)))
      case Free(name, typ) => (1, termFree.encode((name, typ)))
      case Var(iname, typ) => (2, termVar.encode((iname, typ)))
      case Bound(idx) => (3, termBound.encode(idx))
      case Abs(name, typ, body) => (4, termAbs.encode((name, typ, body)))
      case App(f, x) => (5, termApp.encode((f, x)))
    }

    def dec(idx: Int) = idx match {
      case 0 => Some(tree => termConst.decode(tree).right.map { case (name, typ) => Const(name, typ) })
      case 1 => Some(tree => termFree.decode(tree).right.map { case (name, typ) => Free(name, typ) })
      case 2 => Some(tree => termVar.decode(tree).right.map { case (iname, typ) => Var(iname, typ) })
      case 3 => Some(tree => termBound.decode(tree).right.map { idx => Bound(idx) })
      case 4 => Some(tree => termAbs.decode(tree).right.map { case (name, typ, body) => Abs(name, typ, body) })
      case 5 => Some(tree => termApp.decode(tree).right.map { case (f, x) => App(f, x) })
//      case 6 => Some(tree => ())
      case _ => None
    }
  }
}

object Test0 {
  def main(args: Array[String]): Unit = {

  }

  def main0(args: Array[String]): Unit = {
    try {
      val tl = Toplevel.makeToplevel(cheating=false)
      tl.run(
        """
          |isabelle PrgEnc.
          |
          |ambient var rho : program_state.
          |
          |classical var k : key.
          |classical var s : key.
          |
          |# Variables for adversary communication
          |classical var m1 : msg.
          |classical var m2 : msg.
          |classical var c : msg.
          |classical var r : msg.
          |classical var b : bit.
          |
          |quantum var qglobA : string.
          |classical var cglobA : string.
          |
          |# A1: inputs: none; outputs m1,m2
          |adversary A1 vars m1,m2,cglobA,qglobA.
          |# A: inputs: c; outputs: b
          |adversary A2 vars c,b,cglobA,qglobA.
          |
          |# B1/B2: inputs: r; outputs: b
          |program B1 := { call A1; c <- r+m1; call A2; }.
          |program B2 := { call A1; c <- r+m2; call A2; }.
          |
          |program indcpa0 := {
          |  k <$ uniform UNIV;
          |  call A1;
          |  c <- enc(k,m1);
          |  call A2;
          |}.
          |
          |program indcpa1 := {
          |  k <$ uniform UNIV;
          |  call A1;
          |  c <- enc(k,m2);
          |  call A2;
          |}.
          |
          |program prg0B1 := {
          |  s <$ uniform UNIV;
          |  r <- G(s);
          |  call B1;
          |}.
          |
          |program prg1B1 := {
          |  r <$ uniform UNIV;
          |  call B1;
          |}.
          |
          |program prg0B2 := {
          |  s <$ uniform UNIV;
          |  r <- G(s);
          |  call B2;
          |}.
          |
          |program prg1B2 := {
          |  r <$ uniform UNIV;
          |  call B2;
          |}.
          |
          |qrhl {(ℭ𝔩𝔞[¬ True] + ⊤) ⊓ ℭ𝔩𝔞[c1 = c2 ∧ b1 = b2 ∧ cglobA1 = cglobA2] ⊓ ⟦qglobA1⟧ ≡𝔮 ⟦qglobA2⟧} call prg1B1; ~ call prg1B2; {(ℭ𝔩𝔞[¬ True] + ⊤) ⊓ ℭ𝔩𝔞[c1 = c2 ∧ b1 = b2 ∧ cglobA1 = cglobA2] ⊓ ⟦qglobA1⟧ ≡𝔮 ⟦qglobA2⟧}.
          |
          | inline prg1B1.
          | inline prg1B2.
          | inline B1.
          | inline B2.
          | equal.
          |  simp!.
        """.stripMargin)

      val cmd = tl.state.parseCommand("wp left")

      val repetitions = 100

      println("*** Start ***")
      val start = new Date()
      for (_ <- 1 to repetitions) {
        val state = cmd.act(tl.state)
//        println(state)
      }
      val end = new Date()
      println("*** End ***")

      println(s"Time per iteration: ${(end.getTime - start.getTime) * 1.0 / repetitions} ms")
    } catch {
      case e: Throwable => e.printStackTrace()
    }

    import sys.process._
//    "nohup play ~/Dropbox/Schwarzenegger-You-are-stupid.mp3" !

    sys.exit(0)
  }
}
