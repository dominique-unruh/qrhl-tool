// This file is for temporary experiments only

import java.util.Date

import qrhl.toplevel.Toplevel

import scala.language.implicitConversions

object Test0 {
  def main(args: Array[String]): Unit = {
    try {
      val tl = new Toplevel()
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
