package qrhl.toplevel

import org.scalatest.funsuite.AnyFunSuite

class PrintCommandTest extends AnyFunSuite {
  test("print goal") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("quantum var q : int")
    tl.execCmd("quantum var r : int")
    tl.execCmd("classical var x : int")
    tl.execCmd("ambient var z : int")
    tl.execCmd("qrhl bla: {Cla[x1=1 & z=2]} skip; ~ skip; {Qeq[q1 = q2]}")
    val output = PrintCommand("goal").actString(tl.state).lastOutput
    println(output)
    assert(output.contains("lemma bla_"))
    assert(output.contains("""fixes var_x1 :: "int variable" and z :: int and q1 :: "int variable" and q2 :: "int variable""""))
    assert(output.contains("""assumes [simp]: ‹declared_qvars ⟦q1, q2⟧›"""))
    assert(output.contains("""shows "QRHL {ℭ𝔩𝔞[(x1::int) = 1 ∧ (z::int) = 2]} [] [] {⟦q1::int variable⟧ ≡𝔮 ⟦q2⟧}""""))
  }

  test("print goal parser") {
    val tl = ToplevelTest.makeToplevelWithTheory()
    tl.execCmd("lemma test: 1=(1::nat)")
    tl.execCmd("print goal")
    val output = tl.state.lastOutput
    println(output)
    assert(output.contains("lemma test_"))
    assert(output.contains("""shows "(1::nat) = 1"""") || output.contains("""shows "1 = 1""""))
    assert(!output.contains("declared_qvars"))
  }
}
