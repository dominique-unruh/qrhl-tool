package isabelle

import org.scalatest.FunSuite

class SymbolsTest extends FunSuite {

  test("roundtrip") {
    val string = """Proj (Span {ket 0})»⟦C1⟧ · Proj (Span {ket 0})»⟦A1⟧ ⋅ """
    val symbolString = Symbols.globalInstance.unicodeToSymbols(string)
    println(symbolString)
    val unicodeString = Symbols.globalInstance.symbolsToUnicode(symbolString)
    println(unicodeString)
    assert(unicodeString == string)
  }
}
