package hashedcomputation

import org.scalatest.funsuite.AnyFunSuite

class HashTagTest extends AnyFunSuite {
  test("same HashTag() twice") {
    //noinspection AccessorLikeMethodIsEmptyParen
    def getHashTag() = HashTag()
    val tag1 = getHashTag()
    val tag2 = getHashTag()
    assert(tag1 == tag2)
  }

  test("different HashTag()") {
    val tag1 = HashTag()
    val tag2 = HashTag()
    assert(tag1 != tag2)
  }
}
