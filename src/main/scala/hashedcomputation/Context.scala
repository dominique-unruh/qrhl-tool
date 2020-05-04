package hashedcomputation

import java.nio.charset.Charset
import java.security.MessageDigest

import scala.collection.mutable
import scala.language.higherKinds

trait Context {
  type Hash
  /** Each value can be one of:
   * - Hash
   * - String
   * */
  def hash(values: Any*): Hash

  type Hashed[T] = hashedcomputation.Hashed[T, Hash]

  trait FunctionTrait[T,U] extends (Hashed[T] => Computation[U]) {
    val context : Context = Context.this
  }

  type Function[T,U] <: FunctionTrait[T,U]

  def createFunction[T,U](function: Hashed[T]=>U) : Function[T,U]
}





object Context {
  implicit val default : Context = new DefaultContext
}
