package hashedcomputation

class Computation[T] private[hashedcomputation] (computation: => T) {
  /** Blocks until the result is computed and returns it. */
  lazy val result: T = computation
}
