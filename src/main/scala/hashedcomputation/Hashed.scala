package hashedcomputation


case class Hashed[T, Hash](value: T, hash: Hash)
object Hashed {
  object Value {
    def unapply[T,Hash](arg: Hashed[T, Hash]): Some[T] = Some(arg.value)
  }
}