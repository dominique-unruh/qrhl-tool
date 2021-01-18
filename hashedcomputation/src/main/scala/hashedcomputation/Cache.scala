package hashedcomputation

import com.google.common.cache
import hashedcomputation.HashedPromise.State
import org.jetbrains.annotations.NotNull
import org.log4s

import java.util.concurrent.TimeUnit.HOURS
import java.util.concurrent.atomic.{AtomicLong, AtomicReference}
import scala.annotation.tailrec
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.util.control.Breaks

object Cache {
  private val logger = log4s.getLogger

  private val hashCache: cache.Cache[Hash[_], AnyRef] = cache.CacheBuilder.newBuilder()
    .softValues()
    .expireAfterAccess(1, HOURS)
    .build()

  private val outputCache: cache.Cache[(Hash[_], Hash[_]), Hash[_]] = cache.CacheBuilder.newBuilder()
    .softValues()
    .expireAfterAccess(1, HOURS)
    .build()

  /** Query with (0,computationHash) -> Get (id,Element)
   * Get the hash of the extraction of that Element, query (id,hash), get next (id,Element), etc.
   * Done when getting a hash instead of an Element
   * The (id,Element) is actually a Seq, then need to backtrace over all choices
   * */
  private val fingerprintCache: cache.Cache[(Long, Hash[_]), Either[(Long, Element[_, _]), (Hash[_], Fingerprint[_])]] =
    cache.CacheBuilder.newBuilder()
      .softValues()
      .expireAfterAccess(1, HOURS)
      .build()

  private val fingerprintIdCounter = new AtomicLong(1)

  def getByHash[T](@NotNull hash: Hash[T]): Option[T] = Option(hashCache.getIfPresent(hash)).asInstanceOf[Option[T]]

  private[hashedcomputation] def register[A, B: Hashable]
  (@NotNull value: B, @NotNull computationHash: Hash[_], @NotNull fingerprint: Fingerprint[A]): Unit = {
    logger.debug(s"Registering $value in cache")
    val valueHash = Hashable.hash(value)
    hashCache.put(valueHash, value.asInstanceOf[AnyRef])
    outputCache.put((computationHash, fingerprint.hash), valueHash)

    logger.debug(s"Registering ${(computationHash, fingerprint, valueHash)} in fingerprints")

    def put[C](id: Long, hash: Hash[_], element: Element[C, _]): Long = {
      val entry = fingerprintCache.asMap().compute((id, hash), { (_, entry) =>
        entry match {
          case null =>
            Left((fingerprintIdCounter.incrementAndGet(), element))
          case Left((id, oldElement)) =>
            if (oldElement == element)
              entry
            else {
              // This can only happen if the Fingerprint-generation is nondeterministic
              Left((fingerprintIdCounter.incrementAndGet(), element))
            }
          case _ =>
            // We already have a result hash, we don't need a less precise Fingerprint, should probably not happen with welldesigned fingerprinters except maybe due to nondeterministism
            entry
        }
      })
      entry match {
        case Left((id, _)) => id
        case _ => Breaks.break() // Means we are done
      }
    }

    // TODO: We are ignoring the Fingerprint.hash entries when there are subfingerprints which would allow shortcutting

    val (id, hash) = fingerprint.unfold.foldLeft[(Long, Hash[_])]((0L, computationHash: Hash[_])) {
      case ((id, currentHash), (element, elementHash: Hash[_])) =>
        val id2 = put(id, currentHash, element)
        (id2, elementHash)
    }
    fingerprintCache.put((id, hash), Right(valueHash, fingerprint))

    /*    def storeEntries[C](id: Long, currentHash: Hash,
                                       @Nullable outerElement: Element[A, C],
                                       entries: Seq[Fingerprint.Entry[C, _]]): (Long, Hash) = {
      def storeEntry[D](id: Long, hash: Hash, entry: Entry[C, D]): (Long, Hash) = {
        val element = NestedElement(outerElement, entry.element)
//        val extracted: D = entry.element.extract(extracted)
        entry.fingerprint.fingerprints match {
          case None =>
            val id2 = put(id, hash, element)
            (id2, entry.fingerprint.hash)
          case Some(entries) =>
            storeEntries[D](id, hash, element, entries)
        }
      }

      entries.foldLeft((id, currentHash)) { case ((id, hash), entry) => storeEntry(id, hash, entry) }
    }

    Breaks.breakable {
      val (id, hash) = fingerprint.fingerprints match {
        case Some(fingerprints) =>
          storeEntries[A](0, computationHash, IDElement[A](), fingerprints)
        case None =>
          (0, computationHash)
      }
      fingerprintCache.put((id, hash), Right(valueHash))
    }*/
  }

  def getHashByInputHash[A, B](@NotNull computationHash: Hash[HashedFunction[A, B]], @NotNull inputHash: Hash[A]): Option[Hash[B]] =
    Option(outputCache.getIfPresent((computationHash, inputHash))).asInstanceOf[Option[Hash[B]]]

  def getHashByInput[A, B](@NotNull computationHash: Hash[HashedFunction[A, B]],
                           @NotNull input: A): Option[(Hash[B],Fingerprint[A])] = {
    logger.debug(s"Searching for $computationHash($input) in fingerprints")

    var hash: Hash[_] = computationHash
    var id = 0L
    while (true) {
      fingerprintCache.getIfPresent((id, hash)) match {
        case null => return None
        case Right((hash, fingerprint)) => return Some((hash.asInstanceOf[Hash[B]], fingerprint.asInstanceOf[Fingerprint[A]]))
        case Left((id2, element)) =>
          val element2 = element.asInstanceOf[Element[A, _]]
          id = id2
          hash = element2.extractHash(input)
      }
    }
    throw new AssertionError("Unreachable code")
  }

  /*
  def getByInput[A](@NotNull computationHash: Hash, @NotNull input: A): Option[HashedValue] =
    for (hash <- getHashByInput(computationHash, input);
         value <- getByHash(hash))
      yield value
*/
}


object HashedPromise {
  private def apply[A : Hashable, B : Hashable](state: State[A,B]) =
    new HashedPromise[A,B](new AtomicReference[State[A, B]](state))

  /** Note: does not add hashedValue to the cache! */
  def apply[A : Hashable](hashedValue: A): HashedPromise[HashedValue, A] =
    apply(State.Result[HashedValue,A](hashedValue, null))

  def apply[A : Hashable, B : Hashable](function: HashedFunction[A, B], input: HashedPromise[_, A]): HashedPromise[A, B] =
    apply(State.FunctionOnly(function, input))

  def apply[A : Hashable, B : Hashable](function: HashedFunction[A, B],
                                        input: HashedPromise[_, A], hash: Hash[B]): HashedPromise[A, B] =
    apply(State.FunctionAndHash(function, input, hash))

  def apply[A : Hashable, B : Hashable](hashedFunction: HashedFunction[A, B], input: A): HashedPromise[A, B] =
    apply(hashedFunction, HashedPromise(input))

  private sealed trait State[A, B]
  private object State {
    /** A state in which a computation function is available (but was not executed yet, nor the inputs computed) */
    sealed trait StateWithFunction[A, B] extends State[A,B] {
      val function : HashedFunction[A,B]
      def inputFuture: Future[A]
      def inputPromise: HashedPromise[_, A]
    }
    /** A state where a future with the hash is available (hash computation started or finished) */
    sealed trait HashFutureState[A,B] extends State[A,B] {
      def hashFuture : Future[Hash[B]]
    }
    /** A state where a future with the result is available (hash computation started or finished) */
    sealed trait ResultFutureState[A, B] extends HashFutureState[A,B] {
      def resultFuture : Future[(B, Fingerprint[A])]
      def _hashFuture(implicit hashable: Hashable[B]): Future[Hash[B]] =
        resultFuture.map(result => Hashable.hash[B](result._1))
    }
    /** A state where all computations have been performed (but possibly failed) */
    sealed trait FinalState[A, B] extends HashFutureState[A,B] with ResultFutureState[A,B]
    sealed trait Computing[A, B] extends State[A,B]

    final case class HashAndInput[A : Hashable, B](function: HashedFunction[A,B], input: A, hash: Hash[B])
      extends HashFutureState[A,B] with StateWithFunction[A,B] {
      override def hashFuture: Future[Hash[B]] = Future.successful(hash)
      override def inputFuture: Future[A] = Future.successful(input)
      override def inputPromise: HashedPromise[_, A] = HashedPromise(input)
    }
    final case class Failed[A, B](exception: Throwable) extends FinalState[A,B] {
      override def hashFuture: Future[Hash[B]] = Future.failed(exception)
      override def resultFuture: Future[(B, Fingerprint[A])] = Future.failed(exception)
    }
    final case class Locked[A, B]() extends State[A,B]
    final case class ComputingHash[A, B](override val hashFuture: Future[Hash[B]]) extends HashFutureState[A,B] with Computing[A,B]
    final case class ComputingResult[A, B : Hashable](override val resultFuture: Future[(B, Fingerprint[A])])
      extends ResultFutureState[A,B] with Computing[A,B] {
      override def hashFuture: Future[Hash[B]] = _hashFuture
    }
    sealed case class Result[A, B : Hashable](result: B, fingerprint: Fingerprint[A]) extends FinalState[A,B] {
      override def hashFuture: Future[Hash[B]] = Future.successful(Hashable.hash(result))
      override def resultFuture: Future[(B, Fingerprint[A])] = Future.successful((result, fingerprint))
    }
    final case class FunctionOnly[A, B](override val function: HashedFunction[A, B], input: HashedPromise[_, A]) extends StateWithFunction[A,B] {
      override def inputFuture: Future[A] = input.getOutput
      override def inputPromise: HashedPromise[_, A] = input
    }
    final case class FunctionAndHash[A, B]
    (override val function: HashedFunction[A, B], val input: HashedPromise[_, A],
     hash: Hash[B])
      extends StateWithFunction[A,B] with HashFutureState[A,B] {
      override def hashFuture: Future[Hash[B]] = Future.successful(hash)
      override def inputFuture: Future[A] = input.getOutput
      override def inputPromise: HashedPromise[_, A] = input
    }
  }
}


class HashedPromise[A : Hashable, B : Hashable]
(private val state: AtomicReference[HashedPromise.State[A,B]]) {
  //  private val state: AtomicReference[State[A, B]] = new AtomicReference(initialState)

  private def doCompute(function: HashedFunction[A,B], input: A) : Future[State.FinalState[A,B]] = {

    val future = for ((result, fingerprint) <- function.compute(input);
                      _ = Cache.register(result, function.hash, fingerprint))
      yield State.Result[A,B](result, fingerprint)

    future.recover { exception => State.Failed[A,B](exception) }

  }

  /** Tries to get the hash of the result, but without running the function (but potentially computing the input) */
  private def getHashByInputPromise(function: HashedFunction[A,B], inputPromise: HashedPromise[_, A]):
    Future[Option[(Hash[B], Fingerprint[A])]] = {
    val functionHash = function.hash
    for (inputHash <- inputPromise.getHash; // TODO: catch exception
         hashOption = Cache.getHashByInputHash(functionHash, inputHash);
         hashOption2 <- hashOption match {
           case Some(hash) => Future.successful(Some(hash, Fingerprint[A](inputHash)))
           case None => for (input <- inputPromise.get) yield Cache.getHashByInput(functionHash, input._1)
         })
      yield hashOption2
  }

  /** Guarantees that state is a HashFutureState from now on */
  @tailrec
  private def triggerHashComputation(): Unit = {
    val currentState = state.get()
    currentState match {
      case _ : State.HashFutureState[A,B] =>
      case _ : State.Locked[A,B] =>
        Thread.sleep(1)
        triggerHashComputation()
      case st : State.StateWithFunction[A,B] =>
        if (state.compareAndSet(st, State.Locked())) {
          val function = st.function
          val inputPromise = st.inputPromise
          val future = for (hashOption <- getHashByInputPromise(function, inputPromise);
                            newState <- hashOption match {
                              case Some((hash, _)) =>
                                inputPromise.peek match {
                                  case None =>
                                    Future.successful(State.FunctionAndHash[A,B](function, inputPromise, hash))
                                  case Some(inputFuture) =>
                                    for (inputValue <- inputFuture)
                                      yield State.HashAndInput[A,B](function, inputValue._1, hash)
                                }
                              case None =>
                                for (inputValue <- inputPromise.get; // TODO: Catch exception!
                                     newState <- doCompute(function, inputValue._1))
                                  yield newState
                            };
                            _ = state.set(newState);
                            hash <- newState.hashFuture)
            yield hash
          state.set(State.ComputingHash[A, B](future))
        } else
          triggerHashComputation()
    }
  }

  /** Guarantees that stat is a ResultFutureState from now on (unless it's a Computing state, in which case triggerComputation needs to be invoked again
   * when the computation is finished). */
  @tailrec
  private def triggerComputation(): Unit = {
    val currentState = state.get()
    currentState match {
      case _ : State.Computing[A,B] =>
      case _ : State.ResultFutureState[A,B] =>
      case _ : State.Locked[A,B] =>
        Thread.sleep(1)
        triggerComputation()
      case st: State.StateWithFunction[A, B] =>
        if (state.compareAndSet(st, State.Locked())) {
          val function = st.function
          val inputPromise = st.inputPromise
          val future = for (hashFpOption <- getHashByInputPromise(function, inputPromise);
                            hashOption = hashFpOption.map(_._1);
                            resultOption = hashOption.flatMap(Cache.getByHash);
                            newState <- resultOption match {
                              case Some(result) => Future.successful(State.Result[A, B](result, hashFpOption.get._2))
                              case None =>
                                for (inputValue <- inputPromise.get; // TODO catch exceptions
                                     result <- doCompute(function, inputValue._1))
                                  yield result
                            };
                            _ = state.set(newState);
                            result <- newState.resultFuture)
            yield result
          state.set(State.ComputingResult[A, B](future))
        } else
          triggerComputation()
    }
  }


  def getHash: Future[Hash[B]] = state.get() match {
    case st: State.HashFutureState[A, B] => st.hashFuture
    case _ =>
      triggerHashComputation()
      getHash
  }

  def peek: Option[Future[(B, Fingerprint[A])]] = state.get() match {
    case st : State.ResultFutureState[A, B] => Some(st.resultFuture)
    case _ => None
  }

  def get: Future[(B,Fingerprint[A])] = state.get() match {
    case st: State.ResultFutureState[A, B] => st.resultFuture
    case st: State.ComputingHash[A, B] =>
      for (_ <- st.hashFuture; result <- get) yield result
    case _ =>
      triggerComputation()
      get
  }

  def getOutput: Future[B] = get.map(_._1)
}

