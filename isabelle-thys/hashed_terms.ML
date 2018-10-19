structure Hashed_Terms =
struct

val hashed_terms = Unsynchronized.ref Inttab.empty : term Inttab.table Unsynchronized.ref

val hashed_term_lock = Mutex.mutex ()

val h1 = 4635782457857634685
val h2 = 46357824578576344234

fun hash_int i h = (h * h1 + i) mod h2

fun hash_string (s:string) h = CharVector.foldr (fn (c,h) => hash_int (Char.ord c) h) h s |> hash_int 256

fun hash_list hash xs h = h |> fold (fn x => hash_int 1 #> hash x) xs |> hash_int 0

val hash_sort = hash_list hash_string

datatype hterm' =
    HConst of string * typ |
    HFree of string * typ |
    HVar of indexname * typ |
    HBound of int |
    HAbs of string * typ * (int * hterm') |
    HApp of (int * hterm') * (int * hterm') |
    HOmitted
type hterm = int * hterm'

val hash_of = fst : hterm -> int

(* Encodes type into prefix free sequence of hash_int's *)
fun hash_typ (Type(n,Ts)) h = h |> hash_int 1 |> hash_string n |> hash_list hash_typ Ts
  | hash_typ (TVar((n,i),s)) h = h |> hash_int 2 |> hash_string n |> hash_int i |> hash_sort s
  | hash_typ (TFree(n,s)) h = h |> hash_int 3 |> hash_string n |> hash_sort s

fun hash_term (Free(n,T)) = 1 |> hash_string n |> hash_typ T
  | hash_term (Var((n,i),T)) = 2 |> hash_string n |> hash_int i |> hash_typ T
  | hash_term (t1 $ t2) = 3 |> hash_int (hash_term t1) |> hash_int (hash_term t2)
  | hash_term (Const(n,T)) = 4 |> hash_string n |> hash_typ T
  | hash_term (Abs(n,T,body)) = 5 |> hash_string n |> hash_typ T |> hash_int (hash_term body)
  | hash_term (Bound i) = 6 |> hash_int i

fun hash_and_store_term'' (Free(n,T)) = (1 |> hash_string n |> hash_typ T, HFree(n, T))
  | hash_and_store_term'' (Var(ni as (n,i),T)) = (2 |> hash_string n |> hash_int i |> hash_typ T, HVar(ni, T))
  | hash_and_store_term'' (t1 $ t2) = let 
        val ht1 = hash_and_store_term' t1
        val ht2 = hash_and_store_term' t2
        in (3 |> hash_int (hash_of ht1) |> hash_int (hash_of ht2), HApp(ht1, ht2)) end
  | hash_and_store_term'' (Const(n,T)) = (4 |> hash_string n |> hash_typ T, HConst(n, T))
  | hash_and_store_term'' (Abs(n,T,body)) = let val hbody = hash_and_store_term' body in
                          (5 |> hash_string n |> hash_typ T |> hash_int (hash_of hbody), HAbs(n, T, hbody)) end
  | hash_and_store_term'' (Bound i) = (6 |> hash_int i, HBound i)

and hash_and_store_term' t : hterm = let
  val ht = hash_and_store_term'' t
  val h = hash_of ht
in case Inttab.lookup (!hashed_terms) h of NONE => 
      (tracing ("Adding "^string_of_int h^" -> "^Syntax.string_of_term \<^context> t);
       hashed_terms := Inttab.update_new (h,t) (!hashed_terms);
       ht)
    | SOME t' => if t <> t' then raise TERM("hash_and_store_term': collision "^string_of_int h,[t',t]) else (h,HOmitted)
end

fun hash_and_store_term t = Multithreading.synchronized "hash_and_store_term" hashed_term_lock (fn _ => hash_and_store_term' t)


fun lookup_term h = case Inttab.lookup (!hashed_terms) h of SOME t => t | NONE => error ("lookup_term: "^string_of_int h)

fun hterm_to_term (h,HOmitted) = lookup_term h
  | hterm_to_term ht = error ("hterm_to_term: "^\<^make_string> ht)

local
open Codec
val indexname: indexname codec = tuple string int
in

fun hterm_codec () =
  let
    val term_const = tuple string typ
    val term_free = tuple string typ
    val term_var = tuple indexname typ
    val term_bound = int
    fun term_abs () = triple string typ (hterm_codec ())
    fun term_app () = tuple (hterm_codec ()) (hterm_codec ())

    fun enc' (HConst arg) = (0, encode term_const arg)
      | enc' (HFree arg) =  (1, encode term_free arg)
      | enc' (HVar arg) =   (2, encode term_var arg)
      | enc' (HBound arg) = (3, encode term_bound arg)
      | enc' (HAbs arg) =   (4, encode (term_abs ()) arg)
      | enc' (HApp arg) =  (5, encode (term_app ()) arg)
      | enc' (HOmitted) = (6, encode (Codec.unit) ())

    fun dec' 0 = SOME (decode term_const #> map_result HConst)
      | dec' 1 = SOME (decode term_free #> map_result HFree)
      | dec' 2 = SOME (decode term_var #> map_result HVar)
      | dec' 3 = SOME (decode term_bound #> map_result HBound)
      | dec' 4 = SOME (decode (term_abs ()) #> map_result HAbs)
      | dec' 5 = SOME (decode (term_app ()) #> map_result HApp)
      | dec' 6 = SOME (decode Codec.unit #> map_result (fn _ => HOmitted))
      | dec' _ = NONE

    val codec' = variant enc' dec' "hterm'"
  in tuple int codec' end
end

val hterm_codec = hterm_codec ()

val term_codec = Codec.transform hterm_to_term hash_and_store_term hterm_codec

end
