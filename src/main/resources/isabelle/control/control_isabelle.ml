structure Control_Isabelle : sig
  val handleLines : unit -> unit
  datatype data = D_String of string | D_Int of int | D_Tree of data list
  exception E_Function of exn -> exn
  exception E_Int of int
  exception E_String of string
  exception E_Data of data
  exception E_Pair of exn * exn
  val store : int -> exn -> unit
  (* For diagnostics. Linear time *)
  val numObjects : unit -> int
end
=
struct
datatype data = D_String of string | D_Int of int | D_Tree of data list

exception E_Function of exn -> exn
(*exception E_StoreFunction of tree -> exn*)
(*exception E_RetrieveFunction of exn -> tree*)
exception E_Data of data
exception E_Int of int
exception E_Unit
exception E_String of string
exception E_Pair of exn * exn

val inStream = TextIO.openIn inputPipeName
val outStream = BinIO.openOut outputPipeName

val objectsMax = Unsynchronized.ref 0
val objects : exn Inttab.table Unsynchronized.ref = Unsynchronized.ref Inttab.empty

fun numObjects () : int = Inttab.fold (fn _ => fn i => i+1) (!objects) 0

fun sendByte b = BinIO.output1 (outStream, b)

fun sendInt32 i = let
  val word = Word32.fromInt i
  val _ = sendByte (Word8.fromLargeWord (Word32.toLargeWord (Word32.>> (word, 0w24))))
  val _ = sendByte (Word8.fromLargeWord (Word32.toLargeWord (Word32.>> (word, 0w16))))
  val _ = sendByte (Word8.fromLargeWord (Word32.toLargeWord (Word32.>> (word, 0w8))))
  val _ = sendByte (Word8.fromLargeWord (Word32.toLargeWord (word)))
  in () end

fun sendInt64 i = let
  val word = Word64.fromInt i
  val _ = sendByte (Word8.fromLargeWord (Word64.toLargeWord (Word64.>> (word, 0w56))))
  val _ = sendByte (Word8.fromLargeWord (Word64.toLargeWord (Word64.>> (word, 0w48))))
  val _ = sendByte (Word8.fromLargeWord (Word64.toLargeWord (Word64.>> (word, 0w40))))
  val _ = sendByte (Word8.fromLargeWord (Word64.toLargeWord (Word64.>> (word, 0w32))))
  val _ = sendByte (Word8.fromLargeWord (Word64.toLargeWord (Word64.>> (word, 0w24))))
  val _ = sendByte (Word8.fromLargeWord (Word64.toLargeWord (Word64.>> (word, 0w16))))
  val _ = sendByte (Word8.fromLargeWord (Word64.toLargeWord (Word64.>> (word, 0w8))))
  val _ = sendByte (Word8.fromLargeWord (Word64.toLargeWord (word)))
  in () end

fun sendString str = let
  val len = size str
  val _ = sendInt32 len
  val _ = BinIO.output (outStream, Byte.stringToBytes str)
  in () end

fun sendData (D_Int i) = (sendByte 0w1; sendInt64 i)
  | sendData (D_String str) = (sendByte 0w2; sendString str)
  | sendData (D_Tree list) = let
      val _ = sendByte 0w3
      val _ = sendInt64 (length list)
      val _ = List.app sendData list
    in () end
      
(* Deprecated *)
fun sendReplyStr seq str = let
  val _ = sendInt64 seq
  val _ = sendByte 0w1
  val _ = sendData (D_String str)
  val _ = BinIO.flushOut outStream
  in () end

(* Deprecated *)
fun sendReplyN seq ints = let
  val _ = sendInt64 seq
  val _ = sendByte 0w1
  val _ = sendData (D_Tree (map D_Int ints))
  val _ = BinIO.flushOut outStream
  in () end

(* Deprecated *)
fun sendReply1 seq int = let
  val _ = sendInt64 seq
  val _ = sendByte 0w1
  val _ = sendData (D_Int int)
  val _ = BinIO.flushOut outStream
  in () end



fun executeML ml = let
  (* val _ = TextIO.print ("Compiling "^ ml^"\n") *)
  (* val flags = ML_Compiler.verbose true ML_Compiler.flags *)
  val flags = ML_Compiler.flags
  val _ = ML_Compiler.eval flags Position.none (ML_Lex.tokenize ml)
  (* val _ = TextIO.flushOut TextIO.stdOut (* Doesn't seem to work *) *)
  in () end

fun addToObjects exn = let
  val idx = !objectsMax
  val _ = objects := Inttab.update_new (idx, exn) (!objects)
  val _ = objectsMax := idx + 1
  in idx end

fun store seq exn = sendReply1 seq (addToObjects exn)

fun storeMany seq exns = sendReplyN seq (map addToObjects exns)

fun storeMLValue seq ml =
  executeML ("let open Control_Isabelle val result = ("^ml^") in store "^string_of_int seq^" result end")

fun exn_str exn = Runtime.pretty_exn exn |> Pretty.unformatted_string_of

fun retrieveInt seq id = case Inttab.lookup (!objects) id of
  NONE => error ("no object " ^ string_of_int id)
  | SOME (E_Int i) => sendReply1 seq i
  | SOME exn => error ("expected E_Int, got: " ^ exn_str exn)

fun retrieveString seq id = case Inttab.lookup (!objects) id of
  NONE => error ("no object " ^ string_of_int id)
  | SOME (E_String str) => sendReplyStr seq str
  | SOME exn => error ("expected E_String, got: " ^ exn_str exn)

fun applyFunc seq f x = case (Inttab.lookup (!objects) f, Inttab.lookup (!objects) x) of
  (NONE,_) => error ("no object " ^ string_of_int f)
  | (_,NONE) => error ("no object " ^ string_of_int x)
  | (SOME (E_Function f), SOME x) => store seq (f x)
  | (SOME exn, _) => error ("object " ^ string_of_int f ^ " is not an E_Function but: " ^ exn_str exn)



fun mkPair seq a b = case (Inttab.lookup (!objects) a, Inttab.lookup (!objects) b) of
  (NONE,_) => error ("no object " ^ string_of_int a)
  | (_,NONE) => error ("no object " ^ string_of_int b)
  | (SOME x, SOME y) => store seq (E_Pair (x,y))

fun splitPair seq id = case (Inttab.lookup (!objects) id) of
  NONE => error ("no object " ^ string_of_int id)
  | SOME (E_Pair (x,y)) => storeMany seq [x,y]
  | SOME exn => error ("object " ^ string_of_int id ^ " is not an E_Pair but: " ^ exn_str exn)

fun removeObjects ids =
  objects := fold Inttab.delete ids (!objects)

fun int_of_string str = case Int.fromString str of
  NONE => error ("Failed to parse '" ^ str ^ "' as an int")
  | SOME i => i

(* Without error handling *)
fun handleLine' seq line =
  case String.sub (line, 0) of
    (* Mxxx - executes ML code xxx *)
    #"M" => (executeML (String.extract (line, 1, NONE)); sendReplyN seq [])

    (* ixxx - executes ML expression xxx (of type int) and gives response 'seq result' *)
    (*   | #"i" => executeMLInt seq (String.extract (line, 1, NONE)) *)

    (* Sxxx - stores xxx as a string in objects, response 'seq ID' *)
  | #"S" => store seq (E_String (String.substring (line, 1, String.size line - 2)))

    (* snnn - Parses nnn as integer, stores result as object, response 'seq object#' *)
  | #"s" => store seq (E_Int (int_of_string (String.extract (line, 1, NONE))))

    (* fxxx - Parses xxx as ML function of type exn \<rightarrow> exn, stores xxx as object #seq *)
  | #"f" => storeMLValue seq (String.extract (line, 1, NONE))

    (* rID - Parses ID as object# and returns the object, assuming it's (E_Int i), response 'seq i' *)
  | #"r" => retrieveInt seq (int_of_string (String.extract (line, 1, NONE)))

    (* RID - Parses ID as object# and returns the object, assuming it's (E_String s), response 'seq s' *)
  | #"R" => retrieveString seq (int_of_string (String.extract (line, 1, NONE)))

    (* af x - Parses f,x as object#, f of type E_Function, computes f x, stores the result, response 'seq ID' *)
  | #"a" => let val (f,x) = case String.fields (fn c => #" "=c) (String.extract (line, 1, NONE)) |> map int_of_string
                            of [f,x] => (f,x) | _ => raise Match
        in applyFunc seq f x end

    (* gi j k ... - removes object i,j,k,... from objects *)
  | #"g" => removeObjects (String.extract (line, 1, NONE) |> String.fields (fn c => #" "=c) |> map int_of_string)

    (* pi j - takes objects i j, creates new object with content E_Pair (i,j), returns 'seq object' *)
  | #"p" => let val (a,b) = case String.fields (fn c => #" "=c) (String.extract (line, 1, NONE)) |> map int_of_string
                            of [a,b] => (a,b) | _ => raise Match
        in mkPair seq a b end

    (* Px - takes object x, parses as E_Pair (a,b), stores a,b as objects, returns "seq a b" *)
  | #"P" => splitPair seq (int_of_string (String.extract (line, 1, NONE)))

  | cmd => error ("Unknown command " ^ str cmd)

fun reportException seq exn = let
  val msg = Runtime.exn_message exn
  val _ = sendInt64 seq
  val _ = sendByte 0w2
  val _ = sendString msg
  val _ = BinIO.flushOut outStream
  in () end

fun handleLine seq line =
  handleLine' seq line
  handle exn => reportException seq exn

fun handleLines' number = case TextIO.inputLine inStream of
    NONE => (tracing "End of input"; ())
    | SOME line => (handleLine number line; handleLines' (number+1))
    ;;

fun handleLines () = handleLines' 0

val _ = TextIO.StreamIO.setBufferMode (TextIO.getOutstream TextIO.stdOut, IO.LINE_BUF)

end
