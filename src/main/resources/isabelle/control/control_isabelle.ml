structure Control_Isabelle : sig
  (* TODO: Does this need to be exported? *)
  (* val sendReply : int -> int list -> unit *)
  val handleLines : unit -> unit
  exception E_ExnExn of exn -> exn
  exception E_Int of int
  exception E_String of string
  exception E_Pair of exn * exn
(*   exception E_Context of Proof.context
  exception E_Theory of theory
  exception E_Typ of typ
  exception E_Term of term
  exception E_Cterm of cterm
  exception E_Thm of thm *)
  val store : int -> exn -> unit
  (* For diagnostics. Linear time *)
  val numObjects : unit -> int
end
=
struct
val inStream = TextIO.openIn inputPipeName
val outStream = TextIO.openOut outputPipeName

val objectsMax = Unsynchronized.ref 0
val objects : exn Inttab.table Unsynchronized.ref = Unsynchronized.ref Inttab.empty

fun numObjects () = Inttab.fold (fn _ => fn i => i+1) (!objects) 0

fun sendReplyStr seq str = let
(*  val _ = if Char.contains str #"\n" then error "Trying to send string containing newline" else () *)
  val str = String.map (fn c => case c of #"\n" => #" " | _ => c) str  (* TODO: Support newlines *)
  val str = string_of_int seq ^ " " ^ str ^ "\n"
  (* val _ = tracing ("sendReply: "^str) *)
  val _ = TextIO.output (outStream, str)
  val _ = TextIO.flushOut outStream
  in () end

fun sendReply seq ints = let
  val str = (String.concatWith " " (map string_of_int (seq::ints)) ^ "\n")
  (* val _ = tracing ("sendReply: "^str) *)
  val _ = TextIO.output (outStream, str)
  val _ = TextIO.flushOut outStream
  in () end

exception E_ExnExn of exn -> exn
exception E_Int of int
exception E_Unit
exception E_String of string
exception E_Pair of exn * exn

fun executeML ml = let
  (* val _ = TextIO.print ("Compiling "^ ml^"\n") *)
  (* val flags = ML_Compiler.verbose true ML_Compiler.flags *)
  val flags = ML_Compiler.flags
  val _ = ML_Compiler.eval flags Position.none (ML_Lex.tokenize ml)
  (* val _ = TextIO.flushOut TextIO.stdOut (* Doesn't see to work *) *)
  in () end

(* fun executeMLInt seq ml = let
  val _ = tracing ("executeMLInt "^string_of_int seq ^" : " ^ml)
  in  executeML ("Control_Isabelle.sendReply "^string_of_int seq^" [" ^ ml ^ "]") end *)

fun addToObjects exn = let
  val idx = !objectsMax
  val _ = objects := Inttab.update_new (idx, exn) (!objects)
  val _ = objectsMax := idx + 1
  in idx end

fun store seq exn = sendReply seq [addToObjects exn]

fun storeMany seq exns = sendReply seq (map addToObjects exns)

fun storeMLValue seq ml =
  executeML ("let open Control_Isabelle val result = ("^ml^") in store "^string_of_int seq^" result end")

fun exn_str exn = Runtime.pretty_exn exn |> Pretty.unformatted_string_of

fun retrieveInt seq id = case Inttab.lookup (!objects) id of
  NONE => error ("no object " ^ string_of_int id)
  | SOME (E_Int i) => sendReply seq [i]
  | SOME exn => error ("expected E_Int, got: " ^ exn_str exn)

fun retrieveString seq id = case Inttab.lookup (!objects) id of
  NONE => error ("no object " ^ string_of_int id)
  | SOME (E_String str) => sendReplyStr seq str
  | SOME exn => error ("expected E_String, got: " ^ exn_str exn)


fun applyFunc seq f x = case (Inttab.lookup (!objects) f, Inttab.lookup (!objects) x) of
  (NONE,_) => error ("no object " ^ string_of_int f)
  | (_,NONE) => error ("no object " ^ string_of_int x)
  | (SOME (E_ExnExn f), SOME x) => store seq (f x)
  | (SOME exn, _) => error ("object " ^ string_of_int f ^ " is not an E_ExnExn but: " ^ exn_str exn)



fun mkPair seq a b = case (Inttab.lookup (!objects) a, Inttab.lookup (!objects) b) of
  (NONE,_) => error ("no object " ^ string_of_int a)
  | (_,NONE) => error ("no object " ^ string_of_int b)
  | (SOME x, SOME y) => store seq (E_Pair (x,y))

fun splitPair seq id = case (Inttab.lookup (!objects) id) of
  NONE => error ("no object " ^ string_of_int id)
  | SOME (E_Pair (x,y)) => storeMany seq [x,y]
  | SOME exn => error ("object " ^ string_of_int id ^ " is not an E_Pair but: " ^ exn_str exn)

(* fun executeML' ml =
  executeML ("local open Control_Isabelle in " ^ ml ^ " end") *)

fun removeObjects ids =
  objects := fold Inttab.delete ids (!objects)

fun int_of_string str = case Int.fromString str of
  NONE => error ("Failed to parse '" ^ str ^ "' as an int")
  | SOME i => i

(* Without error handling *)
fun handleLine' seq line =
  case String.sub (line, 0) of
    (* Mxxx - executes ML code xxx *)
    #"M" => (executeML (String.extract (line, 1, NONE)); sendReply seq [])

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

    (* af x - Parses f,x as object#, f of type E_ExnExn, computes f x, stores the result, response 'seq ID' *)
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
  val idx = addToObjects (E_String msg)
  val str = string_of_int seq ^ " !" ^ string_of_int idx ^ "\n"
  val _ = TextIO.output (outStream, str)
  val _ = TextIO.flushOut outStream
  in () end

fun handleLine seq line =
  handleLine' seq line
  handle exn => reportException seq exn

fun handleLines' number = case TextIO.inputLine inStream of
    NONE => (tracing "End of input"; ())
    | SOME line => (handleLine number line; handleLines' (number+1))
    ;;

fun handleLines () = handleLines' 0

(* 
TODO: try this to flush stderr/stdout:
TextIO.StreamIO.setBufferMode (TextIO.getOutstream TextIO.stdOut, IO.LINE_BUF)
 *)

end
