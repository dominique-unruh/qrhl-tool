structure Control_Isabelle : sig
  (* TODO: Does this need to be exported? *)
  (* val sendReply : int -> int list -> unit *)
  val handleLines : unit -> unit
  exception E_ExnExn of exn -> exn
  exception E_Int of int
  exception E_String of string
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
  val _ = if Char.contains str #"\n" then error "Trying to send string containing newline" else ()
  val str = string_of_int seq ^ " " ^ str ^ "\n"
  val _ = tracing ("sendReply: "^str)
  val _ = TextIO.output (outStream, str)
  val _ = TextIO.flushOut outStream
  in () end

fun sendReply seq ints = let
  (* val _ = OS.Process.sleep (seconds 0.1) *)
  val str = (String.concatWith " " (map string_of_int (seq::ints)) ^ "\n")
  val _ = tracing ("sendReply: "^str)
  val _ = TextIO.output (outStream, str)
  val _ = TextIO.flushOut outStream
  in () end

exception E_ExnExn of exn -> exn
exception E_Int of int
exception E_Unit
exception E_String of string
(* exception E_Context of Proof.context
exception E_Theory of theory
exception E_Typ of typ
exception E_Term of term
exception E_Cterm of cterm
exception E_Thm of thm *)

fun executeML ml =
  ML_Compiler.eval (ML_Compiler.verbose true ML_Compiler.flags) Position.none (ML_Lex.tokenize ml)

(* fun executeMLInt seq ml = let
  val _ = tracing ("executeMLInt "^string_of_int seq ^" : " ^ml)
  in  executeML ("Control_Isabelle.sendReply "^string_of_int seq^" [" ^ ml ^ "]") end *)

fun store seq exn = let
  val idx = !objectsMax
  val _ = objects := Inttab.update_new (idx, exn) (!objects)
  val _ = objectsMax := idx + 1
  in sendReply seq [idx] end

fun storeMLExnExn seq ml =
  executeML ("let open Control_Isabelle val result = E_ExnExn ("^ml^") in store "^string_of_int seq^" result end")

fun retrieveInt seq id = case Inttab.lookup (!objects) id of
  NONE => error ("no object " ^ string_of_int id)
  | SOME (E_Int i) => sendReply seq [i]
  | SOME _ => error ("expected E_Int, got different exn")

fun retrieveString seq id = case Inttab.lookup (!objects) id of
  NONE => error ("no object " ^ string_of_int id)
  | SOME (E_String str) => sendReplyStr seq str
  | SOME _ => error ("expected E_String, got different exn")


fun applyFunc seq f x = case (Inttab.lookup (!objects) f, Inttab.lookup (!objects) x) of
  (NONE,_) => error ("no object " ^ string_of_int f)
  | (_,NONE) => error ("no object " ^ string_of_int x)
  | (SOME (E_ExnExn f), SOME x) => store seq (f x)
  | _ => error ("object " ^ string_of_int f ^ " is not an E_ExnExn")

(* fun executeML' ml =
  executeML ("local open Control_Isabelle in " ^ ml ^ " end") *)

fun removeObjects ids =
  objects := fold Inttab.delete ids (!objects)

fun int_of_string str = case Int.fromString str of
  NONE => error ("Failed to parse '" ^ str ^ "' as an int")
  | SOME i => i

fun handleLine seq line = (tracing ("COMMAND:"^line);
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
  | #"f" => storeMLExnExn seq (String.extract (line, 1, NONE))

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

  | cmd => error ("Unknown command " ^ str cmd))

fun handleLines' number = case TextIO.inputLine inStream of
    NONE => (TextIO.print "No input\n"; ())
    | SOME line => (handleLine number line; handleLines' (number+1))
    ;;

fun handleLines () = handleLines' 0

end
