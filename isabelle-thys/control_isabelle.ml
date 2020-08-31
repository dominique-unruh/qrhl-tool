structure Control_Isabelle : sig
  val sendReply : int -> int list -> unit
  val handleLines : unit -> unit
  exception E_ExnExn of exn -> exn
  exception E_Int of int
  val store : int -> exn -> unit
  val numObjects : unit -> int
end
=
struct
val inStream = TextIO.openIn inputPipeName
val outStream = TextIO.openOut outputPipeName

val objectsMax = Unsynchronized.ref 0
val objects : exn Inttab.table Unsynchronized.ref = Unsynchronized.ref Inttab.empty

fun numObjects () = Inttab.fold (fn _ => fn i => i+1) (!objects) 0

fun sendReply int ints = let
  (* val _ = OS.Process.sleep (seconds 0.1) *)
  val str = (String.concatWith " " (map string_of_int (int::ints)) ^ "\n")
  val _ = tracing ("sendReply: "^str)
  val _ = TextIO.output (outStream, str)
  val _ = TextIO.flushOut outStream
  in () end

exception E_ExnExn of exn -> exn
exception E_Int of int

fun executeML ml =
  ML_Compiler.eval (ML_Compiler.verbose true ML_Compiler.flags) Position.none (ML_Lex.tokenize ml)

fun executeMLInt seq ml = let
  val _ = tracing ("executeMLInt "^string_of_int seq ^" : " ^ml)
  in  executeML ("Control_Isabelle.sendReply "^string_of_int seq^" [" ^ ml ^ "]") end

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

fun applyFunc seq f x = case (Inttab.lookup (!objects) f, Inttab.lookup (!objects) x) of
  (NONE,_) => error ("no object " ^ string_of_int f)
  | (_,NONE) => error ("no object " ^ string_of_int x)
  | (SOME (E_ExnExn f), SOME x) => store seq (f x)
  | _ => error ("object " ^ string_of_int f ^ " is not an E_ExnExn")

fun executeML' ml =
  executeML ("local open Control_Isabelle in " ^ ml ^ " end")

fun removeObjects ids =
  objects := fold Inttab.delete ids (!objects)

fun int_of_string str = case Int.fromString str of
  NONE => error ("Failed to parse '" ^ str ^ "' as an int")
  | SOME i => i

fun handleLine seq line = (tracing ("COMMAND:"^line);
  case String.sub (line, 0) of
    (* Mxxx - executes ML code xxx *)
    #"M" => executeML' (String.extract (line, 1, NONE))
    (* ixxx - executes ML expression xxx (of type int) and gives response 'seq result' *)
  | #"i" => executeMLInt seq (String.extract (line, 1, NONE))
    (* snnn - Parses nnn as integer, stores result as object, response 'seq object#' *)
  | #"s" => store seq (E_Int (int_of_string (String.extract (line, 1, NONE))))
    (* fxxx - Parses xxx as ML function of type exn \<rightarrow> exn, stores xxx as object #seq *)
  | #"f" => storeMLExnExn seq (String.extract (line, 1, NONE))
    (* rID - Parses ID as object# and returns the object, assuming it's (E_Int i), response 'seq i' *)
  | #"r" => retrieveInt seq (int_of_string (String.extract (line, 1, NONE)))
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