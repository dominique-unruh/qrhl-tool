structure ML_Term_Antiquot =
struct

val ml_term_parser = Args.context -- Scan.lift (
Parse.term
-- Scan.optional (\<^keyword>\<open>for\<close> |-- Scan.repeat1 (Args.name --| Parse.$$$ "=" -- Parse.ML_source)) []
--| Scan.ahead Parse.eof)

val ml_typ_parser = Args.context -- Scan.lift (
Parse.typ
-- Scan.optional (\<^keyword>\<open>for\<close> |-- Scan.repeat1 (Args.name --| Parse.$$$ "=" -- Parse.ML_source)) []
--| Scan.ahead Parse.eof)


val print_pair = ML_Syntax.print_pair
val print_string = ML_Syntax.print_string
val print_list = ML_Syntax.print_list
val print_int = ML_Syntax.print_int
val print_indexname = ML_Syntax.print_indexname
val print_sort = ML_Syntax.print_sort
val atomic = ML_Syntax.atomic

type conf = {mlmap: (string * Input.source list)}

fun print_typ conf (Type arg) = "Term.Type " ^ print_pair print_string (print_list (print_typ conf)) arg
  | print_typ conf (TFree (arg as (n,_))) = 
      (case AList.lookup op= (#mlmap conf) n of
          SOME str => atomic (Input.source_content str)
        | NONE => "Term.TFree " ^ print_pair print_string print_sort arg)
  | print_typ _ (TVar arg) = "Term.TVar " ^ print_pair print_indexname print_sort arg

fun print_term conf (Const arg) = "Term.Const " ^ print_pair print_string (print_typ conf) arg
  | print_term conf (Free (arg as (n,_))) =
      (case AList.lookup op= (#mlmap conf) n of
          SOME str => atomic (Input.source_content str)
        | NONE => "Term.Free " ^ print_pair print_string (print_typ conf) arg)
  | print_term conf (Var arg) = "Term.Var " ^ print_pair print_indexname (print_typ conf) arg
  | print_term _ (Bound i) = "Term.Bound " ^ print_int i
  | print_term conf (Abs (s, T, t)) =
      "Term.Abs (" ^ print_string s ^ ", " ^ print_typ conf T ^ ", " ^ print_term conf t ^ ")"
  | print_term conf (t1 $ t2) = "Term.$ " ^ print_pair (print_term conf) (print_term conf) (t1, t2);

fun ml_term (ctxt,(str,mlmap)) =
  let val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
      val trm = Syntax.read_term ctxt str
      val trm_ML = ML_Syntax.atomic (print_term {mlmap=mlmap} trm)
  in
    trm_ML
  end

fun ml_typ (ctxt,(str,mlmap)) =
  let val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
      val trm = Syntax.read_typ ctxt str
      val trm_ML = ML_Syntax.atomic (print_typ {mlmap=mlmap} trm)
  in
    trm_ML
  end


val ml_term_antiquot = ml_term_parser >> ml_term
val ml_typ_antiquot = ml_typ_parser >> ml_typ

end
