structure Cert_Codegen =
struct

type specf = {name: string, pattern: term, inputs: string list, outputs: string list}
type specfx = {name: string, pattern: term, inputs: string list, outputs: string list,
              thms: string list, fallback: string}
type spec = specfx list

fun print_tuple [] = "()"
  | print_tuple [x] = x
  | print_tuple xs = ML_Syntax.atomic (String.concatWith ", " xs)

fun free_to_varT (Type(n,Ts)) = Type(n,map free_to_varT Ts)
  | free_to_varT (TFree (n,T)) = TVar ((n,0),T)
  | free_to_varT (T as TVar _) = T
fun free_to_var (Free(v,T)) = Var((v,0),free_to_varT T)
  | free_to_var (Var(v,T)) = Var(v,free_to_varT T)
  | free_to_var (Abs(v,T,t)) = Abs(v,free_to_varT T,free_to_var t)
  | free_to_var (t $ u) = free_to_var t $ free_to_var u
  | free_to_var (Const(n,T)) = Const (n,free_to_varT T)
  | free_to_var (t as Bound _) = t

fun string_concat_func _ a b = let
  val a' = HOLogic.dest_string a
  val b' = HOLogic.dest_string b
  val c = a' ^ b' |> HOLogic.mk_string
  fun cert () = Goal.prove \<^context> ["a","b","c"] [] (@{ml_term "Trueprop (a @ b = (c::string))" for a=a b=b c=c}) 
                (fn {context,...} => simp_tac context 1)
  in
  (c,cert)
  end

val string_concat_func_spec : specf = {name="string_concat_func", inputs=["a","b"], outputs=["c"],
                                       pattern=\<^prop>\<open>a @ b = (c::string)\<close> |> free_to_var}

fun assert_equals_func ctxt a b = 
  if a <> b then raise TERM("assert_equals_func",[a,b])
  else ((),fn () => infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt a)] @{thm assert_equals_refl})

val assert_equals_func_spec : specf = {name="assert_equals_func", inputs=["a","b"], outputs=[],
                                      pattern=\<^prop>\<open>assert_equals a b\<close> |> free_to_var}


fun assert_string_neq_func _ a b = let
  val a' = HOLogic.dest_string a
  val b' = HOLogic.dest_string b
  val _ = if a' = b' then raise TERM("assert_string_neq_func",[a,b]) else ()
  fun cert () = Goal.prove \<^context> ["a","b"] [] (@{ml_term "Trueprop (assert_string_neq a b)" for a=a b=b}) 
                (fn {context,...} => simp_tac context 1)
  in
    ((),cert)
  end

val assert_string_neq_func_spec : specf = {name="assert_string_neq_func", inputs=["a","b"], outputs=[],
                                      pattern=\<^prop>\<open>assert_string_neq a b\<close> |> free_to_var}

  (* TODO: does not support schematic variables in pattern yet *)
fun NO_MATCH_func ctxt pattern t = let
  val discard_types = map_types (K dummyT)
  in
  if discard_types pattern aconv discard_types t then raise Bind else ((), fn () => 
    infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt pattern), SOME (Thm.cterm_of ctxt t)] @{thm NO_MATCH_I})
  end

val NO_MATCH_func_spec : specf = {name="NO_MATCH_func", pattern=Thm.prop_of @{thm NO_MATCH_I},
  inputs=["x","y"], outputs=[]}

type conf = {
  tracing: bool,
  (* term_vars: string Symtab.table Unsynchronized.ref, (* Names used for variables occurring in terms *) *)
  (* ctxt: Proof.context Unsynchronized.ref,  (* will be returned in the end *) *)
  (* checks: string list Unsynchronized.ref, (* additional checks that have to be performed after the pattern match *)  *)
  current: specfx, (* spec of currently created function *)
  current_assm: term (* currently processed assumption *)
  (* globals: string list Unsynchronized.ref, *)
  (* thms: thm Inttab.table Unsynchronized.ref *)
}
fun empty_conf current = 
    {tracing = true, (* term_vars = Unsynchronized.ref Symtab.empty, *) 
     (* checks = Unsynchronized.ref [], *) (* thms = Unsynchronized.ref Inttab.empty, *)
      (* globals=Unsynchronized.ref [], *) current=current, current_assm = @{prop "dummyterm"}} : conf
(* fun update_conf_pattern ({term_vars,ctxt,checks,current,current_assm...}:conf) pattern = 
  {current=current, current_assm=current_assm, term_vars=term_vars, ctxt=ctxt, checks=checks, pattern=pattern} : conf *)
fun update_conf_current_assm ({tracing,current,...}:conf) current_assm = {tracing=tracing, current=current, current_assm=current_assm}

fun print_comment str = let
  fun quote (#"*" :: #")" :: l) res = quote l (#")" :: #" " :: #"*" :: res)
    | quote (#"(" :: #"*" :: l) res = quote (#"*" :: l) (#" " :: #"(" :: res)
    | quote (x :: l) res = quote l (x :: res)
    | quote [] res = rev res
  val str' = YXML.content_of str
in
  "(* " ^ String.implode (quote (String.explode str') []) ^ " *)"
end

fun print_var_pattern name (ctxt,term_vars,checks) =
    case Symtab.lookup (term_vars) name of
      (* Variable was already seen, use fresh name but add an equality check *)
      SOME name'' => let val (name',ctxt) = ML_Context.variant name ctxt
                         val checks = name'^"="^name'' :: checks
                      in (name',(ctxt,term_vars,checks)) end
      (* Variable was not seen before *)
    | NONE => let val (name',ctxt) = ML_Context.variant name ctxt
                  val term_vars = Symtab.update_new (name,name') term_vars
              in (name',(ctxt,term_vars,checks)) end

fun print_var term_vars name =
    case Symtab.lookup term_vars name of
      SOME name' => name'
    | NONE => error ("Variable "^name^" undeclared")

fun print_typ_pattern (Type (n,Ts)) stuff =
    let val (Ts',stuff) = fold_map print_typ_pattern Ts stuff
    in
      ("Term.Type " ^ print_tuple [ML_Syntax.print_string n, ML_Syntax.print_list I Ts'], stuff)
    end
  | print_typ_pattern (T as TFree _) _ = raise TYPE("print_typ_pattern",[T],[])
  | print_typ_pattern (TVar ((n,_),_)) stuff = print_var_pattern ("t_" ^ String.extract (n,1,NONE)) stuff
      (* TODO: in pattern mode, check sorts *)

fun print_typ termvars (Type arg) = "Term.Type " ^ ML_Syntax.print_pair ML_Syntax.print_string (ML_Syntax.print_list (print_typ termvars)) arg
  | print_typ _ (T as TFree _) = raise TYPE("print_typ",[T],[])
  | print_typ termvars (TVar ((n,_),_)) = print_var termvars ("t_" ^ String.extract (n,1,NONE)) 

fun print_term_pattern (Const (n,T)) stuff = 
    let val (ml,stuff) = print_typ_pattern T stuff
    in
      ("Term.Const " ^ ML_Syntax.print_pair I I (ML_Syntax.print_string n, ml), stuff)
    end
  | print_term_pattern (Free (n,T)) stuff = 
    let val (ml,stuff) = print_typ_pattern T stuff
    in
      ("Term.Free " ^ ML_Syntax.print_pair I I (ML_Syntax.print_string n, ml), stuff)
    end
  | print_term_pattern (Var ((n,_),_)) stuff = print_var_pattern n stuff
      (* TODO: in_pattern mode, check type *)
  | print_term_pattern (Bound i) stuff = ("Term.Bound " ^ ML_Syntax.print_int i, stuff)
  | print_term_pattern (Abs (s, T, t)) stuff =
    let val (mlT,stuff) = print_typ_pattern T stuff
        val (mlt,stuff) = print_term_pattern t stuff
    in
      ("Term.Abs (" ^ ML_Syntax.print_string s ^ ", " ^ mlT ^ ", " ^ mlt ^ ")", stuff)
    end
  | print_term_pattern (t1 $ t2) stuff = 
    let val (ml1,stuff) = print_term_pattern t1 stuff
        val (ml2,stuff) = print_term_pattern t2 stuff
    in
      ("Term.$ " ^ ML_Syntax.print_pair I I (ml1,ml2), stuff)
    end

fun print_term conf (Const arg) = "Term.Const " ^ ML_Syntax.print_pair ML_Syntax.print_string (print_typ conf) arg
  | print_term conf (Free v) = "Term.Free " ^ ML_Syntax.print_pair ML_Syntax.print_string (print_typ conf) v
  | print_term conf (Var ((n,_),_)) = print_var conf n
      (* TODO: in mode, check type *)
  | print_term _ (Bound i) = "Term.Bound " ^ ML_Syntax.print_int i
  | print_term conf (Abs (s, T, t)) =
      "Term.Abs (" ^ ML_Syntax.print_string s ^ ", " ^ print_typ conf T ^ ", " ^ print_term conf t ^ ")"
  | print_term conf (t1 $ t2) = "Term.$ " ^ ML_Syntax.print_pair (print_term conf) (print_term conf) (t1, t2);

fun check_to_val check = "val _ = if (" ^ check ^") then () else raise Bind"

(* fun pull_checks (conf:conf) =
  let val checks = ! (#checks conf)
      val _ = #checks conf := []
  in checks end *)

fun eqterm_to_ml ctxt termvars _ (pattern as Const(@{const_name "Pure.eq"}, _) $ a $ b) =
    let 
        (* val termvars = #term_vars conf |> ! *)
        val (b',(ctxt,termvars,checks)) = print_term_pattern b (ctxt,termvars,[])
        val a' = print_term termvars a 
        val comment = "Assumption: " ^ Syntax.string_of_term ctxt pattern ^ "\n   Handled using pattern matching" |> print_comment
        val code = comment ^ "\nval "^b'^" = "^a'
        val checks = map check_to_val checks
        (* val checks = pull_checks conf |> map check_to_val *)
        val mkcert = "infer_instantiate' ctxt [Thm.cterm_of ctxt ("^b'^") |> SOME] reflexive_thm"
        (* val _ = #term_vars conf := termvars *)
    in
      ((code::checks, mkcert), (termvars,ctxt))
    end
  | eqterm_to_ml _ _ {current,...} t = raise TERM("Don't know how to handle this assumption when creating function '" ^ #name current ^ "'", [t])

(* local
(* TODO: use theory data for this *)
val thms = Synchronized.var "Cert_Codegen.thms" Inttab.empty
in
fun get_thm id = Inttab.lookup (Synchronized.value thms) id |> the
fun thm_antiq (conf:conf) (thm:thm) =
  let val id = serial ()
      val _ = Synchronized.change thms (Inttab.update_new (id,thm))
      val ctxt = ! (#ctxt conf)
      val (var,ctxt) = ML_Context.variant "thm" ctxt
      val prepare = "val " ^ var ^ " = get_thm " ^ ML_Syntax.print_int id
      val retrieve = (* ML_Context.struct_name ctxt ^ "." ^ *) var
      val _ = #ctxt conf := ctxt
  in
    (prepare,retrieve)
  end
end *)

val indent = String.translate (fn c => if c = #"\n" then "\n  " else str c)
fun indent' str = "  " ^ indent str

fun code_for_assumption ctxt termvars (conf:conf) (spec:spec) t = let
  val conf = update_conf_current_assm conf t
  (* val _ = if null (! (#checks conf)) then () else error "code_for_assumption: checks not empty (1)" *)
  val code = Library.get_first (fn {name,pattern,inputs,outputs,...} => 
            let val _ = if (fastype_of pattern <> propT) then raise TERM("code_for_assumption: not prop",[pattern]) else ()
                (* val _ = if null (! (#checks conf)) then () else error "code_for_assumption: checks not empty" *)
                (* val ctxt = ! (#ctxt conf) (* Now we maintain current context in ctxt *) *)
(* val _ = @{print} (pattern |> Thm.cterm_of ctxt, t |> Thm.cterm_of ctxt) *)
(* val _ = @{print} (Pattern.first_order_match (Proof_Context.theory_of ctxt) (pattern,t) (Vartab.empty,Vartab.empty)) *)
                val (_,tenv) = Pattern.first_order_match (Proof_Context.theory_of ctxt) (pattern,t) (Vartab.empty,Vartab.empty)
                (* val termvars = ! (#term_vars conf) *)
                val inputs = inputs |> map (fn v => Vartab.lookup tenv (v,0) |> the |> snd |> print_term termvars
                                             |> ML_Syntax.atomic)
                val (outputs,(ctxt,termvars,checks)) = fold_map (fn v => fn stuff => 
                                let val t = Vartab.lookup tenv (v,0) |> the |> snd
                                    val (pat,stuff) = print_term_pattern t stuff
                                in (ML_Syntax.atomic pat, stuff) end) outputs (ctxt,termvars,[])
                val (certvar,ctxt) = ML_Context.variant "cert" ctxt
                val comment = "Assumption: " ^ Syntax.string_of_term ctxt t ^ "\n   Handled using function " ^ name |> print_comment
                val code = comment ^ "\nval " ^ ML_Syntax.atomic (ML_Syntax.atomic (String.concatWith ", " outputs) ^ ", "^certvar) 
                      ^ "\n         = " ^ name ^ " ctxt " ^ String.concatWith " " inputs
                val checks = map check_to_val checks
                (* val _ = #ctxt conf := ctxt *)
                (* val _ = #term_vars conf := termvars *)
            in SOME ((code::checks, certvar ^ " ()"), (termvars,ctxt))
            end
            handle Pattern.MATCH => NONE) spec
  (* val _ = if null (! (#checks conf)) then () else error "code_for_assumption: checks not empty (2)" *)
  val code = case code of SOME c => c | NONE => eqterm_to_ml ctxt termvars conf t
  (* val code = apsnd indent code *)
  (* val _ = #current_assm conf := @{term "dummyterm"} *)
  (* val _ = if null (! (#checks conf)) then () else error "code_for_assumption: checks not empty (3)" *)
  in
    code
  end

(* Returns a function. 
   Computes the variables in "outputs" using thm.
   Raises Bind if the pattern from thm is not matched, or if the preconditions cannot be fulfilled.
 *)
fun thm_to_fun ctxt (conf:conf) spec thmname funname inputs outputs = let
  (* val _ = if null (! (#checks conf)) then () else error "thm_to_fun (1): checks not empty" *)
  (* val term_vars_orig = ! (#term_vars conf) *)
  (* val _ = #term_vars conf := Symtab.empty *)
(* val _ = @{print} inputs *)
(* val _ = @{print} conf *)
  val (inputs',(ctxt,termvars,checks)) = fold_map print_var_pattern inputs (ctxt,Symtab.empty,[])
  (* val inputs' = map (print_var_pattern conf) inputs *)
(* val _ = @{print} (#checks conf) *)
  val _ = if null checks then () else error "thm_to_fun (1b): checks not empty"
(* val _ = @{print} "xxx" *)
  val thm = Proof_Context.get_thm ctxt thmname
  (* val _ = #term_vars conf := termvars *)
  val ((vals,certs),(termvars,ctxt)) =
    fold_map (fn prem => fn (termvars,ctxt) => code_for_assumption ctxt termvars conf spec prem) (Thm.prems_of thm) (termvars,ctxt) |> apfst split_list
  val vals = flat vals
  (* val termvars = #term_vars conf |> ! *)
  (* val _ = if null (! (#checks conf)) then () else error "thm_to_fun (2): checks not empty" *)
  val mkcert_name = "mkcert"
  (* val _ = #globals conf := prep :: ! (#globals conf) *)
  val insts = Term.add_vars (Thm.prop_of thm) [] |> rev |> map (fn ((n,_),_) => print_var termvars n)
              |> String.concatWith ", " |> enclose "[" "]" |> (fn c => "(map (SOME o Thm.cterm_of ctxt) "^c^")")
  val mkcert = "fun "^mkcert_name^" () = (infer_instantiate' ctxt "^insts^" @{thm " ^ ML_Syntax.print_string thmname ^ "}) OF [" ^ 
              String.concatWith ", " certs ^ "]"
  val steps = vals @ [mkcert]
  val outputs' = map (print_var termvars) outputs
  val comment = thmname ^ ": " ^ (thm |> Thm.prop_of |> Syntax.string_of_term ctxt) |> print_comment
  val code = comment ^ "\nfun " ^ funname ^ " " ^ String.concatWith " " inputs' ^ " = let\n"^
    String.concatWith "\n" (map indent' steps) ^ "\nin " ^ 
    print_tuple [print_tuple outputs', mkcert_name] ^ " end\n"
  (* val _ = #term_vars conf := term_vars_orig *)
  in
    code
  end

fun thms_to_fun ctxt (spec:spec) (func:specfx) =
  let 
      val (thm_names,ctxt) = fold_map (fn n => fn ctxt => let val (n',ctxt) = ML_Context.variant n ctxt in ((n,n'),ctxt) end) (#thms func) ctxt
      (* val named_thms = #thms func |> map (fn name => (name,Proof_Context.get_thm ctxt name)) *)
(* Library.map_index (fn (i,thm) => ("alternative_"^string_of_int i, thm)) (#thms func) *)
      val concls = #thms func |> map (Thm.concl_of o Proof_Context.get_thm ctxt)
      val discard_types = map_types (K dummyT)
      val pattern' = discard_types (#pattern func)
      val _ = if not (List.all (fn c => discard_types c=pattern') concls)
              then raise TERM("thms_to_fun",#pattern func::concls)
              else ()
      val conf = empty_conf func
      (* val (inputs,(ctxt,termvars,checks)) = fold_map print_var_pattern (#inputs func) (ctxt,Symtab.empty,[]) *)
      val (inputs,ctxt) = fold_map ML_Context.variant (#inputs func) ctxt
      (* val _ = if null checks then () else error "thms_to_fun: checks not empty" *)
      (* val named_thms = Library.map_index (fn (i,thm) => ("alternative_"^string_of_int i, thm)) (#thms func) *)
      val fundefs = map (fn (thm,funname) => thm_to_fun ctxt conf spec thm funname (#inputs func) (#outputs func)) thm_names
            |> map indent'
      val inputs' = " " ^ String.concatWith " " inputs
      val tracing_cmd = "  val _ = " ^ ML_Syntax.print_string ("Invoking: " ^ #name func ^ " ") ^ " ^ " ^ 
            String.concatWith " ^\" \"^ " (inputs |> map (fn s => "(Syntax.string_of_term ctxt "^s^")")) ^
            " |> tracing"
      val fundefs = if #tracing conf then fundefs @ [tracing_cmd] else fundefs
      val body = fold (fn snippet => fn sofar => if sofar="" then snippet ^ inputs' else sofar ^ " handle Bind => " ^ snippet ^ inputs') (map snd thm_names) ""
      val body = body ^ " handle Bind => " ^ ML_Syntax.atomic (#fallback func) ^ " " ^ print_tuple inputs
      val code = #name func ^ " ctxt" ^ inputs' ^ " = let\n" ^ String.concatWith "\n" fundefs ^ "\nin\n" ^  body ^ "\nend\n\n"
      (* val preps = rev (! (#globals conf)) *)
  in
    code
  end

fun thms_to_funs ctxt (spec:spec) structname filename =
  let val spec' = filter_out (fn {fallback,thms,...} => fallback="" andalso null thms) spec
      val ctxt = fold (fn func => fn ctxt => ML_Context.variant (#name func) ctxt |> snd) spec ctxt
      val codes = map (thms_to_fun ctxt spec) spec'
      (* val prep = String.concatWith "\n" preps *)
      (* val prep = String.concatWith "\n" (flat preps) *)
      val code = "structure " ^ structname ^ " =\nstruct\n\nfun " ^ String.concatWith "\nand " codes ^ "\nend\n"
      val path = Path.append (Resources.master_directory (Proof_Context.theory_of ctxt)) (Path.make [filename])
      val _ = File.write path code
      val _ = ML_Context.eval_file ML_Compiler.flags path
(* val _ = writeln prep *)
(* val _ = writeln code *)
  in
    ()
  end

end
