structure Cert_Codegen =
struct

type specf = {name: string, pattern: term, inputs: string list, outputs: string list}
type specfx = {name: string, pattern: term, inputs: string list, outputs: string list,
              thms: string list, fallback: string}
type spec = specfx list

fun specf_to_specfx ({name,inputs,outputs,pattern} : specf) = {name=name,fallback="",inputs=inputs,outputs=outputs,pattern=pattern,thms=[]} : specfx
fun specfx_to_specf ({name,inputs,outputs,pattern,...} : specfx) = {name=name,inputs=inputs,outputs=outputs,pattern=pattern} : specf
fun specfx_to_specf' structname ({name,inputs,outputs,pattern,...} : specfx) = {name=structname^"."^name,inputs=inputs,outputs=outputs,pattern=pattern} : specf

structure Data = Theory_Data(
  type T = specf list
  val empty = []
  val merge = Library.merge op=
  val extend = I
)

fun add_specs specs = Data.map (fn s => specs @ s)
fun add_spec spec = add_specs [spec]

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

(* Returns a term %(v1,..,vn). t (v1,...,vn) and a certificate t == %(v1,..,vn). t (v1,...,vn) *)
fun mk_tupled_lambda ctxt vs t = let
  val vnames = vs |> map fst |> Name.variant_list []
  val vs' = (vnames ~~ map snd vs) |> map Free
  val tuple = HOLogic.mk_tuple vs'
  val tT = fastype_of t
  val lambda = HOLogic.tupled_lambda tuple (Var(("t",0),tT) $ tuple)
  val lambda' = Term.subst_Vars [(("t",0),t)] lambda
  fun cert () = case vs of
      [] => infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt t)] @{thm unit_abs_eta_conv[symmetric, THEN eq_reflection]} |> \<^print>
    | [_] => Thm.eta_conversion (Thm.cterm_of ctxt lambda') |> Thm.symmetric
    | _ => let
      (* val thm = infer_instantiate ctxt [(("x",0),lambda |> Thm.cterm_of ctxt)] @{thm reflexive} *)
      val lambda'' = Term.subst_Vars [(("t",0),Free("t",tT))] lambda
      val _ = \<^print> lambda'' 
      val thm = case eta_proc ctxt lambda'' of SOME thm => thm | NONE => raise TYPE("mk_tupled_lambda",map snd vs,[t,lambda''])
      val thm = Thm.generalize ([],["t"]) 2 thm
      val thm = Thm.symmetric thm
      val thm = Thm.instantiate ([],[((("t",2),tT), Thm.cterm_of ctxt t)]) thm
      val _ = thm |> Thm.prop_of |> \<^print>
      in thm end
  in
    (lambda',cert)
  end

(* ;;
val _ = mk_tupled_lambda \<^context> [("x",\<^typ>\<open>unit\<close>)] @{term "xxx::unit\<Rightarrow>int"} 
|> (fn x => snd x ()) |> Thm.prop_of |> \<^print>
;; *)

fun list_last ctxt t = let
  val list = HOLogic.dest_list t
  val lT = fastype_of t
  val T = lT |> dest_Type |> snd |> the_single
  val (l1,t2) = split_last list
  val t1 = HOLogic.mk_list T l1
  fun cert () = let
    val lhs = Const(\<^const_name>\<open>append\<close>, lT-->lT-->lT) $ t1 $ HOLogic.mk_list T [t2] |> Thm.cterm_of ctxt
    fun conv ct = (((Conv.rewr_conv @{thm List.append.append_Cons[THEN eq_reflection]}) then_conv Conv.arg_conv conv)
                  else_conv (Conv.rewr_conv @{thm List.append.left_neutral[THEN eq_reflection]})) ct
    val thm = conv lhs 
    val thm = @{thm list_lastI} OF [thm]
  in thm end
in
  ((t1,t2),cert)
end

val list_last_spec = {name="Cert_Codegen.list_last", inputs=["list"], outputs=["xs","x"],
  pattern=\<^prop>\<open>list_last list xs x\<close> |> free_to_var} : specf

fun string_concat_func _ a b = let
  val a' = HOLogic.dest_string a
  val b' = HOLogic.dest_string b
  val c = a' ^ b' |> HOLogic.mk_string
  fun cert () = Goal.prove \<^context> ["a","b","c"] [] (@{ml_term "Trueprop (a @ b = (c::string))" for a=a b=b c=c}) 
                (fn {context,...} => simp_tac context 1)
  in
  (c,cert)
  end

val string_concat_func_spec : specf = {name="Cert_Codegen.string_concat_func", inputs=["a","b"], outputs=["c"],
                                       pattern=\<^prop>\<open>a @ b = (c::string)\<close> |> free_to_var}

fun assert_equals_func ctxt a b = 
  if a <> b then raise TERM("assert_equals_func",[a,b])
  else ((),fn () => infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt a)] @{thm assert_equals_refl})

val assert_equals_func_spec : specf = {name="Cert_Codegen.assert_equals_func", inputs=["a","b"], outputs=[],
                                      pattern=\<^prop>\<open>assert_equals a b\<close> |> free_to_var}

fun constant_function ctxt (Abs(_,T,body)) = let
  val _ = if loose_bvar (body,0) then raise Bind else ()
  fun cert () = let
    val cT = Thm.ctyp_of ctxt T
    val cbody = Thm.cterm_of ctxt body
    val bodycT = Thm.ctyp_of_cterm cbody
    val bodyT = Thm.typ_of bodycT
    in instantiate_normalize ([((("'a",0),\<^sort>\<open>type\<close>),cT),
                               ((("'b",0),\<^sort>\<open>type\<close>),bodycT)],[
                               ((("y",0),bodyT),cbody)]) @{thm constant_function_absI} end
    (* infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt body)] @{thm constant_function_absI} *)
  in (body,cert) end
  | constant_function _ _ = raise Bind
val constant_function_spec = {name="Cert_Codegen.constant_function", inputs=["f"], outputs=["y"], pattern=\<^prop>\<open>constant_function f y\<close> |> free_to_var} : specf


fun assert_string_neq_func _ a b = let
  val a' = HOLogic.dest_string a
  val b' = HOLogic.dest_string b
  val _ = if a' = b' then raise TERM("assert_string_neq_func",[a,b]) else ()
  fun cert () = Goal.prove \<^context> ["a","b"] [] (@{ml_term "Trueprop (assert_string_neq a b)" for a=a b=b}) 
                (fn {context,...} => simp_tac context 1)
  in
    ((),cert)
  end

val assert_string_neq_func_spec : specf = {name="Cert_Codegen.assert_string_neq_func", inputs=["a","b"], outputs=[],
                                      pattern=\<^prop>\<open>assert_string_neq a b\<close> |> free_to_var}

  (* TODO: does not support schematic variables in pattern yet *)
fun NO_MATCH_func ctxt pattern t = let
  val discard_types = map_types (K dummyT)
  in
  if discard_types pattern aconv discard_types t then raise Bind else ((), fn () => 
    infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt pattern), SOME (Thm.cterm_of ctxt t)] @{thm NO_MATCH_I})
  end

val NO_MATCH_func_spec : specf = {name="Cert_Codegen.NO_MATCH_func", pattern=Thm.prop_of @{thm NO_MATCH_I},
  inputs=["x","y"], outputs=[]}

type conf = {
  tracing: bool,
  current: specfx, (* spec of currently created function *)
  current_assm: term (* currently processed assumption *)
}
fun empty_conf current = 
    {tracing = false,
     current=current,
     current_assm = @{prop "dummyterm"}} : conf
fun update_conf_current_assm ({tracing,current,...}:conf) current_assm = 
  {tracing=tracing, current=current, current_assm=current_assm} : conf

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
  | print_typ_pattern (TVar ((n,_),_)) stuff = print_var_pattern (* ("t_" ^ String.extract (n,1,NONE)) *)n stuff
      (* TODO: in pattern mode, check sorts *)

fun print_typ termvars (Type arg) = "Term.Type " ^ ML_Syntax.print_pair ML_Syntax.print_string (ML_Syntax.print_list (print_typ termvars)) arg
  | print_typ _ (T as TFree _) = raise TYPE("print_typ",[T],[])
  | print_typ termvars (TVar ((n,_),_)) = print_var termvars (* ("t_" ^ String.extract (n,1,NONE)) *) n 

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

fun code_for_assumption ctxt termvars (conf:conf) (spec:specf list) t = let
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
  val code = case code of SOME c => c | NONE =>
    (case t of Const(@{const_name Pure.eq},_) $ _ $ _ => eqterm_to_ml ctxt termvars conf t
             | Const(@{const_name Pure.all},_) $ Abs(_,_,_) => code_for_assumption_allquant ctxt termvars (conf:conf) (spec:specf list) t
             | _ => raise TERM("Don't know how to handle this assumption when creating function '" ^ #name (#current conf) ^ "'", [t]))
  (* val code = apsnd indent code *)
  (* val _ = #current_assm conf := @{term "dummyterm"} *)
  (* val _ = if null (! (#checks conf)) then () else error "code_for_assumption: checks not empty (3)" *)
  in
    code
  end

and code_for_assumption_allquant ctxt termvars (conf:conf) (spec:specf list) assm = let
  val vars = Term.add_vars assm [] |> map (fst o fst)
  val (Const(@{const_name Pure.all}, _) $ Abs(z,T,body)) = assm
  val [z'] = Name.variant_list vars [z]  (* Fresh name for schematic var z *)
  (* val ((z,T),assm') = Logic.dest_all assm *)
  val assm' = Term.subst_bound (Var((z',0),T), body)
  (* val _ = (z,T) |> @{print} *)
  (* val _ = assm' |> Thm.cterm_of ctxt *)
  val outputs = vars |> filter (not o Symtab.defined termvars)
  val inputs = vars |> filter (Symtab.defined termvars)
  val inoutputs = inputs @ outputs
  val inoutputs_z = Name.variant_list (z'::vars) (inoutputs |> map (fn n => n ^ "_" ^ z))
  val (_,(ctxt,termvars,[])) = print_var_pattern z' (ctxt,termvars,[])
  val subst = inoutputs ~~ inoutputs_z |> Symtab.make
(* val _ = @{print} subst *)

  fun s (t as Var((n,0),T') $ Var v) =
      (case (Symtab.lookup subst n, v=((z',0),T)) of
        (SOME nz, true) => Var((nz,0),T' |> dest_funT |> snd)
      | _ => t)
    | s (t1 $ t2) = s t1 $ s t2
    | s (Abs(n,T,t)) = Abs(n,T,s t)
    | s t = t
  val assm'' = s assm'

  val z'' = print_var termvars z'
  val z_def_code = "val " ^ z'' ^ " = Free(" ^ ML_Syntax.print_string (z'^"_") ^" ^ serial_string(), " ^ print_typ termvars T ^")"

  val (code_inputs_z,(termvars,ctxt)) = fold_map (fn v => fn (termvars,ctxt) => let
      val vz = Symtab.lookup subst v |> the
      val v' = print_var termvars v
      val (vz',(ctxt,termvars,[])) = print_var_pattern vz (ctxt,termvars,[])
      val codeline = "val " ^ vz' ^ " = betapply (" ^ v' ^","^ z'' ^")"
    in (codeline,(termvars,ctxt)) end)
    inputs (termvars,ctxt)

  val ((code,cert'),(termvars,ctxt)) = code_for_assumption ctxt termvars conf spec assm''
  val code = z_def_code :: code_inputs_z @ code
  
  val comment = "Assumption: " ^ Syntax.string_of_term ctxt assm ^ "\n   Handled by stripping all-quantifier" |> print_comment
  
  fun abscode1 v (ctxt,termvars,checks) = let 
    val vz = Symtab.lookup subst v |> the
    val (v',(ctxt,termvars,checks)) = print_var_pattern v (ctxt,termvars,checks)
    val vz' = print_var termvars vz
    in ("val "^v'^" = Cert_Codegen.absfree' "^ML_Syntax.print_string z^" (dest_Free "^z''^") "^vz', 
        (ctxt,termvars,checks)) end
  val (abscode,(ctxt,termvars,checks)) = fold_map abscode1 outputs (ctxt,termvars,[])
  val _ = if null checks then () else error "code_for_assumption_allquant: checks not empty"
  val (certvar,ctxt) = ML_Context.variant "cert" ctxt
  val certcode = "fun "^certvar^" () = Cert_Codegen.generalize_thm_to ctxt " ^ ML_Syntax.atomic cert' ^ " (dest_Free " ^ z'' ^")\n               "
   ^ ML_Syntax.atomic (print_term termvars assm)
  val code = code @ comment :: abscode @ [certcode]
  
  val termvars = fold Symtab.delete (z'::inoutputs_z) termvars
in ((code,certvar^" ()"),(termvars,ctxt)) end

(* transforms thm="A1=>A2=>...=>An=>B" into B given prems=[A1,...,An]
  B is beta reduced, and all premises have to match up to beta equivalence
 *)
local
val beta_red = Conv.fconv_rule (Thm.beta_conversion true)
in
fun implies_elim_multi_beta thm prems = fold (fn prem => fn thm => Thm.implies_elim thm (beta_red prem)) prems (beta_red thm)
end

fun absfree' n (a,T) body = Abs (n, T, abstract_over (Free (a, T), body))

fun find_type_of_vars t vs = let
  val vars = Term.add_vars t []
  fun find v = case List.find (fn (n,_) => n=(v,0)) vars of 
                  NONE => raise TERM("find_type_of_vars: "^v,[t])
                | SOME ((n,_),T) => (n,T)
in
  map find vs
end

(* Returns a function. 
   Computes the variables in "outputs" using thm.
   Raises Bind if the pattern from thm is not matched, or if the preconditions cannot be fulfilled.
 *)
fun thm_to_fun ctxt (conf:conf) (spec:specf list) thmname funname inputs outputs = let
  val (inputs',(ctxt,termvars,checks)) = fold_map print_var_pattern inputs (ctxt,Symtab.empty,[])
  val _ = if null checks then () else error "thm_to_fun (1b): checks not empty"
  val thm = Proof_Context.get_thm ctxt thmname
  val input_typs = find_type_of_vars (Thm.concl_of thm) inputs
  val (vals0,(ctxt,termvars,checks)) = fold_map (fn (n,T) => fn stuff => 
              let val (Tpat,stuff) = print_typ_pattern T stuff 
              in ("val " ^ Tpat ^ " = fastype_of " ^ print_var termvars n,stuff) end)
          input_typs (ctxt,termvars,[])
  val vals0 = vals0 @ map check_to_val checks 
(* |> @{print} *)
  val ((vals,certs),(termvars,ctxt)) =
    fold_map (fn prem => fn (termvars,ctxt) => code_for_assumption ctxt termvars conf spec prem) (Thm.prems_of thm) (termvars,ctxt) |> apfst split_list
  val vals = flat vals
  val (mkcert_name,ctxt) = ML_Context.variant "mkcert" ctxt
  val insts = Term.add_vars (Thm.prop_of thm) [] |> rev |> map (fn ((n,_),_) => print_var termvars n)
              |> String.concatWith ", " |> enclose "[" "]" |> (fn c => "(map (SOME o Thm.cterm_of ctxt) "^c^")")
  (* TODO: make sure the result is not beta_reduced (using rewrite_thm_as) (or specify that certificates are up to beta-conv?) *)
  val mkcert = "fun "^mkcert_name^" () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt "^insts^" @{thm " ^ ML_Syntax.print_string thmname ^ "}) [" ^ 
              String.concatWith ", " certs ^ "]"
  val steps = vals0 @ vals @ [mkcert]
  val outputs' = map (print_var termvars) outputs
  val comment = thmname ^ ": " ^ (thm |> Thm.prop_of |> Syntax.string_of_term ctxt) |> print_comment
  val code = comment ^ "\nfun " ^ funname ^ " " ^ String.concatWith " " inputs' ^ " = let\n"^
    String.concatWith "\n" (map indent' steps) ^ "\nin " ^ 
    print_tuple [print_tuple outputs', mkcert_name] ^ " end\n"
  in
    code
  end                                               

fun term_tuple_to_string n = let
  val vars = Library.map_range (fn i => "x"^string_of_int i) n
  in "(fn (" ^ String.concatWith "," vars ^ ") => String.concatWith \" \" [" ^ 
      String.concatWith "," (map (fn v => "Syntax.string_of_term ctxt "^v) vars) ^ "])" end

;;
val _ = term_tuple_to_string 4 |> writeln
;;

fun thms_to_fun ctxt (spec:specf list) (func:specfx) =
  let 
      val (thm_names,ctxt) = fold_map (fn n => fn ctxt => let val (n',ctxt) = ML_Context.variant n ctxt in ((n,n'),ctxt) end) (#thms func) ctxt
      val concls = #thms func |> map (Thm.concl_of o Proof_Context.get_thm ctxt)
      val discard_types = map_types (K dummyT)
      val pattern' = discard_types (#pattern func)
      val _ = if not (List.all (fn c => discard_types c=pattern') concls)
              then raise TERM("thms_to_fun",#pattern func::concls)
              else ()
      val conf = empty_conf func
      val (inputs,ctxt) = fold_map ML_Context.variant (#inputs func) ctxt
      val fundefs = map (fn (thm,funname) => thm_to_fun ctxt conf spec thm funname (#inputs func) (#outputs func)) thm_names
            |> map indent'
      val inputs' = " " ^ String.concatWith " " inputs
      val tracing_cmd = "  val _ = " ^ ML_Syntax.print_string ("Invoking:  " ^ #name func ^ " ") ^ " ^ " ^ 
            String.concatWith " ^\" \"^ " (inputs |> map (fn s => "(\"\<open>\" ^ Syntax.string_of_term ctxt "^s^" ^ \"\<close>\")")) ^
            " |> tracing"
      val fundefs = if #tracing conf then fundefs @ [tracing_cmd] else fundefs
      val body = fold (fn snippet => fn sofar => if sofar="" then snippet ^ inputs' else sofar ^ " handle Bind => " ^ snippet ^ inputs') (map snd thm_names) ""
      val (result_var,ctxt) = ML_Context.variant "result" ctxt
      val body = "  val " ^ result_var ^ " = " ^ body ^ " handle Bind => " ^ ML_Syntax.atomic (#fallback func) ^ " " ^ print_tuple inputs
      val fundefs = fundefs @ [body]
      val tracing_cmd2 = "  val _ = " ^ ML_Syntax.print_string ("Returning: " ^ #name func ^ " -> ") ^ " ^ " 
             ^ term_tuple_to_string (length (#outputs func)) ^ " (fst " ^ result_var ^ ") |> tracing"
      val fundefs = if #tracing conf then fundefs @ [tracing_cmd2] else fundefs
      val code = #name func ^ " ctxt" ^ inputs' ^ " = let\n" ^ String.concatWith "\n" fundefs ^ "\nin\n" ^  result_var ^ "\nend\n\n"
  in
    code
  end

fun thms_to_funs (spec:spec) structname filename thy =
  (* TODO: assert that all vars in spec have index 0 *)
  let 
      val ctxt = Proof_Context.init_global thy (* This context will be discarded in the end *)
      val allspec = map specfx_to_specf spec @ Data.get thy
      (* val spec' = filter_out (fn {fallback,thms,...} => fallback="" andalso null thms) spec *)
      val ctxt = fold (fn func => fn ctxt => ML_Context.variant (#name func) ctxt |> snd) allspec ctxt
      val codes = map (thms_to_fun ctxt allspec) spec
      (* val prep = String.concatWith "\n" preps *)
      (* val prep = String.concatWith "\n" (flat preps) *)
      val code = "structure " ^ structname ^ " =\nstruct\n\nfun " ^ String.concatWith "\nand " codes ^ "\nend\n"
      val path = Path.append (Resources.master_directory (Proof_Context.theory_of ctxt)) (Path.make ["autogenerated",filename])
      val _ = File.write path code
      val pos = Path.position path
      val src = ML_Lex.read_pos pos (File.read path)
      val thy = Context.theory_map (ML_Context.exec (fn () => ML_Context.eval ML_Compiler.flags pos src)) thy
      val thy = add_specs (map (specfx_to_specf' structname) spec) thy
(* val _ = writeln prep *)
(* val _ = writeln code *)
  in
    thy
  end

fun rewrite_thm_as thm ct = let
  val eq = Thm.transitive (Thm.beta_conversion true (Thm.cprop_of thm)) (Thm.beta_conversion true ct |> Thm.symmetric)
  val thm' = Thm.equal_elim eq thm
  in thm' end

fun generalize_thm_to ctxt thm (v,T) prop = let
  val thm' = thm |> (* Thm.generalize ([],["v"]) 0 |>  *) Thm.forall_intr (Thm.cterm_of ctxt (Free(v,T)))
  val thm'' = rewrite_thm_as thm' (Thm.cterm_of ctxt prop)
  in thm'' end

end
