structure Expressions = struct

local open Prog_Variables in

fun mk_expressionT T = \<^typ>\<open>cl\<close> --> T
fun mk_expression2T T = \<^typ>\<open>cl2\<close> --> T

val clean_expression_conv_simpset = 
  \<^context>
  |> Simplifier.init_simpset @{thms
      getter_setter_same[THEN eq_reflection]
      getter_setter_compat[THEN eq_reflection]
      add_index_to_expression_aux1
      add_index_to_expression_aux2
  } |> simpset_of
(* TODO: Implement this without using simplifier *)
fun clean_expression_conv ctxt = let
  val outer_simpset = simpset_of ctxt
  val simpset_ctxt = put_simpset clean_expression_conv_simpset ctxt
  fun prover ctxt = SINGLE (ALLGOALS (distinct_vars_tac (put_simpset outer_simpset ctxt)))
in
   Raw_Simplifier.rewrite_cterm (false,true,false) prover simpset_ctxt
   then_conv normalize_register_conv2 ctxt
end

fun variable_shortname n NoIndex = n
  | variable_shortname n Index1 = n ^ "1"
  | variable_shortname n Index2 = n ^ "2"

fun varterm_to_variable2_shortform Classical VTUnit = \<^term>\<open>empty_cregister :: unit c2variable\<close>
  | varterm_to_variable2_shortform Quantum VTUnit = \<^term>\<open>empty_qregister :: unit q2variable\<close>
  | varterm_to_variable2_shortform _ (VTSingle (name,NoIndex,T)) =
          raise error ("varterm_to_variable2_shortform: not an indexed variable: " ^ name)
  | varterm_to_variable2_shortform Classical (VTSingle (name,idx,T)) =
          Free (variable_shortname name idx, mk_c2variableT T)
  | varterm_to_variable2_shortform Quantum (VTSingle (name,idx,T)) =
          Free (variable_shortname name idx, mk_q2variableT T)
  | varterm_to_variable2_shortform cq (VTCons (t1, t2)) = let
        val v1 = varterm_to_variable2_shortform cq t1
        val v2 = varterm_to_variable2_shortform cq t2
        val T1 = case cq of Classical => dest_c2variableT (fastype_of v1) | Quantum => dest_q2variableT (fastype_of v1)
        val T2 = case cq of Classical => dest_c2variableT (fastype_of v2) | Quantum => dest_q2variableT (fastype_of v2)
        val T = HOLogic.mk_prodT (T1, T2)
        val pair = case cq of Classical => Const(\<^const_name>\<open>cregister_pair\<close>, fastype_of v1 --> fastype_of v2 --> mk_c2variableT T)
                            | Quantum => Const(\<^const_name>\<open>qregister_pair\<close>, fastype_of v1 --> fastype_of v2 --> mk_q2variableT T)
      in pair $ v1 $ v2 end



(* Translates expression in longform to expression in shortform *)
fun expression_to_term ctxt t =
  let val lookup_var = lookup_variable ctxt
      val memT = case fastype_of t of \<^Type>\<open>fun T _\<close> => T | T => raise TYPE("expression_to_term: expression should have function type", [T], [t])
      val e = betapply (t, Free("_memory", memT)) |> Envir.beta_eta_contract
(*       fun check_qvariable n T = case lookup_var n of
          SOME {qc=Classical, ...} => raise TYPE("expression_to_term: classical variable after qregister_chain", [T], [t])
        | SOME {qc=Quantum, in_typ, ...} => 
            mk_qvariableT in_typ = T orelse raise TYPE("expression_to_term: quantum variable of wrong type", [T, in_typ], [t])
        | NONE => false *)
      fun translate (g as (Const(\<^const_name>\<open>getter\<close>,_) $ var $ Free("_memory", _))) = let
            val (cq,n,i,T) = case decompose_singleton_variable ctxt var of
               SOME v => v
               | NONE => 
                    raise TYPE("expression_to_term: not a known variable after getter", [fastype_of var], [t,g])
            val _ = mk_cvariableT T = fastype_of var orelse  mk_c2variableT T = fastype_of var orelse
                    raise TYPE("expression_to_term: classical variable of wrong type", [T, fastype_of var], [t,g])
          in Free(variable_shortname n i,T) end
        | translate (Free("_memory", _)) = raise TERM("expression_to_term: encountered memory access without getter", [t,e])
        | translate t = case decompose_singleton_variable ctxt t of
            NONE => (case t of (t1 $ t2) => translate t1 $ translate t2 | (Abs(n,T,body)) => Abs(n, T, translate body) | t => t)
            | SOME (cq,n,i,T) => Free(variable_shortname n i, fastype_of t)
  in
    translate e
  end

(* Finds all (registered) variables in an expression in *instantiated* longform *)
fun variables_in_expression ctxt t =
  let val variables = Unsynchronized.ref []
      val others = Unsynchronized.ref []
      fun add x = variables := insert (op=) x (!variables)
      fun add_other x = others := insert (op=) x (!others)
      val lookup_var = lookup_variable ctxt
      (* val memT = case fastype_of t of \<^Type>\<open>fun T _\<close> => T | T => raise TYPE("expression_to_term: expression should have function type", [T], [t]) *)
      val e = (* betapply (t, Free("_memory", memT)) *) t |> Envir.beta_eta_contract
      fun collect (g as (Const(\<^const_name>\<open>getter\<close>,_) $ var $ Free("_memory", _))) = let
            val (_,n,i,T) = case decompose_singleton_variable ctxt var of
               SOME v => v
               | NONE => 
                    raise TYPE("expression_to_term: not a known variable after getter", [fastype_of var], [t,g])
            val _ = mk_cvariableT T = fastype_of var orelse  mk_c2variableT T = fastype_of var orelse
                    raise TYPE("expression_to_term: classical variable of wrong type", [T, fastype_of var], [t,g])
          in add (Classical, n, i, T) end
        | collect (Free("_memory", _)) = raise TERM("expression_to_term: encountered memory access without getter", [t,e])
        | collect t = case decompose_singleton_variable ctxt t of
            NONE => (case t of (t1 $ t2) => (collect t1; collect t2) | (Abs(_,_,body)) => collect body | Free(n,_) => add_other n | _ => ())
            | SOME (cq,n,i,_) => add (cq, n, i, fastype_of t)
     val _ = collect e
  in
    (!variables, !others)
  end

fun register_of_varinfo {qc=Classical, in_typ, out_typ, name} = Free(name, \<^Type>\<open>cregister in_typ out_typ\<close>)
  | register_of_varinfo {qc=Quantum, in_typ, out_typ, name} = Free(name, \<^Type>\<open>qregister in_typ out_typ\<close>)

fun shortname_to_register ctxt (name,T) = case lookup_variable ctxt name of
  SOME v => SOME (register_of_varinfo v, #qc v)
  | NONE => 
    let val len = String.size name
        val idx = case String.substring (name, len-1, 1) of "1" => Index1 | "2" => Index2 | _ => NoIndex
    in case idx of
      NoIndex => NONE
      | _ => case lookup_variable ctxt (String.substring (name, 0, len-1)) of
               NONE => NONE
               | SOME v => case (#qc v, idx) of
                               (Classical, Index1) => SOME (\<^Const>\<open>cregister_chain \<open>\<^typ>\<open>cl\<close>\<close> \<open>\<^typ>\<open>cl2\<close>\<close> \<open>#in_typ v\<close>\<close> $ \<^Const>\<open>cFst \<open>\<^typ>\<open>cl\<close>\<close> \<open>\<^typ>\<open>cl\<close>\<close>\<close> $ register_of_varinfo v, Classical)
                             | (Classical, Index2) => SOME (\<^Const>\<open>cregister_chain \<open>\<^typ>\<open>cl\<close>\<close> \<open>\<^typ>\<open>cl2\<close>\<close> \<open>#in_typ v\<close>\<close> $ \<^Const>\<open>cSnd \<open>\<^typ>\<open>cl\<close>\<close> \<open>\<^typ>\<open>cl\<close>\<close>\<close> $ register_of_varinfo v, Classical)
                             | (Quantum, Index1) => SOME (\<^Const>\<open>qregister_chain \<open>\<^typ>\<open>qu\<close>\<close> \<open>\<^typ>\<open>qu2\<close>\<close> \<open>#in_typ v\<close>\<close> $ \<^Const>\<open>qFst \<open>\<^typ>\<open>qu\<close>\<close> \<open>\<^typ>\<open>qu\<close>\<close>\<close> $ register_of_varinfo v, Quantum)
                             | (Quantum, Index2) => SOME (\<^Const>\<open>qregister_chain \<open>\<^typ>\<open>qu\<close>\<close> \<open>\<^typ>\<open>qu2\<close>\<close> \<open>#in_typ v\<close>\<close> $ \<^Const>\<open>qSnd \<open>\<^typ>\<open>qu\<close>\<close> \<open>\<^typ>\<open>qu\<close>\<close>\<close> $ register_of_varinfo v, Quantum)
                             | (_, NoIndex) => error "shortname_to_register: unreachable code"
    end


(* Translates expression in shortform to expression in longform *)
fun term_to_expression ctxt memT t =
  let (* val lookup_var = lookup_variable ctxt *)
      val mem_var = Free("_memory_", memT)
      (* val _ = \<^print> (Term.add_frees t [] |> map fst |> map lookup_var) *)
      val subst = Term.add_frees t [] 
        |> map_filter (fn (n,T) => case shortname_to_register ctxt (n,T) of
              SOME (reg, Classical) => 
                SOME (Free (n,T), Const(\<^const_name>\<open>getter\<close>, fastype_of reg --> memT --> (fastype_of reg |> dest_cregisterT |> fst)) $ reg $ mem_var)
            | SOME (reg, Quantum) => 
                SOME (Free (n,T), reg)
            | _ => NONE)
      (* val _ = \<^print> subst *)
      val body = abstract_over (mem_var, subst_atomic subst t)
      (* val _ = \<^print> body *)
  in
    Abs("mem", memT, body)
  end

type varterm_names = string tree

(* t \<rightarrow> \<lambda>m. (t (fst m))   if left=true *)
fun add_index_to_expression ctxt left t = let
  val fst_t = if left then @{const fst(cl,cl)} else @{const snd(cl,cl)}
  val res = Abs("memory", \<^typ>\<open>cl2\<close>, Term.betapply (t, (fst_t $ Bound 0)))
  val res = Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt)
      @{thms add_index_to_expression_aux1 add_index_to_expression_aux2} [] res
  in res end

(* (* t \<rightarrow> \<lambda>m. liftSpace (t (fst m)) qFst   if left=true *)
fun add_index_to_predicate left t = let
  val qFst = if left then @{const qFst(qu,qu)} else @{const qSnd(qu,qu)} 
  val fst_t = if left then @{const fst(cl,cl)} else @{const snd(cl,cl)}
  val res = Abs("memory", \<^typ>\<open>cl2\<close>, @{const liftSpace(qu)} $ (t $ (fst_t $ Bound 0)) $ qFst)
  (* Should do cleanup like in add_index_to_expression. *)
  in res end *)

fun generalize_getters ctxt = Subgoal.FOCUS_PARAMS (fn focus => let
  val m = focus |> #params |> hd |> snd (* We assume the memory is the outermost parameter! *)
  val pattern = Const ("Prog_Variables.getter", TVar(("'a",0),[])) $ 
                    Var (("_dummy_", 1), TVar(("'b",0),[])) $ Thm.term_of m
  fun varname (Const(\<^const_name>\<open>getter\<close>,_) $ v $ _) = varname v ^ "'"
    | varname (Free(n,_)) = n
    | varname (Const(\<^const_name>\<open>cregister_chain\<close>,_) $ Const(\<^const_name>\<open>cFst\<close>,_) $ v) = varname v^"1"
    | varname (Const(\<^const_name>\<open>cregister_chain\<close>,_) $ Const(\<^const_name>\<open>cSnd\<close>,_) $ v) = varname v^"2"
    | varname (Const(\<^const_name>\<open>cregister_chain\<close>,_) $ v1 $ v2) = varname v1 ^ varname v2
    | varname (v1 $ v2) = varname v1 ^ varname v2
    | varname (Var((n,_),_)) = n
    | varname (Bound _) = "x"
    | varname (Abs(_,_,body)) = varname body
    | varname (Const(c,_)) = c
  val tac = REPEAT_DETERM (Misc.generalize_tac (#context focus) varname pattern 1)
in tac end) ctxt
THEN'
rewrite_goal_tac ctxt @{thms triv_forall_equality} (* Removes all unused parameters. Theoretically should be limited to the toplevel ones, not any inside the term *)



end

end