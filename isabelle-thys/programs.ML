structure Programs = struct

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
fun clean_expression_conv ctxt = let
  val outer_simpset = simpset_of ctxt
  val simpset_ctxt = put_simpset clean_expression_conv_simpset ctxt
  fun prover ctxt = SINGLE (ALLGOALS (distinct_vars_tac (put_simpset outer_simpset ctxt)))
in Raw_Simplifier.rewrite_cterm (false,true,false) prover simpset_ctxt end

(* Translates expression in longform to expression in shortform *)
fun expression_to_term ctxt t =
  let val lookup_var = lookup_variable ctxt
      val body = case t of Abs(_,_,body) => body | _ => raise TERM("expression_to_term", [t])
      val e = subst_bound (Free("_memory", dummyT), body)
      fun check_qvariable n T = case lookup_var n of
          SOME {qc=Classical, ...} => raise TYPE("expression_to_term: classical variable after qregister_chain", [T], [])
        | SOME {qc=Quantum, typ, ...} => 
            mk_qvariableT typ = T orelse raise TYPE("expression_to_term: quantum variable of wrong type", [T,typ], [])
        | NONE => false
      fun translate (g as (Const(\<^const_name>\<open>getter\<close>,_) $ var $ Free("_memory", _))) = let
            val (n,T) = case find_variable ctxt var of
               SOME {qc=Classical, typ, name, ...} => (name,typ)
               | SOME {qc=Quantum, ...} => 
                    raise TYPE("expression_to_term: quantum variable after getter", [fastype_of var], [t,g])
               | NONE => 
                    raise TYPE("expression_to_term: not a known variable after getter", [fastype_of var], [t,g])
            val _ = mk_cvariableT T = fastype_of var orelse  mk_c2variableT T = fastype_of var orelse
                    raise TYPE("expression_to_term: classical variable of wrong type", [T, fastype_of var], [t,g])
          in Free(n,T) end
        | translate (q1 as (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ Const(\<^const_name>\<open>qFst\<close>,_) $ Free(n,T))) = 
          if check_qvariable n T then Free(n^"1", dest_qvariableT T |> mk_q2variableT) else q1
        | translate (q2 as (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ Const(\<^const_name>\<open>qSnd\<close>,_) $ Free(n,T))) = 
          if check_qvariable n T then Free(n^"2", dest_qvariableT T |> mk_q2variableT) else q2
        | translate (t1 $ t2) = translate t1 $ translate t2
        | translate (Abs(n,T,body)) = Abs(n, T, translate body)
        | translate (Free(n,T)) = (case lookup_var n of
            SOME {qc=Classical, ...} => raise TERM("expression_to_term: classical variable occurs without getter", [Free(n,T), t])
          | _ => Free(n,T))
        | translate t = t
  in
    translate e
  end


fun term_to_expression ctx memT t =
  let val lookup_var = lookup_variable ctx
      val mem_var = Free("_memory_", memT)
      (* val _ = \<^print> (Term.add_frees t [] |> map fst |> map lookup_var) *)
      val subst = Term.add_frees t [] 
        |> map_filter (fn (v,T) => case lookup_var v of
              SOME {qc=Classical, typ, register, ...} => 
                SOME (Free (v,T), Const(\<^const_name>\<open>getter\<close>, fastype_of register --> memT --> typ) $ register $ mem_var)
            | SOME {qc=Quantum, typ, register, ...} => 
                SOME (Free (v,T), register)
            | _ => NONE)
      (* val _ = \<^print> subst *)
      val body = abstract_over (mem_var, subst_atomic subst t)
      (* val _ = \<^print> body *)
  in
    Abs("mem", memT, body)
  end

datatype call = CALL of string * call list

type varterm_names = string tree

datatype statement = 
  Block of statement list
| Local of varterm(*cvars*) * varterm(*qvars*) * statement list
| Assign of varterm * term
| Sample of varterm * term
| Call of call
| Measurement of varterm * varterm * term
| QInit of varterm * term
| QApply of varterm * term
| IfThenElse of term * statement list * statement list
| While of term * statement list

(* fun the_block (Block stmts) = stmts
  | the_block _ = error "the_block" *)

fun call_to_term (CALL (name,[])) = Free(name,\<^typ>\<open>program\<close>)
  | call_to_term (CALL (name,args)) = 
      \<^const>\<open>instantiateOracles\<close> $ Free(name,\<^typ>\<open>oracle_program\<close>) $ HOLogic.mk_list \<^typ>\<open>program\<close> (map call_to_term args)

fun term_to_call (Free(name,_)) = CALL (name,[])
  | term_to_call (Const(\<^const_name>\<open>instantiateOracles\<close>,_) $ Free(name,_) $ args) = let
      val args' = args |> HOLogic.dest_list |> map term_to_call
      in CALL (name,args') end
  | term_to_call t = raise TERM ("term_to_call",[t])

fun statement_to_term ctxt (Assign(lhs,rhs)) = let 
      val T = fastype_of rhs
      val lhs' : term = lhs |> varterm_to_variable Classical
      in Const(\<^const_name>\<open>assign\<close>, mk_cvariableT T --> mk_expressionT T --> \<^typ>\<open>program\<close>) $ 
         lhs' $ term_to_expression ctxt \<^typ>\<open>cl\<close> rhs end
  | statement_to_term ctxt (Sample(lhs,rhs)) = let 
      val T = fastype_of rhs
      val lhsT = Discrete_Distributions.dest_distrT T
      val lhs' : term = lhs |> varterm_to_variable Classical
      in Const(\<^const_name>\<open>sample\<close>, mk_cvariableT lhsT --> mk_expressionT T --> \<^typ>\<open>program\<close>) $ 
         lhs' $ term_to_expression ctxt \<^typ>\<open>cl\<close> rhs end
  | statement_to_term ctxt (Block stmts) = \<^const>\<open>block\<close> $ statements_to_term ctxt stmts
  | statement_to_term ctxt (Local (cvars,qvars,stmts)) = let
      val cvars' = varterm_to_variable Classical cvars
      val qvars' = varterm_to_variable Quantum qvars
      in Const(\<^const_name>\<open>localvars\<close>, fastype_of cvars' --> fastype_of qvars' --> \<^typ>\<open>program list \<Rightarrow> program\<close>) 
          $ cvars' $ qvars' $ statements_to_term ctxt stmts
      end
  | statement_to_term _ (Call call) = call_to_term call
  | statement_to_term ctxt (IfThenElse (e, p1, p2)) =
    \<^const>\<open>ifthenelse\<close> $ term_to_expression ctxt \<^typ>\<open>cl\<close> e $ statements_to_term ctxt p1 $ statements_to_term ctxt p2
  | statement_to_term ctxt (While (e, p)) =
    \<^const>\<open>while\<close> $ term_to_expression ctxt \<^typ>\<open>cl\<close> e $ statements_to_term ctxt p
  | statement_to_term ctxt (Measurement (lhs,loc,e)) = let
    val T = fastype_of e
    val (vT,locT) = QRHL.dest_measurementT T
    val lhs' : term = varterm_to_variable Classical lhs
    val loc' : term = varterm_to_variable Quantum loc
    in Const(\<^const_name>\<open>measurement\<close>, mk_cvariableT vT --> mk_qvariableT locT --> mk_expressionT T --> \<^typ>\<open>program\<close>) $
         lhs' $ loc' $ term_to_expression ctxt \<^typ>\<open>cl\<close> e end
  | statement_to_term ctxt (QApply (loc,e)) = let
    val T = fastype_of e
    val locT = dest_bounded2T T
    (* val _ = if locT = locT' then () else raise TYPE("statement_to_term QApply locT<>locT'",[T],[e]) *)
    val loc' : term = varterm_to_variable Quantum loc
    in Const(\<^const_name>\<open>qapply\<close>, mk_qvariableT locT --> mk_expressionT T --> \<^typ>\<open>program\<close>) $
         loc' $ term_to_expression ctxt \<^typ>\<open>cl\<close> e end
  | statement_to_term ctxt (QInit (loc,e)) = let
    val T = fastype_of e
    val locT = dest_ell2T T
    val loc' : term = varterm_to_variable Quantum loc
    in Const(\<^const_name>\<open>qinit\<close>, mk_qvariableT locT --> mk_expressionT T --> \<^typ>\<open>program\<close>) $
         loc' $ term_to_expression ctxt \<^typ>\<open>cl\<close> e end

and statements_to_term ctxt statements = map (statement_to_term ctxt) statements |> HOLogic.mk_list \<^typ>\<open>program\<close>

fun term_to_statement ctxt (Const(\<^const_name>\<open>block\<close>,_) $ statements) = Block (term_to_statements ctxt statements)
  | term_to_statement ctxt (Const(\<^const_name>\<open>localvars\<close>, _) $ cvars $ qvars $ body) =
      Local (variable_to_varterm ctxt cvars, variable_to_varterm ctxt qvars, term_to_statements ctxt body)
  | term_to_statement ctxt (Const(\<^const_name>\<open>assign\<close>,_) $ x $ e) = 
      Assign (variable_to_varterm ctxt x, expression_to_term ctxt e)
  | term_to_statement ctxt (Const(\<^const_name>\<open>sample\<close>,_) $ x $ e) = 
      Sample (variable_to_varterm ctxt x, expression_to_term ctxt e)
  | term_to_statement ctxt (Const(\<^const_name>\<open>while\<close>,_) $ e $ body) =
      While (expression_to_term ctxt e, term_to_statements ctxt body)
  | term_to_statement ctxt (Const(\<^const_name>\<open>ifthenelse\<close>,_) $ e $ p1 $ p2) =
      IfThenElse (expression_to_term ctxt e, term_to_statements ctxt p1, term_to_statements ctxt p2)
  | term_to_statement ctxt (Const(\<^const_name>\<open>qinit\<close>,_) $ vs $ e) =
      QInit (variable_to_varterm ctxt vs, expression_to_term ctxt e)
  | term_to_statement ctxt (Const(\<^const_name>\<open>qapply\<close>,_) $ vs $ e) =
      QApply (variable_to_varterm ctxt vs, expression_to_term ctxt e)
  | term_to_statement ctxt (Const(\<^const_name>\<open>measurement\<close>,_) $ x $ vs $ e) =
      Measurement (variable_to_varterm ctxt x, 
                   variable_to_varterm ctxt vs, expression_to_term ctxt e)
  | term_to_statement _ (t as Free _) = Call (term_to_call t)
  | term_to_statement _ (t as Const(\<^const_name>\<open>instantiateOracles\<close>,_) $ _ $ _) = Call (term_to_call t)
  | term_to_statement _ t = raise TERM("term_to_statement",[t])

and term_to_statements ctxt t = HOLogic.dest_list t |> map (term_to_statement ctxt)

fun free_vars_tac ctxt = let
  val fact = Proof_Context.get_fact ctxt (Facts.named \<^named_theorems>\<open>program_fv\<close>)
  in
    Misc.succeed_or_error_tac' (resolve_tac ctxt @{thms Cccompatible_antimono_left Qqcompatible_antimono_left}) ctxt
      (fn t => "free_vars_tac: Expected 'Qq/Cccompatible ... ...', got: "^Syntax.string_of_term ctxt t)
  THEN'
    Misc.succeed_or_error_tac' (resolve_tac ctxt fact) ctxt
      (fn t => "Could not determine free variables of adversary. Problematic subgoal: "^Syntax.string_of_term ctxt t)
  THEN'
    distinct_vars_tac ctxt
  end

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

end
end
