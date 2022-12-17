structure Programs = struct

local open Prog_Variables open Expressions in


datatype call = CALL of string * call list

datatype statement = 
  Block of statement list
| Local of varterm1(*cvars*) * varterm1(*qvars*) * statement list
| Assign of varterm1 * term
| Sample of varterm1 * term
| Call of call
| Measurement of varterm1 * varterm1 * term
| QInit of varterm1 * term
| QApply of varterm1 * term
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
      val rhsT = fastype_of rhs
      val T = range_type rhsT
      val lhs' : term = lhs |> varterm1_to_variable1 Classical
      in Const(\<^const_name>\<open>assign\<close>, mk_cvariableT T --> rhsT --> \<^typ>\<open>program\<close>) $ 
         lhs' $ rhs end
  | statement_to_term ctxt (Sample(lhs,rhs)) = let 
      val rhsT = fastype_of rhs
      val T = range_type rhsT
      val lhsT = Discrete_Distributions.dest_distrT T
      val lhs' : term = lhs |> varterm1_to_variable1 Classical
      in Const(\<^const_name>\<open>sample\<close>, mk_cvariableT lhsT --> rhsT --> \<^typ>\<open>program\<close>) $ 
         lhs' $ rhs end
  | statement_to_term ctxt (Block stmts) = \<^const>\<open>block\<close> $ statements_to_term ctxt stmts
  | statement_to_term ctxt (Local (cvars,qvars,stmts)) = let
      val cvars' = varterm1_to_variable1 Classical cvars
      val qvars' = varterm1_to_variable1 Quantum qvars
      in Const(\<^const_name>\<open>localvars\<close>, fastype_of cvars' --> fastype_of qvars' --> \<^typ>\<open>program list \<Rightarrow> program\<close>) 
          $ cvars' $ qvars' $ statements_to_term ctxt stmts
      end
  | statement_to_term _ (Call call) = call_to_term call
  | statement_to_term ctxt (IfThenElse (e, p1, p2)) =
    \<^const>\<open>ifthenelse\<close> $ e $ statements_to_term ctxt p1 $ statements_to_term ctxt p2
  | statement_to_term ctxt (While (e, p)) =
    \<^const>\<open>while\<close> $ e $ statements_to_term ctxt p
  | statement_to_term ctxt (Measurement (lhs,loc,e)) = let
    val eT = fastype_of e
    val T = range_type eT
    val (vT,locT) = QRHL.dest_measurementT T
    val lhs' : term = varterm1_to_variable1 Classical lhs
    val loc' : term = varterm1_to_variable1 Quantum loc
    in Const(\<^const_name>\<open>measurement\<close>, mk_cvariableT vT --> mk_qvariableT locT --> eT --> \<^typ>\<open>program\<close>) $
         lhs' $ loc' $ e end
  | statement_to_term ctxt (QApply (loc,e)) = let
    val eT = fastype_of e
    val T = range_type eT
    val locT = dest_bounded2T T
    (* val _ = if locT = locT' then () else raise TYPE("statement_to_term QApply locT<>locT'",[T],[e]) *)
    val loc' : term = varterm1_to_variable1 Quantum loc
    in Const(\<^const_name>\<open>qapply\<close>, mk_qvariableT locT --> eT --> \<^typ>\<open>program\<close>) $
         loc' $ e end
  | statement_to_term ctxt (QInit (loc,e)) = let
    val eT = fastype_of e
    val T = range_type eT
    val locT = dest_ell2T T
    val loc' : term = varterm1_to_variable1 Quantum loc
    in Const(\<^const_name>\<open>qinit\<close>, mk_qvariableT locT --> eT --> \<^typ>\<open>program\<close>) $
         loc' $ e end

and statements_to_term ctxt statements = map (statement_to_term ctxt) statements |> HOLogic.mk_list \<^typ>\<open>program\<close>

fun term_to_statement ctxt (Const(\<^const_name>\<open>block\<close>,_) $ statements) = Block (term_to_statements ctxt statements)
  | term_to_statement ctxt (Const(\<^const_name>\<open>localvars\<close>, _) $ cvars $ qvars $ body) =
      Local (variable_to_varterm1 ctxt cvars, variable_to_varterm1 ctxt qvars, term_to_statements ctxt body)
  | term_to_statement ctxt (Const(\<^const_name>\<open>assign\<close>,_) $ x $ e) = 
      Assign (variable_to_varterm1 ctxt x, e)
  | term_to_statement ctxt (Const(\<^const_name>\<open>sample\<close>,_) $ x $ e) = 
      Sample (variable_to_varterm1 ctxt x, e)
  | term_to_statement ctxt (Const(\<^const_name>\<open>while\<close>,_) $ e $ body) =
      While (e, term_to_statements ctxt body)
  | term_to_statement ctxt (Const(\<^const_name>\<open>ifthenelse\<close>,_) $ e $ p1 $ p2) =
      IfThenElse (e, term_to_statements ctxt p1, term_to_statements ctxt p2)
  | term_to_statement ctxt (Const(\<^const_name>\<open>qinit\<close>,_) $ vs $ e) =
      QInit (variable_to_varterm1 ctxt vs, e)
  | term_to_statement ctxt (Const(\<^const_name>\<open>qapply\<close>,_) $ vs $ e) =
      QApply (variable_to_varterm1 ctxt vs, e)
  | term_to_statement ctxt (Const(\<^const_name>\<open>measurement\<close>,_) $ x $ vs $ e) =
      Measurement (variable_to_varterm1 ctxt x, 
                   variable_to_varterm1 ctxt vs, e)
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

end
end
