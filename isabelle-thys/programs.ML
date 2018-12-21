structure Programs = struct

datatype call = CALL of string * call list

datatype statement = 
  Block of statement list
| Assign of string * term
| Sample of string * term
| Call of call
| Measurement of string * string list * term
| QInit of string list * term
| QApply of string list * term
| IfThenElse of term * statement list * statement list
| While of term * statement list

(* fun the_block (Block stmts) = stmts
  | the_block _ = error "the_block" *)

fun call_to_term (CALL (name,[])) = Free(name,\<^typ>\<open>program\<close>)
  | call_to_term (CALL (name,args)) = 
      \<^const>\<open>instantiateOracles\<close> $ Free(name,\<^typ>\<open>oracle_program\<close>) $ HOLogic.mk_list \<^typ>\<open>program\<close> (map call_to_term args)


local open Expressions open Prog_Variables in
(* TODO move *)
fun varterm_instantiate \<^typ>\<open>unit\<close> VTUnit = VTUnit
  | varterm_instantiate T VTUnit = raise TYPE ("varterm_instantiate: invalid type for VTUnit",[T],[])
  | varterm_instantiate (Type(\<^type_name>\<open>prod\<close>,[T1,T2])) (VTCons (v1,v2)) = VTCons (varterm_instantiate T1 v1, varterm_instantiate T2 v2)
  | varterm_instantiate T (VTCons _) = raise TYPE ("varterm_instantiate: invalid type for VTCons",[T],[])
  | varterm_instantiate T (VTSingle (v,_)) = VTSingle (v,T)

fun statement_to_term ctxt (Assign(lhs,rhs)) = let 
      val T = fastype_of rhs
      in Const(\<^const_name>\<open>assign\<close>, mk_variableT T --> mk_expressionT T --> \<^typ>\<open>program\<close>) $ 
         Free("var_"^lhs, mk_variableT T) $ term_to_expression ctxt rhs end
  | statement_to_term ctxt (Sample(lhs,rhs)) = let 
      val T = fastype_of rhs
      val lhsT = Discrete_Distributions.dest_distrT T |> mk_variableT
      in Const(\<^const_name>\<open>sample\<close>, lhsT --> mk_expressionT T --> \<^typ>\<open>program\<close>) $ 
         Free("var_"^lhs, lhsT) $ term_to_expression ctxt rhs end
  | statement_to_term ctxt (Block stmts) = \<^const>\<open>block\<close> $ statements_to_term ctxt stmts
  | statement_to_term _ (Call call) = call_to_term call
  | statement_to_term ctxt (IfThenElse (e, p1, p2)) =
    \<^const>\<open>ifthenelse\<close> $ term_to_expression ctxt e $ statements_to_term ctxt p1 $ statements_to_term ctxt p2
  | statement_to_term ctxt (While (e, p)) =
    \<^const>\<open>while\<close> $ term_to_expression ctxt e $ statements_to_term ctxt p
  | statement_to_term ctxt (Measurement (lhs,loc,e)) = let
    val T = fastype_of e
    val (vT,locT) = QRHL.dest_measurementT T
    val loc' : term = loc |> varterm_from_list_untyped |> varterm_instantiate locT |> mk_varterm |> fst
    in Const(\<^const_name>\<open>measurement\<close>, mk_variableT vT --> mk_variablesT locT --> mk_expressionT T --> \<^typ>\<open>program\<close>) $
         Free("var_"^lhs, mk_variableT vT) $ loc' $ term_to_expression ctxt e end
  | statement_to_term ctxt (QApply (loc,e)) = let
    val T = fastype_of e
    val (locT,locT') = QRHL.dest_boundedT T
    val _ = if locT = locT' then () else raise TYPE("statement_to_term QApply locT<>locT'",[T],[e])
    val loc' : term = loc |> varterm_from_list_untyped |> varterm_instantiate locT |> mk_varterm |> fst
    in Const(\<^const_name>\<open>qapply\<close>, mk_variablesT locT --> mk_expressionT T --> \<^typ>\<open>program\<close>) $
         loc' $ term_to_expression ctxt e end
  | statement_to_term ctxt (QInit (loc,e)) = let
    val T = fastype_of e
    val locT = QRHL.dest_vectorT T
    val loc' : term = loc |> varterm_from_list_untyped |> varterm_instantiate locT |> mk_varterm |> fst
    in Const(\<^const_name>\<open>qinit\<close>, mk_variablesT locT --> mk_expressionT T --> \<^typ>\<open>program\<close>) $
         loc' $ term_to_expression ctxt e end

and statements_to_term ctxt statements = map (statement_to_term ctxt) statements |> HOLogic.mk_list \<^typ>\<open>program\<close>
end

end
