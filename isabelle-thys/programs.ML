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

local open Expressions open Prog_Variables in
fun statement_to_term ctxt (Assign(lhs,rhs)) = let 
      val T = fastype_of rhs
      in Const(\<^const_name>\<open>assign\<close>, mk_variableT T --> mk_expressionT T --> \<^typ>\<open>program\<close>) $ 
         Free("var_"^lhs, mk_variableT T) $ expression_to_term ctxt rhs end
  | statement_to_term _ _ = error ("statement_to_term: nyi")
end
end
