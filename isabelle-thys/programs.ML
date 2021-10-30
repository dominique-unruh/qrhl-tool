structure Programs = struct

datatype call = CALL of string * call list

type varterm_names = string Prog_Variables.tree

datatype statement = 
  Block of statement list
| Local of Prog_Variables.varterm(*cvars*) * Prog_Variables.varterm(*qvars*) * statement list
| Assign of Prog_Variables.varterm * term
| Sample of Prog_Variables.varterm * term
| Call of call
| Measurement of Prog_Variables.varterm * Prog_Variables.varterm * term
| QInit of Prog_Variables.varterm * term
| QApply of Prog_Variables.varterm * term
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

(* local open Expressions open Prog_Variables in *)

fun statement_to_term ctxt (Assign(lhs,rhs)) = let 
      val T = fastype_of rhs
      val lhs' : term = lhs |> map_tree (apfst (fn v => "var_"^v)) |> mk_varterm |> fst
      in Const(\<^const_name>\<open>assign\<close>, mk_variablesT T --> mk_expressionT T --> \<^typ>\<open>program\<close>) $ 
         lhs' $ term_to_expression ctxt rhs end
  | statement_to_term ctxt (Sample(lhs,rhs)) = let 
      val T = fastype_of rhs
      val lhsT = Discrete_Distributions.dest_distrT T
      val lhs' : term = lhs |> map_tree (apfst (fn v => "var_"^v)) |> mk_varterm |> fst
      in Const(\<^const_name>\<open>sample\<close>, mk_variablesT lhsT --> mk_expressionT T --> \<^typ>\<open>program\<close>) $ 
         lhs' $ term_to_expression ctxt rhs end
  | statement_to_term ctxt (Block stmts) = \<^const>\<open>block\<close> $ statements_to_term ctxt stmts
  | statement_to_term ctxt (Local (cvars,qvars,stmts)) = let
      val (cvars',cT) = cvars |> map_tree (fn (v,T) => ("var_"^v,T)) |> mk_varterm
      val (qvars',qT) = mk_varterm qvars
      in Const(\<^const_name>\<open>localvars\<close>, mk_variablesT cT --> mk_variablesT qT --> \<^typ>\<open>program list \<Rightarrow> program\<close>) 
          $ cvars' $ qvars' $ statements_to_term ctxt stmts
      end
  | statement_to_term _ (Call call) = call_to_term call
  | statement_to_term ctxt (IfThenElse (e, p1, p2)) =
    \<^const>\<open>ifthenelse\<close> $ term_to_expression ctxt e $ statements_to_term ctxt p1 $ statements_to_term ctxt p2
  | statement_to_term ctxt (While (e, p)) =
    \<^const>\<open>while\<close> $ term_to_expression ctxt e $ statements_to_term ctxt p
  | statement_to_term ctxt (Measurement (lhs,loc,e)) = let
    val T = fastype_of e
    val (vT,locT) = QRHL.dest_measurementT T
    val lhs' : term = lhs |> map_tree (apfst (fn v => "var_"^v)) |> mk_varterm |> fst
    val loc' : term = loc |> mk_varterm |> fst
    in Const(\<^const_name>\<open>measurement\<close>, mk_variablesT vT --> mk_variablesT locT --> mk_expressionT T --> \<^typ>\<open>program\<close>) $
         lhs' $ loc' $ term_to_expression ctxt e end
  | statement_to_term ctxt (QApply (loc,e)) = let
    val T = fastype_of e
    val (locT,locT') = QRHL.dest_boundedT T
    val _ = if locT = locT' then () else raise TYPE("statement_to_term QApply locT<>locT'",[T],[e])
    val loc' : term = loc |> mk_varterm |> fst
    in Const(\<^const_name>\<open>qapply\<close>, mk_variablesT locT --> mk_expressionT T --> \<^typ>\<open>program\<close>) $
         loc' $ term_to_expression ctxt e end
  | statement_to_term ctxt (QInit (loc,e)) = let
    val T = fastype_of e
    val locT = QRHL.dest_ell2T T
    val loc' : term = loc |> mk_varterm |> fst
    in Const(\<^const_name>\<open>qinit\<close>, mk_variablesT locT --> mk_expressionT T --> \<^typ>\<open>program\<close>) $
         loc' $ term_to_expression ctxt e end

and statements_to_term ctxt statements = map (statement_to_term ctxt) statements |> HOLogic.mk_list \<^typ>\<open>program\<close>

fun term_to_statement ctxt (Const(\<^const_name>\<open>block\<close>,_) $ statements) = Block (term_to_statements ctxt statements)
  | term_to_statement ctxt (Const(\<^const_name>\<open>localvars\<close>, _) $ cvars $ qvars $ body) =
      Local (parse_varterm cvars |> map_tree (apfst strip_var_prefix), parse_varterm qvars, term_to_statements ctxt body)
  | term_to_statement ctxt (Const(\<^const_name>\<open>assign\<close>,_) $ x $ e) = 
      Assign (parse_varterm x |> map_tree (apfst strip_var_prefix), expression_to_term ctxt e)
  | term_to_statement ctxt (Const(\<^const_name>\<open>sample\<close>,_) $ x $ e) = 
      Sample (parse_varterm x |> map_tree (apfst strip_var_prefix), expression_to_term ctxt e)
  | term_to_statement ctxt (Const(\<^const_name>\<open>while\<close>,_) $ e $ body) =
      While (expression_to_term ctxt e, term_to_statements ctxt body)
  | term_to_statement ctxt (Const(\<^const_name>\<open>ifthenelse\<close>,_) $ e $ p1 $ p2) =
      IfThenElse (expression_to_term ctxt e, term_to_statements ctxt p1, term_to_statements ctxt p2)
  | term_to_statement ctxt (Const(\<^const_name>\<open>qinit\<close>,_) $ vs $ e) =
      QInit (parse_varterm vs, expression_to_term ctxt e)
  | term_to_statement ctxt (Const(\<^const_name>\<open>qapply\<close>,_) $ vs $ e) =
      QApply (parse_varterm vs, expression_to_term ctxt e)
  | term_to_statement ctxt (Const(\<^const_name>\<open>measurement\<close>,_) $ x $ vs $ e) =
      Measurement (parse_varterm x |> map_tree (apfst strip_var_prefix), 
                   parse_varterm vs, expression_to_term ctxt e)
  | term_to_statement _ (t as Free _) = Call (term_to_call t)
  | term_to_statement _ (t as Const(\<^const_name>\<open>instantiateOracles\<close>,_) $ _ $ _) = Call (term_to_call t)
  | term_to_statement _ t = raise TERM("term_to_statement",[t])

(*
    case Free(name,_) => Call(name)
    case App(App(Const(Isabelle.instantiateOracles.name,_), Free(name,_)), args) =>
      val args2 = Isabelle.dest_list(args).map(decodeFromTerm(context,_).asInstanceOf[Call])
      Call(name,args2 : _* )
*)

and term_to_statements ctxt t = HOLogic.dest_list t |> map (term_to_statement ctxt)

(* end *)

end
