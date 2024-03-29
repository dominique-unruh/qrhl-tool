structure Expressions = struct

fun mk_expressionT T = Type(\<^type_name>\<open>expression\<close>, [T])

(* Rewrites all index_{flip_var,var,vars,expression,flip_expression} subterms (e.g., index_var True x \<rightarrow> x1, etc.).
   If the involved variables, variable lists, and expressions are all explicit, this will
   remove all occurrences of index_{...}.
*)
fun index_conv ctxt =
  Raw_Simplifier.rewrite ctxt false @{thms 
        index_expression[THEN eq_reflection]
        index_flip_expression[THEN eq_reflection]
        index_vars_concat[THEN eq_reflection]
        index_vars_singleton[THEN eq_reflection]
        index_vars_unit[THEN eq_reflection]
        index_flip_vars_concat[THEN eq_reflection]
        index_flip_vars_singleton[THEN eq_reflection]
        index_flip_vars_unit[THEN eq_reflection]
}
then_conv
  Conv.top_sweep_conv Prog_Variables.index_var_conv ctxt
then_conv
  Conv.top_sweep_conv Prog_Variables.index_flip_var_conv ctxt

val index_tac = Misc.schematic_conv_tac "valid indexing expression" index_conv

(* TODO move *)
fun map_varterm_tuple _ (Prog_Variables.VTUnit) = \<^term>\<open>()\<close>
  | map_varterm_tuple f (Prog_Variables.VTSingle nT) = f nT
  | map_varterm_tuple f (Prog_Variables.VTCons (a,b)) = HOLogic.mk_prod (map_varterm_tuple f a, map_varterm_tuple f b)


(* TODO: should make sure it's sound (i.e., reject expressions that cannot be converted, check whether vars are declared *)
fun expression_to_term ctxt t =
  let val (vs,e) = case t of Const(\<^const_name>\<open>expression\<close>,_) $ vs $ e => (vs,e) | _ => raise (TERM("expression_to_term",[t]))
(*      val vars = Prog_Variables.parse_varlist vs 
          |> map (fn (x,T) => Free (String.extract (x,4,NONE),T)) *) (* unsafe, not checking whether the var name is wellformed *)
      val vT = Prog_Variables.parse_varterm vs
      val arg = map_varterm_tuple (fn (x,T) => Free (Prog_Variables.strip_var_prefix x,T)) vT
      val e' = e $ arg
      val e'' = Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) @{thms case_prod_conv[THEN eq_reflection]} [] e'
  in
    e''
  end

fun case_prod_conv_syntax (Const(\<^const_syntax>\<open>prod.case_prod\<close>, _) $ f $ (Const(\<^const_syntax>\<open>Pair\<close>,_) $ a $ b)) =
            case_prod_conv_syntax (betapplys (f, [a, b]))
  | case_prod_conv_syntax (Const(\<^const_syntax>\<open>prod.case_prod\<close>, _) $ f $ (Const(\<^const_name>\<open>Pair\<close>,_) $ a $ b)) =
            case_prod_conv_syntax (betapplys (f, [a, b]))
  | case_prod_conv_syntax (Abs(_,_, body) $ t) = subst_bound (t, body)
  | case_prod_conv_syntax t = t

fun expression_to_term_syntax t =
  let val (vs,e) = case t of Const(\<^const_name>\<open>expression\<close>,_) $ vs $ e => (vs,e) | _ => raise (TERM("expression_to_term",[t]))
      val vT = Prog_Variables.parse_varterm_syntax vs
      val arg = map_varterm_tuple (fn (x,T) => Free (Prog_Variables.strip_var_prefix x,T)) vT
      val e' = e $ arg
      val e'' = case_prod_conv_syntax e'
  in
    e''
  end


fun expression_to_term_typ ctxt t =
  let val t2 = expression_to_term ctxt t in (t2, fastype_of t2) end

fun add_index_to_expression t left =
  let val suffix = if left then "1" else "2"
      fun rename (Free(x,T)) =  Free(x^suffix,T)
        | rename t = t
      val (vs,e,T) = case t of Const(\<^const_name>\<open>expression\<close>,T) $ vs $ e => (vs,e,T) | _ => 
            raise (TERM("add_index_to_expression",[t]))
      val vs = Term.map_aterms rename vs
  in
    Const(\<^const_name>\<open>expression\<close>,T) $ vs $ e
  end
  

fun lambda_name_untyped (x, v) t =
  Abs (if x = "" then Term.term_name v else x, dummyT, abstract_over (v, t));

fun lambda_untyped v t = lambda_name_untyped ("", v) t;

fun mk_case_prod_untyped t =
      @{const Product_Type.prod.case_prod(dummy,dummy,dummy)} $ t

fun tupled_lambda_untyped (x as Free _) b = lambda_untyped x b
  | tupled_lambda_untyped (x as Var _) b = lambda_untyped x b
  | tupled_lambda_untyped (Const ("Product_Type.Pair", _) $ u $ v) b =
      mk_case_prod_untyped (tupled_lambda_untyped u (tupled_lambda_untyped v b))
  | tupled_lambda_untyped (Const ("Product_Type.Unity", _)) b =
      Abs ("x", HOLogic.unitT, b)
  | tupled_lambda_untyped t _ = raise TERM ("tupled_lambda_untyped: bad tuple", [t]);

  
fun mk_prod_untyped (t1, t2) = @{const Pair(dummy,dummy)} $ t1 $ t2

fun mk_tuple_untyped [] = HOLogic.unit
  | mk_tuple_untyped ts = foldr1 mk_prod_untyped ts;

fun term_to_expression ctxt t =
  let val is_classical = Prog_Variables.is_classical_variable ctxt
      val frees = Term.add_frees t [] |> filter (fn (v,_) => is_classical v) |> rev
(*       val _ = app (fn (v,T) => if Prog_Variables.lookup_variable_type ctxt v = T then () 
            else raise TYPE("term_to_expression: "^v^" has wrong type",[T,Prog_Variables.lookup_variable_type ctxt v],[])) *)
      val (vars,varsT) = 
        frees |> map (fn (v,T) => ("var_"^v,T)) |> Prog_Variables.varterm_from_list |> Prog_Variables.mk_varterm
      val pattern = HOLogic.mk_tuple (map Free frees)
      val e = HOLogic.tupled_lambda pattern t
      val T = fastype_of t
  in
    Const(\<^const_name>\<open>expression\<close>, Prog_Variables.mk_variablesT varsT --> (varsT --> T) --> mk_expressionT T)
      $ vars $ e
  end

fun term_to_expression_untyped ctx t =
  let val lookup_var = Prog_Variables.lookup_variable_type ctx
      val frees = Term.add_frees t [] |> filter (fn (v,_) => lookup_var v = SOME Prog_Variables.Classical) |> rev
      val (vars,varsT) = 
        frees |> map (fn (v,T) => ("var_"^v,T)) |> Prog_Variables.varterm_from_list |> Prog_Variables.mk_varterm
      val pattern = mk_tuple_untyped (map Free frees)
      val e = tupled_lambda_untyped pattern t
  in
    Const(\<^const_name>\<open>expression\<close>, Prog_Variables.mk_variablesT varsT --> (varsT --> dummyT) --> \<^typ>\<open>dummy expression\<close>)
      $ vars $ e
  end

fun read_expression ctx str =
  let val t = Syntax.read_term ctx str
  in term_to_expression ctx t end


(* Translates "expression Q e" (where Q is an explicit variable list) into "expression Q (%(x\<^sub>1,...). e (x\<^sub>1,...)"
   with one x\<^sub>i for each variable in Q. The result is a well-formed explicit expression *)
fun clean_expression_abs_pat_conv ctxt ct = let
  val Q = case Thm.term_of ct of
    Const(\<^const_name>\<open>expression\<close>,_) $ Q $ _ => Q
    | _ => raise CTERM("clean_expression_abs_pat_conv",[ct])
  val varlist = Prog_Variables.parse_varlist Q
  in
    (Conv.arg_conv (Misc.pat_lambda_conv ctxt varlist)) ct
  end


(* Helper for clean_expression_conv_varlist *)
fun clean_expression_conv_varlist_tac1 ctxt =
  resolve_tac ctxt @{thms expression_clean_assoc_aux expression_clean_singleton_aux 
                          expression_clean_cons_unit_aux expression_clean_unit_cons_aux
                          expression_clean_var_cons_aux expression_clean_unit_aux} 1
  ORELSE
  CHANGED (resolve_tac ctxt @{thms expression_id_comp_aux} 1)

(* Helper for clean_expression_conv_varlist *)
fun clean_expression_conv_varlist_tac ctxt = REPEAT_DETERM (clean_expression_conv_varlist_tac1 ctxt)

(* Helper for clean_expression_conv_varlist *)
val clean_expression_conv_varlist1 : Proof.context -> conv = Misc.conv_from_tac (fn _=>fn _=>()) clean_expression_conv_varlist_tac

(* Converts an explicit expression into an expression "expression Q e" where Q is an explicit variable list. *)
fun clean_expression_conv_varlist ctxt : conv = Misc.repeat_until_conv 
  (fn prev => fn current => 
      case Thm.term_of current of Const(\<^const_name>\<open>expression\<close>,_) $ Q $ _ => 
        (Prog_Variables.is_varlist Q orelse 
            case Option.map Thm.term_of prev of SOME (Const(\<^const_name>\<open>expression\<close>,_) $ Q' $ _) => Q aconv Q'
                                              | SOME t => raise (TERM("clean_expression_conv_varlist: malformed prev",[t]))
                                              | NONE => false)
       | _ => raise CTERM("clean_expression_conv_varlist: expected expression",[current]))
  (clean_expression_conv_varlist1 ctxt)

(* Converts a well-formed explicit expression into a well-formed explicit expression, 
   simplifying subterms "case (x,y) of (x,y) => ...". (clean_expression_conv_varlist introduces such subterms.) *)
fun clean_expression_conv_case_prod ctxt : conv = Raw_Simplifier.rewrite ctxt false
  @{thms case_prod_conv[THEN eq_reflection]}

(* Converts an explicit expression into a well-formed explicit expression *)
fun clean_expression_conv ctxt = 
  clean_expression_conv_varlist ctxt then_conv 
  clean_expression_abs_pat_conv ctxt then_conv
  clean_expression_conv_case_prod ctxt

(* Rewrites "map_expression{2,3,2',3',',} ..." where the arguments have to be explicit expressions *)
val map_expression_conv = 
  Conv.rewrs_conv @{thms 
    map_expression[THEN eq_reflection]
    map_expression'[THEN eq_reflection]
    map_expression2'[THEN eq_reflection]
    map_expression2[THEN eq_reflection]
    map_expression3[THEN eq_reflection]
    map_expression3'[THEN eq_reflection]
    map_expression3''[THEN eq_reflection]
    map_expression4'[THEN eq_reflection]}

val map_expression_tac = Misc.schematic_conv_tac "map_expression term" (K map_expression_conv)

(* Subgoals of the form ?x = substitute_vars Q e
   where Q is an explicit varterm and e an explicit expression.
   x will be assigned a list of substitute1's *)
fun substitute_vars_tac ctxt = SUBGOAL (fn (t,i) => 
  case Logic.strip_assums_concl t |> HOLogic.dest_Trueprop of 
    (Const(\<^const_name>\<open>HOL.eq\<close>,_) $ _ $ (Const(\<^const_name>\<open>substitute_vars\<close>,_) $ Q $ 
      (Const(\<^const_name>\<open>expression\<close>,_) $ vars $ e))) =>
    (case Q of
      Const(\<^const_name>\<open>variable_unit\<close>,_) =>
        resolve_tac ctxt @{thms substitute_vars_unit_tac} i
      | Const(\<^const_name>\<open>variable_singleton\<close>,_) $ _ =>
        resolve_tac ctxt @{thms substitute_vars_singleton_tac} i
      | Const(\<^const_name>\<open>variable_concat\<close>,_) $ _ $ _ =>
        resolve_tac ctxt @{thms substitute_vars_concat_tac} i
        THEN map_expression_tac ctxt i
        THEN map_expression_tac ctxt i
        THEN substitute_vars_tac ctxt i
        THEN substitute_vars_tac ctxt i
        THEN Misc.append_list_tac ctxt i
      | _ => raise TERM("substitute_vars_tac: nyi",[t]))
  | _ => raise TERM("substitute_vars_tac: bad shape",[t]))

(* Subgoals of the form ?x (or: expression ?Q ?e) = subst_expression s e
   where s is an explicit substitution1 list and e is an explicit expression *)
fun subst_expression_list_tac ctxt = 
  (* print_tac_n ctxt "subst_expression_tac" THEN' *)
  SUBGOAL (fn (t,i) =>
  case Logic.strip_assums_concl t |> HOLogic.dest_Trueprop of 
        (Const(\<^const_name>\<open>HOL.eq\<close>,_) $ _ $ (Const(\<^const_name>\<open>subst_expression\<close>,_) $ s $ 
          (Const(\<^const_name>\<open>expression\<close>,_) $ vars $ e))) =>
    (case vars of Const(\<^const_name>\<open>variable_unit\<close>, _) => 
                    resolve_tac ctxt @{thms subst_expression_unit_tac} i
                | Const(\<^const_name>\<open>variable_singleton\<close>,_) $ x =>
                    (case s of
                      Const(\<^const_name>\<open>Nil\<close>,_) => 
                        resolve_tac ctxt @{thms subst_expression_singleton_empty_tac} i
                    | Const(\<^const_name>\<open>Cons\<close>,_) $ (Const(\<^const_name>\<open>substitute1\<close>,_) $ y $ _) $ _ =>
                        if x = y then
                           resolve_tac ctxt @{thms subst_expression_singleton_same_tac} i
                        else
                           resolve_tac ctxt @{thms subst_expression_singleton_notsame_tac} i
                           THEN Prog_Variables.different_variable_names_tac ctxt i
                           THEN subst_expression_list_tac ctxt i
                    | _ => raise TERM("subst_expression_list_tac: not an explicit substitution",[t,s]))
                | Const(\<^const_name>\<open>variable_concat\<close>, _) $ _ $ _ => 
                    (case e of 
                       Abs(_,_,Bound 0) => 
                         resolve_tac ctxt @{thms subst_expression_concat_id_tac} i
                         THEN subst_expression_list_tac ctxt i THEN subst_expression_list_tac ctxt i
                     | _ => resolve_tac ctxt @{thms subst_expression_id_comp_tac} i
                            THEN subst_expression_list_tac ctxt i)
                | _ => raise TERM("index_vars_tac: not a varterm",[t,vars]))
  | _ => raise TERM("subst_expression_list_tac: bad shape",[t]))

(* Subgoals of the form ?x (or: expression ?Q ?e) = subst_expression s e
   where s is an explicit substitution and e is an explicit expression.

   An explicit substitution may be a list of substitution1's, or a substitution_vars. *)
fun subst_expression_tac ctxt = SUBGOAL (fn (t,i) => 
  case Logic.strip_assums_concl t |> HOLogic.dest_Trueprop of 
    (Const(\<^const_name>\<open>HOL.eq\<close>,_) $ _ $ (Const(\<^const_name>\<open>subst_expression\<close>,_) $ s $ _)) =>
    (case s of Const(\<^const_name>\<open>substitute_vars\<close>,_) $ _ $ _ => 
              resolve_tac ctxt @{thms subst_expression_convert_substitute_vars_tac} i
              THEN substitute_vars_tac ctxt i
              THEN subst_expression_list_tac ctxt i
           | _ => subst_expression_list_tac ctxt i)
  | _ => raise TERM("subst_expression_tac: bad shape",[t]))



fun is_explicit_expression (Const(\<^const_name>\<open>expression\<close>,_) $ Q $ _) =
  ((Prog_Variables.parse_varterm Q; true) handle TERM _ => false)
  | is_explicit_expression _ = false
fun is_varlist_explicit_expression (Const(\<^const_name>\<open>expression\<close>,_) $ Q $ _) =
  ((Prog_Variables.parse_varlist Q; true) handle TERM _ => false)
  |  is_varlist_explicit_expression _ = false

fun clean_expression_simproc _ ctxt ct = 
  let val t = Thm.term_of ct in
  if is_explicit_expression t andalso not (is_varlist_explicit_expression t) then
      SOME (clean_expression_conv ctxt ct) handle CTERM _ => NONE
    else
      NONE
  end

end
