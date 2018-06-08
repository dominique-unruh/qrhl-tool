structure Encoding = 
struct

fun mk_expressionT T = Type(@{type_name expression}, [T])

(* val expression_to_term_simpset = clear_simpset @{context} addsimps @{thms case_prod_conv} *)

(* TODO: should make sure it's sound (i.e., reject expressions that cannot be converted, check whether vars are declared *)
fun expression_to_term t =
  let val (vs,e) = case t of Const(@{const_name expression},_) $ vs $ e => (vs,e) | _ => raise (TERM("expression_to_term",[t]))
      val vars = QRHL.parse_varlist vs 
          |> map (fn (x,T) => Free (String.extract (x,4,NONE),T)) (* unsafe, not checking whether the var name is wellformed *)
          (* |> @{print} *)
      val e' = e $ HOLogic.mk_tuple vars
      val e'' = Raw_Simplifier.rewrite_term @{theory} @{thms case_prod_conv[THEN eq_reflection]} [] e'
  in
    e''
  end

(* val _ = expression_to_term @{term "expression \<lbrakk>var_x,var_y\<rbrakk> (\<lambda>(x,y). x+y)"} |> (fn t => (t,Thm.cterm_of @{context} t)) |> @{print} *)

fun expression_to_term_typ t =
  let val t2 = expression_to_term t in (t2, fastype_of t2) end

fun add_index_to_expression t left =
  let val suffix = if left then "1" else "2"
      fun rename (Free(x,T)) =  Free(x^suffix,T)
        | rename t = t
      val (vs,e,T) = case t of Const(@{const_name expression},T) $ vs $ e => (vs,e,T) | _ => 
            raise (TERM("add_index_to_expression",[t]))
      val vs = Term.map_aterms rename vs
  in
    Const(@{const_name expression},T) $ vs $ e
  end
    
fun term_to_expression ctx t =
  let val is_classical = QRHL.is_classical_variable ctx
      val frees = Term.add_frees t [] |> filter (fn (v,_) => is_classical v) |> rev
      val (vars,varsT) = 
        frees |> map (fn (v,T) => ("var_"^v,T)) |> QRHL.varterm_from_list |> QRHL.mk_varterm
      val pattern = HOLogic.mk_tuple (map Free frees)
      val e = HOLogic.tupled_lambda pattern t |> @{print}
      val T = fastype_of t
  in
    Const(@{const_name expression}, QRHL.mk_variablesT varsT --> (varsT --> T) --> mk_expressionT T)
      $ vars $ e
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

fun term_to_expression_untyped ctx t =
  let val lookup_var = QRHL.lookup_variable ctx
      val frees = Term.add_frees t [] |> filter (fn (v,_) => lookup_var v = SOME QRHL.Classical) |> rev
      val (vars,varsT) = 
        frees |> map (fn (v,T) => ("var_"^v,T)) |> QRHL.varterm_from_list |> QRHL.mk_varterm
      val pattern = mk_tuple_untyped (map Free frees)
      val e = tupled_lambda_untyped pattern t
  in
    Const(@{const_name expression}, QRHL.mk_variablesT varsT --> (varsT --> dummyT) --> @{typ "dummy expression"})
      $ vars $ e
  end

fun read_expression ctx str =
  let val t = Syntax.read_term ctx str
  in term_to_expression ctx t end

fun read_predicate ctx str =
  let val preterm = Syntax.parse_term ctx str
      val t = Syntax.check_term ctx (Type.constraint @{typ "predicate"} preterm)
  in term_to_expression ctx t end

(* Translates "expression Q e" (where Q is an explicit variable list) into "expression Q (%(x\<^sub>1,...). e (x\<^sub>1,...)"
   with one x\<^sub>i for each variable in Q. The result is a well-formed explicit expression *)
fun clean_expression_abs_pat_conv ctxt ct = let
  val Q = case Thm.term_of ct of
    Const(@{const_name expression},_) $ Q $ _ => Q
    | _ => raise CTERM("clean_expression_abs_pat_conv",[ct])
  val varlist = QRHL.parse_varlist Q
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
fun clean_expression_conv_varlist ctxt : conv = Conv.repeat_conv (Misc.change_conv (clean_expression_conv_varlist1 ctxt))

(* Converts a well-formed explicit expression into a well-formed explicit expression, 
   simplifying subterms "case (x,y) of (x,y) => ...". (clean_expression_conv_varlist introduces such subterms.) *)
fun clean_expression_conv_case_prod ctxt : conv = Raw_Simplifier.rewrite ctxt false
  @{thms case_prod_conv[THEN eq_reflection]}

(* Converts an explicit expression into a well-formed explicit expression *)
fun clean_expression_conv ctxt = 
  clean_expression_conv_varlist ctxt then_conv 
  clean_expression_abs_pat_conv ctxt then_conv
  clean_expression_conv_case_prod ctxt


(* Converts "index_var True/False x" (where x is a free variable) into "x1" or "x2",
   assuming x is declared via the variables-command or equivalent.
   (More specifically, it requires that simp rules "variable_name x/x1/x2 = ''...''" with 
   the correct names are declared.) *)
fun index_var_conv ctxt ct =
  let val (lrname,x,T) = case Thm.term_of ct of
        Const(@{const_name index_var},_) $ Const(lrname,_) $ Free(x,T) => (lrname,x,T)
      | _ => raise CTERM("index_var_conv: wrong shape",[ct])
      val lr = case lrname of 
          @{const_name True} => true
        | @{const_name False} => false
        | _ => raise CTERM("index_var_conv: wrong shape (expected True/False as first arg)",[ct])

      val suffix = (if lr then "1" else "2")
      val x1 = x ^ suffix

      val varname_x = Raw_Simplifier.rewrite_cterm (false,false,false) (fn _ => fn _ => NONE) ctxt (Thm.cterm_of ctxt 
        (Const(@{const_name variable_name}, T --> @{typ string}) $ Free(x,T)))

      val varname_x1 = Raw_Simplifier.rewrite_cterm (false,false,false) (fn _ => fn _ => NONE) ctxt (Thm.cterm_of ctxt 
        (Const(@{const_name variable_name}, T --> @{typ string}) $ Free(x1,T)))

      val helper_thm = if lr then @{thm index_var_conv1_aux} else  @{thm index_var_conv2_aux}
  
      val name_x = varname_x |> Thm.concl_of |> Logic.dest_equals |> snd
      val name_eq = Raw_Simplifier.rewrite_cterm (false,false,false) (fn _ => fn _ => NONE) ctxt
        (@{term "op@ :: string=>_=>_"} $ name_x $ HOLogic.mk_string suffix |> Thm.cterm_of ctxt)
  in
    helper_thm OF [varname_x, varname_x1, name_eq]
  end

(* Simproc that simplifies using index_var_conv, see there.  *)
fun index_var_simproc _ ctxt ct = SOME (index_var_conv ctxt ct) handle CTERM _ => NONE

(* Rewrites all index_{var,vars,expression} subterms (e.g., index_var True x \<rightarrow> x1, etc.).
   If the involved variables, variable lists, and expressions are all explicit, this will
   remove all occurrences of index_{...}.
*)
fun index_conv ctxt =
  Raw_Simplifier.rewrite ctxt false @{thms 
        index_expression_def[THEN eq_reflection]
        index_vars_concat[THEN eq_reflection]
        index_vars_singleton[THEN eq_reflection]
        index_vars_unit[THEN eq_reflection]}
then_conv
  Conv.top_sweep_conv index_var_conv ctxt

(* Rewrites subterms of the form "map_expression ..." (or variants map_expression', 2', 2, 3)
   If the involved variables, variable lists, and expressions are all explicit, this will
   remove all occurrences of map_expression and variants.
 *)
fun map_expression_conv ctxt = 
  Raw_Simplifier.rewrite ctxt false @{thms 
    map_expression[THEN eq_reflection]
    map_expression'_def[THEN eq_reflection]
    map_expression2'[THEN eq_reflection]
    map_expression2[THEN eq_reflection]
    map_expression3[THEN eq_reflection]}

fun subst_expression_conv_tac1 ctxt =
  resolve_tac ctxt @{thms subst_expression_concat_id_aux subst_expression_singleton_same_aux subst_expression_unit_aux} 1
  ORELSE
  CHANGED (resolve_tac ctxt @{thms subst_expression_id_comp_aux} 1)
  ORELSE 
  (resolve_tac ctxt @{thms subst_expression_singleton_notsame_aux} 1
        THEN Misc.SOLVE1 (simp_tac ctxt 1))

fun subst_expression_conv_tac ctxt = REPEAT_DETERM (subst_expression_conv_tac1 ctxt)

fun subst_expression_conv_noclean_check (_:Proof.context) t = let
  val (sub,e) = case t of 
    Const(@{const_name subst_expression},_) $ sub $ e => (sub,e)
    | _ => raise TERM("not a subst_expression term",[t])
  val (x,_) = case sub of
    Const(@{const_name substitute1},_) $ x $ f => (x,f)
    | _ => raise TERM("not an explicit substitution (substitute1 x f)",[t,sub])
  val (Q,_) = case e of
    Const(@{const_name expression},_) $ Q $ e' => (Q,e')
    | _ => raise TERM("not an explicit expression (substitute1 Q e)",[t,e])
  val _ = QRHL.parse_varlist Q
  val _ = case x of
    Free _ => ()
    | _ => raise TERM("not an explicit variable name",[t,x])
in
  ()
end

val subst_expression_conv_noclean = Misc.conv_from_tac subst_expression_conv_noclean_check subst_expression_conv_tac

fun subst_expression_conv ctxt = subst_expression_conv_noclean ctxt then_conv clean_expression_conv ctxt


end
