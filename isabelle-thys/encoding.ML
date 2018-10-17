structure Encoding = 
struct



fun dest_qrhl (Const(\<^const_name>\<open>qrhl\<close>,_) $ A $ p1 $ p2 $ B) = (A,p1,p2,B)
  | dest_qrhl _ = raise Match
fun dest_qrhl_goal t = Logic.strip_imp_concl t |> HOLogic.dest_Trueprop |> dest_qrhl

(* val expression_to_term_simpset = clear_simpset @{context} addsimps @{thms case_prod_conv} *)

fun read_predicate ctx str =
  let val preterm = Syntax.parse_term ctx str
      val t = Syntax.check_term ctx (Type.constraint \<^typ>\<open>predicate\<close> preterm)
  in Expressions.term_to_expression ctx t end


(* Rewrites subterms of the form "map_expression ..." (or variants map_expression', 2', 2, 3)
   If the involved variables, variable lists, and expressions are all explicit, this will
   remove all occurrences of map_expression and variants.
 *)
fun map_expression_conv ctxt = 
  Raw_Simplifier.rewrite ctxt false @{thms 
    map_expression[THEN eq_reflection]
    map_expression'[THEN eq_reflection]
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
    Const(\<^const_name>\<open>subst_expression\<close>,_) $ sub $ e => (sub,e)
    | _ => raise TERM("not a subst_expression term",[t])
  val (x,_) = case sub of
    Const(\<^const_name>\<open>substitute1\<close>,_) $ x $ f => (x,f)
    | _ => raise TERM("not an explicit substitution (substitute1 x f)",[t,sub])
  val (Q,_) = case e of
    Const(\<^const_name>\<open>expression\<close>,_) $ Q $ e' => (Q,e')
    | _ => raise TERM("not an explicit expression (substitute1 Q e)",[t,e])
  val _ = Prog_Variables.parse_varlist Q
  val _ = case x of
    Free _ => ()
    | _ => raise TERM("not an explicit variable name",[t,x])
in
  ()
end

val subst_expression_conv_noclean = Misc.conv_from_tac subst_expression_conv_noclean_check subst_expression_conv_tac

fun subst_expression_conv ctxt = subst_expression_conv_noclean ctxt then_conv Conv.try_conv (Expressions.clean_expression_conv ctxt)

fun is_explicit_expression (Const(\<^const_name>\<open>expression\<close>,_) $ Q $ _) =
  ((QRHL.parse_varterm Q; true) handle TERM _ => false)
  | is_explicit_expression _ = false
fun is_varlist_explicit_expression (Const(\<^const_name>\<open>expression\<close>,_) $ Q $ _) =
  ((Prog_Variables.parse_varlist Q; true) handle TERM _ => false)
  |  is_varlist_explicit_expression _ = false

fun clean_expression_simproc _ ctxt ct = 
  let val t = Thm.term_of ct in
  if is_explicit_expression t andalso not (is_varlist_explicit_expression t) then
      SOME (Expressions.clean_expression_conv ctxt ct) handle CTERM _ => NONE
    else
      NONE
  end

end
