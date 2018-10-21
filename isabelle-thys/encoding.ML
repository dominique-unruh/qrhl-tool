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
(* TODO remove? *)
fun map_expression_subterm_conv ctxt = 
  Raw_Simplifier.rewrite ctxt false @{thms 
    map_expression[THEN eq_reflection]
    map_expression'[THEN eq_reflection]
    map_expression2'[THEN eq_reflection]
    map_expression2[THEN eq_reflection]
    map_expression3[THEN eq_reflection]
    map_expression3'[THEN eq_reflection]}

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
