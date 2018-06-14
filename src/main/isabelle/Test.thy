theory Test
  imports Encoding Tactics
begin

lemma assumes [simp]: "declared_qvars\<lbrakk>a,b,c,d\<rbrakk>"
  fixes x :: "_ subspace"
  shows "reorder_variables_hint (x\<guillemotright>\<lbrakk>a,c,b\<rbrakk>) \<lbrakk>c,d,b,a\<rbrakk> = undefined"
  apply simp
  oops

ML {*
QRHL.sort_variables (QRHL.parse_varterm @{term "variable_concat \<lbrakk>\<rbrakk> \<lbrakk>a,b,c\<rbrakk>"})
|> the |> fst
*}

(* lemma qvar_trafo_adjoint: 
  assumes "qvar_trafo A Q R"
  shows "qvar_trafo (adjoint A) R Q"
proof (unfold qvar_trafo_def, auto)
  show "distinct_qvars R" and "distinct_qvars Q" using assms unfolding qvar_trafo_def by auto
  fix C :: "('b,'b)bounded"
  have "unitary A" using assms
    using qvar_trafo_unitary by blast
  then have "C = (A \<cdot> (A* \<cdot> C \<cdot> A) \<cdot> A* )"
    by (metis (full_types) adjoint_twice assoc_left(1) times_adjoint times_idOp1 unitary_def)
  also have "\<dots>\<guillemotright>R = (A* \<cdot> C \<cdot> A)\<guillemotright>Q"
    using assms unfolding qvar_trafo_def by simp
  finally show "C\<guillemotright>R = (A* \<cdot> C \<cdot> A)\<guillemotright>Q" by assumption
qed *)


(* lemma reorder_variables_hint_subspace_conv_aux:
  "reorder_variables_hint (S\<guillemotright>Q) R \<equiv> variable_renaming_hint (S\<guillemotright>Q) A R" for S::"_ subspace"
  unfolding variable_renaming_hint_def reorder_variables_hint_def by simp

lemma reorder_variables_hint_bounded_conv_aux:
  "reorder_variables_hint (S\<guillemotright>Q) R \<equiv> variable_renaming_hint (S\<guillemotright>Q) A R" for S::"(_,_) bounded"
  unfolding variable_renaming_hint_def reorder_variables_hint_def by simp

lemma reorder_variables_hint_remove_aux: "reorder_variables_hint x R \<equiv> x" 
  unfolding reorder_variables_hint_def by simp
 *)

(* ML"open QRHL" *)

(* ML \<open>
fun variable_extension_hint_conv' ctx vtQ R vtR ct = let
val (lift,S,Q) = case Thm.term_of ct of
    Const(lift,_) $ S $ Q => (lift,S,Q)
    | _ => raise CTERM("variable_extension_hint_conv: wrong shape",[ct])
val conv_rule = case lift of @{const_name liftSpace} => @{thm join_variables_hint_subspace_conv_aux}
                           | @{const_name liftOp} => @{thm join_variables_hint_bounded_conv_aux}
                           | _ => raise CTERM("variable_extension_hint_conv: lift is "^lift, [ct])
(* val vtQ = parse_varterm Q *)
(* val vtR = parse_varterm R *)
val miss = missing_in_varterm vtQ vtR |> mk_varterm |> fst |> Thm.cterm_of ctx
val rule = infer_instantiate ctx 
  [(("S",0),Thm.cterm_of ctx S),
   (("R",0),Thm.cterm_of ctx R),
   (("R'",0),miss),
   (("Q",0),Thm.cterm_of ctx Q)]
  conv_rule 
in
rule
end
\<close> *)


(* ML \<open>
datatype lift_kind = LiftSpace | LiftOp
\<close> *)

variables quantum a :: int and quantum b :: int and quantum c :: int and quantum d :: int begin




ML \<open>

(* reorder_variables_hint_conv' @{context} 
(* ( @{term "\<lbrakk>a,c,b,d\<rbrakk>"}) *)
(parse_varterm @{term "variable_concat  \<lbrakk>\<rbrakk> \<lbrakk>a,c,b,d\<rbrakk>"}) (* TODO: should work with [[]] at the end, too *) 
@{cterm "(S::(_,_)bounded) \<guillemotright> (variable_concat \<lbrakk>a,b\<rbrakk> \<lbrakk>d\<rbrakk>)"}
;;
 *)

;;

QRHL.reorder_variables_hint_conv @{context} 
(* ( @{term "\<lbrakk>a,c,b,d\<rbrakk>"}) *)
(* (parse_varterm @{term "variable_concat  \<lbrakk>\<rbrakk> \<lbrakk>a,c,b,d\<rbrakk>"}) (* TODO: should work with [[]] at the end, too *)  *)
@{cterm "reorder_variables_hint ((S::(_,_)bounded) \<guillemotright> (variable_concat \<lbrakk>a,b\<rbrakk> \<lbrakk>d\<rbrakk>)) (variable_concat  \<lbrakk>\<rbrakk> \<lbrakk>a,c,b,d\<rbrakk>)"}
\<close>
end



ML {*
fun is_explicit_expression (Const(@{const_name expression},_) $ Q $ _) =
  ((QRHL.parse_varterm Q; true) handle TERM _ => false)
  | is_explicit_expression _ = false
fun is_varlist_explicit_expression (Const(@{const_name expression},_) $ Q $ _) =
  ((QRHL.parse_varlist Q; true) handle TERM _ => false)
  |  is_varlist_explicit_expression _ = false
*}

ML {*
fun clean_expression_simproc _ ctxt ct = 
  let val t = Thm.term_of ct in
  if is_explicit_expression t andalso not (is_varlist_explicit_expression t) then
      SOME (Encoding.clean_expression_conv ctxt ct) handle CTERM _ => NONE
    else
      NONE
  end
*}

simproc_setup clean_expression ("expression Q e") = clean_expression_simproc


instantiation expression :: (ord) ord begin
instance sorry
end


ML {*
  fun subst_expression_simproc _ ctxt ct = SOME (Encoding.subst_expression_conv ctxt ct) handle CTERM _ => NONE
*}

simproc_setup subst_expression ("subst_expression (substitute1 x (expression R f')) (expression Q e')") = subst_expression_simproc


variables
  classical x :: int and
  classical a :: int and
  classical b :: int and 
  classical c :: int and
  quantum q :: int
begin

lemma qrhl_top: "qrhl A p1 p2 (expression Q (\<lambda>z. top))" sorry
lemma qrhl_top': "f \<ge> top \<Longrightarrow> qrhl A p1 p2 (expression Q f)" sorry




lemma
  assumes [simp]: "x\<ge>0"
  shows "qrhl D [s1,sample var_x Expr[ uniform {0..max x 0}] ] [t1,t2,assign var_x Expr[0] ] Expr[ Cla[x1\<ge>x2] ]"
  using [[method_error,show_types]]
  apply (tactic \<open>Tactics.wp_tac @{context} true 1\<close>)
  apply (tactic \<open>Tactics.wp_tac @{context} false 1\<close>)
  apply simp
  by (rule qrhl_top)

lemma skip:
  assumes "A \<le> B"
  shows "qrhl A [] [] B"
  sorry

lemma expression_leq1:
  assumes "\<And>x. e x \<le> e' x"
  shows "expression \<lbrakk>v\<rbrakk> e \<le> expression \<lbrakk>v\<rbrakk> e'"
  sorry

lemma expression_leq2:
  assumes "\<And>x y. e x y \<le> e' x y"
  shows "expression \<lbrakk>v,w\<rbrakk> (\<lambda>(x,y). e x y) \<le> expression \<lbrakk>v,w\<rbrakk> (\<lambda>(x,y). e' x y)"
  sorry


schematic_goal
  assumes [simp]: "x\<ge>0"
  shows "qrhl Expr[ Cla[x1=0 \<and> x2=1] ] [qinit \<lbrakk>q\<rbrakk> Expr[ ket 0 ] ] [assign var_x Expr[x-1] ] Expr[ Cla[x1\<ge>x2] ]"
  using [[method_error,show_types]]
  apply (tactic \<open>Tactics.wp_tac @{context} true 1\<close>) 
  apply (tactic \<open>Tactics.wp_tac @{context} false 1\<close>)
  apply simp
  apply (rule skip)
  apply (rule expression_leq2)
  by simp

end

end
