theory Test
  imports Encoding Tactics
begin

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
