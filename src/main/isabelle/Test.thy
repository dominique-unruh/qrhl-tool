theory Test
  imports (* Real_Sqrt2 *) Encoding Tactics QRHL_Code 
begin


(* definition "matrix_H = mat_of_rows_list 2 [ [sqrt 2::complex, sqrt 2], [sqrt 2, -sqrt 2] ]"
axiomatization where bounded_of_mat_H[code]: "mat_of_bounded hadamard = matrix_H"

value "hadamard" *)

(* variables quantum q :: bit and quantum r :: bit and quantum s :: bit and quantum t :: bit begin
ML \<open>
  
;;

QRHL.extend_lift_as_var_concat_hint_conv @{context} @{cterm "extend_lift_as_var_concat_hint ((A::_ subspace)\<guillemotright>\<lbrakk>q,t,s\<rbrakk>) \<lbrakk>r,s\<rbrakk>"};;
(* QRHL.reorder_lift_conv @{context} (QRHL.parse_varterm @{term "\<lbrakk>q,r,s\<rbrakk>"}) @{cterm "((A::_ subspace)\<guillemotright>\<lbrakk>q,s\<rbrakk>)"};; *)
\<close>                                
end *)

(* lemma div:
  fixes S :: "_ subspace"
  shows "NO_MATCH ((variable_concat a b),b) (Q,R) \<Longrightarrow> (space_div (S\<guillemotright>Q) \<psi> R) = 
  (space_div (extend_lift_as_var_concat_hint (S\<guillemotright>Q) R)) \<psi> R"
  unfolding extend_lift_as_var_concat_hint_def by simp *)

(* axiomatization space_div_unlifted :: "('a*'b) subspace \<Rightarrow> 'b vector \<Rightarrow> 'a subspace"
        (* space_div_unlifted S \<psi> := {\<phi>. \<phi>\<otimes>\<psi> \<in> S} *)
  where div2: "space_div (S\<guillemotright>(variable_concat Q R)) \<psi> R = (space_div_unlifted S \<psi>)\<guillemotright>Q"
 *)

(* simproc_setup tmp ("extend_lift_as_var_concat_hint A R") = \<open>fn _ => fn ctxt => fn ct => 
SOME (extend_lift_as_var_concat_hint_conv ctxt ct) handle CTERM _ => NONE\<close> *)

(* space_div_unlifted S \<psi> := {\<phi>. \<phi>\<otimes>\<psi> \<in> S} 
   = {\<phi>. (I\<otimes>\<psi>)*\<phi> \<in> S}
   = {\<phi>. (1-proj S)*(I\<otimes>\<psi>)*\<phi> = 0} *)
(* lemma [code]: "space_div_unlifted S \<psi> = kernel ((idOp-Proj S) \<cdot> addState \<psi>)"
  sorry *)







variables quantum q :: bit and quantum r :: bit begin
term "hadamard\<guillemotright>\<lbrakk>q\<rbrakk>"
lemma "space_div (span{ket 0}\<guillemotright>\<lbrakk>q\<rbrakk>) (ket 1) \<lbrakk>r\<rbrakk> = span{ket 0}\<guillemotright>\<lbrakk>q\<rbrakk>"
  apply (auto simp: prepare_for_code)
  by eval

lemma "space_div (span{ket (0,0), ket(1,1)}\<guillemotright>\<lbrakk>q,r\<rbrakk>) (ket 0) \<lbrakk>r\<rbrakk> = span{ket 0}\<guillemotright>\<lbrakk>q\<rbrakk>"
  apply (auto simp: prepare_for_code)
  by eval

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
