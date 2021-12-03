theory Basic_Rules
  imports Relational_Hoare
begin

lemma skip_rule:
  shows "qrhl B [] [] B"
  by (cheat skip_rule)

lemma conseq_rule:
  assumes "A \<le> A'" and "B' \<le> B"
  assumes "qrhl A' b c B'"
  shows "qrhl A b c B"
  by (cheat conseq_rule)

lemma sym_rule:
  assumes "qrhl (\<lambda>m. index_flip_subspace (A (prod.swap m))) c b (\<lambda>m. index_flip_subspace (B (prod.swap m)))"
  shows "qrhl A b c B"
  by (cheat sym_rule)

lemma assign1_rule:
  fixes A B x e
  assumes \<open>cregister x\<close>
  defines "A == (\<lambda>m::cl2. B (setter (cregister_chain cFst x) (e (fst m)) m))"
  shows "qrhl A [assign x e] [] B"
  by (cheat assign1_rule)

(* 
(* TODO move *)
lemma index_flip_substitute_vars: 
  "map index_flip_substitute1 (substitute_vars xs e) = substitute_vars (index_flip_vars xs) (index_flip_expression e)"
  by (cheat index_flip_substitute_vars) *)

(* (* TODO move *)
lemma index_flip_vars_index_vars: "index_flip_vars (index_vars left xs) = index_vars (\<not> left) xs"
  by (cheat index_flip_vars_index_vars) *)

(* lemma map_expression_subst_expression:
  "map_expression f (subst_expression \<sigma> e) = subst_expression \<sigma> (map_expression f e)"
  unfolding map_expression_def 
  apply (transfer fixing: f \<sigma>)
  by auto *)

lemma assign2_rule:
  fixes A B x e
  assumes [simp]: \<open>cregister x\<close>
  defines "A == (\<lambda>m::cl2. B (setter (cregister_chain cSnd x) (e (snd m)) m))"
  shows "qrhl A [] [assign x e] B"
  apply (rule sym_rule)
  apply (subst DEADID.rel_mono_strong[of \<open>(\<lambda>m. index_flip_subspace (A (prod.swap m)))\<close>]) defer
   apply (rule assign1_rule)
  by (auto simp: A_def setter_chain setter_Fst setter_Snd case_prod_beta getter_Fst getter_Snd)

lemma sample1_rule:
  fixes A B xs e
  assumes \<open>cregister xs\<close>
  defines "xs1 == cregister_chain cFst xs"
  defines "e1 == (\<lambda>m. e (fst m))"
  defines "\<And>z. B' z == (\<lambda>m. B (setter xs1 z m))"
  defines "A == (\<lambda>m. Cla[weight (e1 m) = 1] \<sqinter> (INF z\<in>supp (e1 m). B' z m))"
  shows "qrhl A [sample xs e] [] B"
  by (cheat sample1_rule)

(* lift_definition uniform_expression_family :: "('a \<Rightarrow> 'b expression) \<Rightarrow> bool" is
  "\<lambda>e. \<forall>z. fst (e z) = fst (e undefined)" .

lemma map_expression_map_expression':
  assumes "uniform_expression_family e"
  shows "map_expression f1 (map_expression' f2 e) = map_expression' (f1 o f2) e"
  unfolding map_expression_def
  using assms apply (transfer fixing: f1 f2)
  by (auto simp: case_prod_beta) *)

(* lemma uniform_expression_family_const[simp]: "uniform_expression_family (\<lambda>_. e)"
  apply transfer by simp *)

(* lemma uniform_expression_family_pair_expression[simp]:
  assumes "uniform_expression_family e1"
  assumes "uniform_expression_family e2"
  shows "uniform_expression_family (\<lambda>z. pair_expression (e1 z) (e2 z))"
  using assms apply transfer
  by (auto simp: case_prod_beta)

lemma map_expression_map_expression2':
  assumes [simp]: "uniform_expression_family f"
  shows "map_expression f1 (map_expression2' f2 e f) = map_expression2' (\<lambda>z1 z2. f1 (f2 z1 z2)) e f"
  unfolding map_expression2'_def 
  apply (subst map_expression_map_expression')
  by (simp_all add: o_def)

lemma uniform_expression_family_expression[simp]:
  "uniform_expression_family (\<lambda>z. expression V (e z))"
  apply transfer by simp *)
  
(* lemma uniform_expression_family_subst_expression[simp]:
  assumes "uniform_expression_family e1"
  assumes "uniform_expression_family e2"
  shows "uniform_expression_family (\<lambda>z. subst_expression (substitute_vars V (e1 z)) (e2 z))"
  by (cheat uniform_expression_family_subst_expression) *)

lemma sample2_rule:
  fixes A B xs e
  assumes [simp]: \<open>cregister xs\<close>
  defines "xs1 == cregister_chain cSnd xs"
  defines "e1 == (\<lambda>m. e (snd m))"
  defines "\<And>z. B' z == (\<lambda>m. B (setter xs1 z m))"
  defines "A == (\<lambda>m. Cla[weight (e1 m) = 1] \<sqinter> (INF z\<in>supp (e1 m). B' z m))"
  shows "qrhl A [] [sample xs e] B"
  apply (rule sym_rule)
  apply (subst DEADID.rel_mono_strong[of \<open>(\<lambda>m. index_flip_subspace (A (prod.swap m)))\<close>]) defer
   apply (rule sample1_rule)
  by (auto simp: A_def B'_def e1_def xs1_def setter_chain setter_Fst getter_Snd getter_Fst
      setter_Snd case_prod_beta index_flip_subspace_INF)

(*   using [[simproc del: index_var]]
  apply (rule sym_rule)
  apply (simp add: assms index_flip_subst_expression index_flip_substitute1 
      index_flip_expression_index_expression index_flip_substitute_vars index_flip_vars_index_vars
      index_flip_map_expression2' o_def index_flip_expression_map_expression)
  apply (subst map_expression_map_expression2', simp)
  apply simp
  apply (rewrite at "qrhl \<hole>" DEADID.rel_mono_strong)
  defer
  apply (rule sample1_rule)
 *)

ML \<open>
structure Basic_Rules =
struct

fun after_sym_rule_conv ctxt =
(*   (Conv.bottom_conv (fn ctxt => (Conv.try_conv (Expressions.map_expression_conv then_conv Expressions.clean_expression_conv ctxt))) ctxt) 
then_conv *)
  (Raw_Simplifier.rewrite ctxt false @{thms 
      index_flip_subspace_lift[THEN eq_reflection]
      index_flip_subspace_top[THEN eq_reflection]
      index_flip_subspace_bot[THEN eq_reflection]
      index_flip_subspace_zero[THEN eq_reflection]
      index_flip_subspace_inf[THEN eq_reflection]
      index_flip_subspace_plus[THEN eq_reflection]
      index_flip_subspace_Cla[THEN eq_reflection]
      index_flip_subspace_quantum_equality[THEN eq_reflection]

      (* TODO move to general tactic? *)
      index_flip_qvar_register_pair[THEN eq_reflection]
      index_flip_qvar_chain[THEN eq_reflection]
      index_flip_qvar_Fst[THEN eq_reflection]
      index_flip_qvar_Snd[THEN eq_reflection]
      getter_Fst_chain_swap[THEN eq_reflection]
      getter_Snd_chain_swap[THEN eq_reflection]
  })
(* then_conv
  (Expressions.index_conv ctxt) *)

fun sym_tac ctxt =
  resolve_tac ctxt @{thms sym_rule}
  THEN'
  CONVERSION (after_sym_rule_conv ctxt)
end
\<close>

(* Testing *)
experiment
  fixes Q :: \<open>bit qvariable\<close>
and x :: \<open>bit cvariable\<close>
and G :: \<open>bit cvariable\<close>
and H :: \<open>bit cvariable\<close>
and quantA :: \<open>99 qvariable\<close>
and Hout :: \<open>10 qvariable\<close>
and Hin :: \<open>9 qvariable\<close>
and Gout :: \<open>10 qvariable\<close>
and Gin :: \<open>9 qvariable\<close>
assumes [variable]: \<open>qregister Q\<close> \<open>cregister x\<close> \<open>cregister G\<close>
 \<open>cregister H\<close> \<open>qregister quantA\<close> \<open>qregister Hout\<close>
 \<open>qregister Hin\<close> \<open>qregister Gout\<close> \<open>qregister Gin\<close>
begin
lemma "qrhl Expr[\<CC>\<ll>\<aa>[G1 = G2 \<and> Hr1 = Hr2 \<and> H01 = H02 \<and> Hq1 = Hq2 \<and> H1 = H2 \<and> pk1 = pk2 \<and> skfo1 = skfo2 \<and> mstar1 = mstar2 \<and> cstar1 = cstar2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> K'1 = K'2 \<and> b1 = b2]
         \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>]
  [] [] Expr[top]"
  (* lemma "qrhl Expr[HX\<guillemotright>\<lbrakk>Q1,Q2\<rbrakk>] c d Expr[Cla[x1=x2]]" *)
  apply (tactic \<open>Basic_Rules.sym_tac \<^context> 1\<close>)
  oops
end

end
