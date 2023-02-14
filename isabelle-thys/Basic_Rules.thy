theory Basic_Rules
  imports Relational_Hoare
begin

lemma skip_rule:
  shows "qrhl B [] [] B"
  by (auto simp add: qrhl_def denotation_block)

lemma conseq_rule:
  assumes "\<And>m. A m \<le> A' m" and "\<And>m. B' m \<le> B m"
  assumes "qrhl A' b c B'"
  shows "qrhl A b c B"
  using  assms(3)
  by (auto intro!: satisfies_mono[OF assms(1)] satisfies_mono[OF assms(2)] simp add: qrhl_def)

lemma skip_conseq_rule:
  assumes \<open>\<And>m. A m \<le> B m\<close>
  shows "qrhl A [] [] B"
  apply (rule conseq_rule[where A'=A and B'=A])
  using assms apply auto[2]
  by (rule skip_rule)

lemma sym_rule:
  assumes "qrhl (\<lambda>m. index_flip_subspace (A (prod.swap m))) c b (\<lambda>m. index_flip_subspace (B (prod.swap m)))"
  shows "qrhl A b c B"
  sorry

lemma assign1_rule:
  fixes A B x e
  assumes \<open>cregister x\<close>
  defines "A == (\<lambda>m::cl2. B (setter (cregister_chain cFst x) (e (fst m)) m))"
  shows "qrhl A [assign x e] [] B"
  sorry

(* 
(* TODO move *)
lemma index_flip_substitute_vars: 
  "map index_flip_substitute1 (substitute_vars xs e) = substitute_vars (index_flip_vars xs) (index_flip_expression e)"
*)

(* (* TODO move *)
lemma index_flip_vars_index_vars: "index_flip_vars (index_vars left xs) = index_vars (\<not> left) xs"
*)

(* TODO move *)
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
  by (auto simp: A_def setter_chain setter_cFst setter_cSnd case_prod_beta)

lemma sample1_rule:
  fixes A B xs e
  assumes \<open>cregister xs\<close>
  defines "xs1 == cregister_chain cFst xs"
  defines "e1 == (\<lambda>m. e (fst m))"
  defines "\<And>z. B' z == (\<lambda>m. B (setter xs1 z m))"
  defines "A == (\<lambda>m. Cla[weight (e1 m) = 1] \<sqinter> (INF z\<in>supp (e1 m). B' z m))"
  shows "qrhl A [sample xs e] [] B"
  sorry

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

lemma map_expression_map_expression3'':
  assumes [simp]: "uniform_expression_family f"
  assumes [simp]: "uniform_expression_family g"
  shows "map_expression f1 (map_expression3'' f2 e f g) = 
      map_expression3'' (\<lambda>z1 z2 z3. f1 (f2 z1 z2 z3)) e f g"
  unfolding map_expression3''_def 
  apply (subst map_expression_map_expression')
  by (simp_all add: o_def)

lemma uniform_expression_family_expression[simp]:
  "uniform_expression_family (\<lambda>z. expression V (e z))"
  apply transfer by simp *)
  
(* lemma uniform_expression_family_subst_expression[simp]:
  assumes "uniform_expression_family e1"
  assumes "uniform_expression_family e2"
  shows "uniform_expression_family (\<lambda>z. subst_expression (substitute_vars V (e1 z)) (e2 z))"
*)

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
  by (auto simp: A_def B'_def e1_def xs1_def setter_chain setter_cFst setter_cSnd case_prod_beta)

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

fun skip_conseq_tac ctxt = resolve_tac ctxt @{thms skip_conseq_rule}
  THEN' Expressions.generalize_getters ctxt
end
\<close>



(* Testing *)
experiment
  fixes q :: \<open>bit qvariable\<close>
    and x :: \<open>bit cvariable\<close>
assumes [register]: \<open>qregister q\<close> \<open>cregister x\<close>
begin

lemma \<open>qrhl Expr[Cla[x1 = x2]] [] [] Expr[Cla[x2 = 1]]\<close> if \<open>finite X\<close>
  apply (tactic \<open>Basic_Rules.skip_conseq_tac \<^context> 1\<close>)
  oops
end

end
