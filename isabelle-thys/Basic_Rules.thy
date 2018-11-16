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
  assumes "qrhl (index_flip_expression A) c b (index_flip_expression B)"
  shows "qrhl A b c B"
  by (cheat sym_rule)

lemma assign1_rule:
  fixes A B x e
  defines "x1 == index_var True x"
  defines "e1 == index_expression True e"
  defines "A == subst_expression [substitute1 x1 e1] B"
  shows "qrhl A [assign x e] [] B"
  by (cheat assign1_rule)

(* TODO move *)
lemma index_flip_subst_expression: "index_flip_expression (subst_expression \<sigma> e) 
  = subst_expression (map index_flip_substitute1 \<sigma>) (index_flip_expression e)"
  by (cheat index_flip_subst_expression)

(* TODO move *)
lemma index_flip_var_index_var_raw[simp]: "index_flip_var_raw (index_var_raw left x) = index_var_raw (\<not> left) x"
  apply transfer
  by (auto simp: index_flip_name_def)

(* TODO move *)
lemma index_flip_var_index_var[simp]: "index_flip_var (index_var left x) = index_var (\<not>left) x"
  apply transfer by simp

(* TODO move *)
lemma index_flip_expression_index_expression: "index_flip_expression (index_expression left x) =
  index_expression (\<not>left) x"
  apply transfer apply auto
  using image_iff by fastforce

lemma expression_vars_index_flip_expression: "expression_vars (index_flip_expression e) = index_flip_var_raw ` expression_vars e"
  by (simp add: expression_vars.rep_eq index_flip_expression.rep_eq split_beta)

lemma expression_eval_index_flip_expression: "expression_eval (index_flip_expression e) = 
  expression_eval e o index_flip_mem2"
  unfolding o_def
  by (simp add: expression_eval.rep_eq index_flip_expression.rep_eq split_beta)


lemma expression_eqI: "expression_vars e = expression_vars f \<Longrightarrow> expression_eval e = expression_eval f \<Longrightarrow> e = f"
  apply transfer by auto

(* TODO move *)
lemma index_flip_expression_map_expression': "index_flip_expression (map_expression' f ez)
  = map_expression' f (index_flip_expression o ez)"
proof (cases "\<forall>z. expression_vars (ez z) = expression_vars (ez undefined)")
  case True
  then have True': "expression_vars (index_flip_expression (ez z)) = expression_vars (index_flip_expression (ez undefined))" for z
    apply transfer
    apply simp
    by (metis (mono_tags, lifting) fst_conv split_beta)

  from True have "expression_vars (map_expression' f ez) = expression_vars (ez undefined)"
    apply transfer by (simp add: fst_def)
  hence "expression_vars (index_flip_expression (map_expression' f ez)) 
       = index_flip_var_raw ` expression_vars (ez undefined)"
    unfolding expression_vars_index_flip_expression by simp
  moreover from True' have "expression_vars (map_expression' f (index_flip_expression o ez)) 
      = expression_vars (index_flip_expression (ez undefined))"
    unfolding o_def apply transfer by (auto simp: fst_def)
  moreover have "expression_vars (index_flip_expression (ez undefined))
      = index_flip_var_raw ` expression_vars (ez undefined)"
    unfolding expression_vars_index_flip_expression by simp
  ultimately have vars: "expression_vars (index_flip_expression (map_expression' f ez))
                 = expression_vars (map_expression' f (index_flip_expression o ez))"
    by simp

  from True have "expression_eval (map_expression' f ez) = (\<lambda>m. f (\<lambda>z. expression_eval (ez z) m))"
    apply transfer by (auto simp: fst_def snd_def)
  hence "expression_eval (index_flip_expression (map_expression' f ez)) 
       = (\<lambda>m. f (\<lambda>z. expression_eval (ez z) (index_flip_mem2 m)))"
    unfolding expression_eval_index_flip_expression by (simp add: o_def)
  moreover from True' have "expression_eval (map_expression' f (index_flip_expression o ez)) 
      = (\<lambda>m. f (\<lambda>z. expression_eval (index_flip_expression (ez z)) m))"
    unfolding o_def apply transfer by (auto simp: fst_def snd_def)
  moreover have "expression_eval (ez z) (index_flip_mem2 m) = expression_eval (index_flip_expression (ez z)) m" for m z
    apply transfer by (simp add: split_beta)
  ultimately have eval: "expression_eval (index_flip_expression (map_expression' f ez))
                 = expression_eval (map_expression' f (index_flip_expression o ez))"
    by simp
  
  from vars eval show ?thesis
    by (rule expression_eqI)
next
  case False
  then have False': "\<not> (\<forall>z. expression_vars (index_flip_expression (ez z)) = expression_vars (index_flip_expression (ez undefined)))"
    apply transfer
    apply (simp add: case_prod_beta)
    using index_flip_var_raw_inject by blast

  have "map_expression' f ez = const_expression undefined"
    apply (subst Rep_expression_inject[symmetric])
    using False by (auto simp: map_expression'.rep_eq expression_vars.rep_eq case_prod_beta)
  then have "index_flip_expression (map_expression' f ez) = const_expression undefined"
    by simp
  also from False' have "map_expression' f (index_flip_expression o ez) = const_expression undefined"
    apply (subst Rep_expression_inject[symmetric])
    using False by (auto simp: map_expression'.rep_eq expression_vars.rep_eq case_prod_beta)
  finally show ?thesis by metis
qed


(* TODO move *)
lemma index_flip_expression_pair_expression: "index_flip_expression (pair_expression e1 e2)
  = pair_expression (index_flip_expression e1) (index_flip_expression e2)"
  apply transfer by auto

(* TODO move *)
lemma index_flip_map_expression2': "index_flip_expression (map_expression2' f e1 e2) = 
  map_expression2' f (index_flip_expression e1) (index_flip_expression o e2)"
  unfolding map_expression2'_def by (simp add: index_flip_expression_pair_expression index_flip_expression_map_expression' o_def)

lemma assign2_rule:
  fixes A B x e
  defines "x1 == index_var False x"
  defines "e1 == index_expression False e"
  defines "A == subst_expression [substitute1 x1 e1] B"
  shows "qrhl A [] [assign x e] B"
  using [[simproc del: index_var]]
  apply (rule sym_rule)
  apply (simp add: assms index_flip_subst_expression index_flip_substitute1 index_flip_var_index_var index_flip_expression_index_expression)
  by (rule assign1_rule)

lemma sample1_rule:
  fixes A B x e
  defines "x1 == index_var True x"
  defines "e1 == index_expression True e"
  defines "\<And>z. B' z == subst_expression [substitute1 x1 (const_expression z)] B"
  defines "A == map_expression2' (\<lambda>e1 B'. Cla[weight e1 = 1] \<sqinter> (INF z:supp e1. B' z)) e1 B'"
  shows "qrhl A [sample x e] [] B"
  by (cheat sample1_rule)

lemma sample2_rule:
  fixes A B x e
  defines "x1 == index_var False x"
  defines "e1 == index_expression False e"
  defines "\<And>z. B' z == subst_expression [substitute1 x1 (const_expression z)] B"
  defines "A == map_expression2' (\<lambda>e1 B'. Cla[weight e1 = 1] \<sqinter> (INF z:supp e1. B' z)) e1 B'"
  shows "qrhl A [] [sample x e] B"
  using [[simproc del: index_var]]
  apply (rule sym_rule)
  apply (simp add: assms index_flip_subst_expression index_flip_substitute1 
      index_flip_var_index_var index_flip_expression_index_expression
      index_flip_map_expression2' o_def)
  by (rule sample1_rule)

end
