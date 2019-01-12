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

lemma assign2_rule:
  fixes A B x e
  defines "x1 == index_var False x"
  defines "e1 == index_expression False e"
  defines "A == subst_expression [substitute1 x1 e1] B"
  shows "qrhl A [] [assign x e] B"
  using [[simproc del: index_var]]
  apply (rule sym_rule)
  apply (simp add: assms index_flip_subst_expression index_flip_substitute1 index_flip_expression_index_expression)
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
      index_flip_expression_index_expression
      index_flip_map_expression2' o_def)
  by (rule sample1_rule)

end
