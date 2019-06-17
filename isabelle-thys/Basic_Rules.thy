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


lift_definition index_flip_vector :: "mem2 ell2 \<Rightarrow> mem2 ell2" is
  "\<lambda>\<psi>. \<psi> o index_flip_mem2"
  by (cheat xxx)

lift_definition index_flip_subspace :: "mem2 ell2 linear_space \<Rightarrow> mem2 ell2 linear_space" is
  "\<lambda>S. index_flip_vector ` S"
  by (cheat TODO)

(* typedef 'a bla = "UNIV::'a set set" by auto
setup_lifting type_definition_bla

lift_definition index_flip_subspace :: "'a::chilbert_space bla \<Rightarrow> 'a bla" is
  "undefined :: 'a set \<Rightarrow> 'a set". *)


(* lemma sym_rule:
  assumes "qrhl (index_flip_expression (map_expression index_flip_subspace A)) c b (index_flip_expression (map_expression index_flip_subspace B))"
  shows "qrhl A b c B"
  by (cheat sym_rule)  *)


lemma sym_rule:
  assumes "qrhl (index_flip_expression (A)) c b (index_flip_expression (B))"
  shows "qrhl A b c B"
  by (cheat sym_rule)  

lemma assign1_rule:
  fixes A B x e
  defines "x1 == index_vars True x"
  defines "e1 == index_expression True e"
  defines "A == subst_expression (substitute_vars x1 e1) B"
  shows "qrhl A [assign x e] [] B"
  by (cheat assign1_rule)


(* TODO move *)
lemma index_flip_substitute_vars: 
  "map index_flip_substitute1 (substitute_vars xs e) = substitute_vars (index_flip_vars xs) (index_flip_expression e)"
  by (cheat index_flip_substitute_vars)

(* TODO move *)
lemma index_flip_vars_index_vars: "index_flip_vars (index_vars left xs) = index_vars (\<not> left) xs"
  by (cheat index_flip_vars_index_vars)

lemma assign2_rule:
  fixes A B x e
  defines "x1 == index_vars False x"
  defines "e1 == index_expression False e"
  defines "A == subst_expression (substitute_vars x1 e1) B"
  shows "qrhl A [] [assign x e] B"
  using [[simproc del: index_var]]
  apply (rule sym_rule)
  apply (simp add: assms index_flip_vars_index_vars index_flip_substitute_vars index_flip_subst_expression index_flip_substitute1 index_flip_expression_index_expression)
  (* by (rule assign1_rule) *)
  by (cheat TODO)

lemma sample1_rule:
  fixes A B xs e
  defines "xs1 == index_vars True xs"
  defines "e1 == index_expression True e"
  defines "\<And>z. B' z == subst_expression (substitute_vars xs1 (const_expression z)) B"
  defines "A == map_expression2' (\<lambda>e1 B'. Cla[weight e1 = 1] \<sqinter> (INF z:supp e1. B' z)) e1 B'"
  shows "qrhl A [sample xs e] [] B"
  by (cheat sample1_rule)

thm index_flip_subst_expression
thm index_flip_substitute1

lemma sample2_rule:
  fixes A B xs e
  defines "xs1 == index_vars False xs"
  defines "e1 == index_expression False e"
  defines "\<And>z. B' z == subst_expression (substitute_vars xs1 (const_expression z)) B"
  defines "A == map_expression2' (\<lambda>e1 B'. Cla[weight e1 = 1] \<sqinter> (INF z:supp e1. B' z)) e1 B'"
  shows "qrhl A [] [sample xs e] B"
  using [[simproc del: index_var]]
  apply (rule sym_rule)
  apply (simp add: assms index_flip_subst_expression index_flip_substitute1 
      index_flip_expression_index_expression index_flip_substitute_vars index_flip_vars_index_vars
      index_flip_map_expression2' o_def)
  (* by (rule sample1_rule) *)
  by (cheat TODO)

end
