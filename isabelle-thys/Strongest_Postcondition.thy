theory Strongest_Postcondition
  imports Tactics Basic_Rules Weakest_Precondition
begin

lemma pair_expression_footprint:
  \<open>expression_vars (pair_expression e f) = expression_vars e \<union> expression_vars f\<close>
  apply transfer
  by auto

lemma expression_eval_map_expression3'':
  assumes "\<And>z. expression_vars (e2 z) = expression_vars (e2 undefined)"
  assumes "\<And>z. expression_vars (e3 z) = expression_vars (e3 undefined)"
  shows "expression_eval (map_expression3'' f e1 e2 e3) x = f (expression_eval e1 x) (\<lambda>z. expression_eval (e2 z) x) (\<lambda>z. expression_eval (e3 z) x)"
  unfolding map_expression3''_def
  apply (subst expression_eval_map_expression')
  apply (auto simp: pair_expression_footprint)
  using assms by blast+

lemma subst_mem2_twice: \<open>subst_mem2 (substitute_vars x e) (subst_mem2 (substitute_vars x f) m) = subst_mem2 (substitute_vars x e) m\<close>
  by (cheat subst_mem2_twice)

lemma subst_mem2_eval_vars: \<open>subst_mem2 (substitute_vars x1 Expr[eval_variables x1 m]) m = m\<close>
  by (cheat subst_mem2_eval_vars)

lemma subst_expression_footprint_substitute_vars_const: \<open>subst_expression_footprint (substitute_vars x Expr[z]) y = y - set (raw_variables x)\<close>
  by (cheat subst_expression_footprint_substitute_vars_const)

lemma eval_var_subst_that_var: \<open>eval_variables x (subst_mem2 (substitute_vars x e) m) = expression_eval e m\<close> if \<open>distinct_qvars x\<close>
  by (cheat eval_var_subst_that_var)

lemma flatten_tree_index: \<open>flatten_tree (index_vartree side x) = map (index_var_raw side) (flatten_tree x)\<close>
  apply (induction x)
  by (auto simp: index_vartree_def)

lemma distinct_qvars_index: \<open>distinct_qvars (index_vars side x) \<longleftrightarrow> distinct_qvars x\<close>
  unfolding distinct_qvars_def
  apply (transfer fixing: side)
  by (auto simp: flatten_tree_index distinct_map index_var_raw_inject intro!: inj_onI)

lemma sp1_assign_tac:
  fixes A B x v
  assumes x1: "x1 = index_vars True x"
  assumes e1: \<open>e1 = index_expression True e\<close>
  assumes A': \<open>\<And>z. A' z = subst_expression (substitute_vars x1 (const_expression z)) A\<close>
  assumes e1': \<open>\<And>z. e1' z = subst_expression (substitute_vars x1 (const_expression z)) e1\<close>
  assumes B: \<open>B = map_expression3'' (\<lambda>x1' A' e1'. SUP z. A' z \<sqinter> Cla[x1' = e1' z]) (expression x1 (\<lambda>x. x)) A' e1'\<close>
  assumes dist_x: \<open>distinct_qvars x\<close>
  shows \<open>qrhl A [assign x e] [] B\<close>
proof -
  from dist_x have dist_x1: \<open>distinct_qvars x1\<close>
    by (simp add: x1 distinct_qvars_index)
  define A'' where \<open>A'' = subst_expression (substitute_vars x1 e1) B\<close>
  have A'_foot: \<open>expression_vars (A' z) = expression_vars (A' undefined)\<close> for z
    unfolding A' subst_expression_footprint subst_expression_footprint_substitute_vars_const by simp
  have e1'_foot: \<open>expression_vars (e1' z) = expression_vars (e1' undefined)\<close> for z
    unfolding e1' subst_expression_footprint subst_expression_footprint_substitute_vars_const by simp
  define x' where \<open>x' m = eval_variables x1 m\<close> for m
  have [simp]: \<open>subst_mem2 (substitute_vars x1 Expr[x' m]) m = m\<close> for m
    unfolding x'_def by (rule subst_mem2_eval_vars) 
  have \<open>expression_eval A m
    \<le> \<CC>\<ll>\<aa>[expression_eval (expression x1 (\<lambda>x. x)) (subst_mem2 (substitute_vars x1 e1) m) =
                   expression_eval (e1' (x' m)) (subst_mem2 (substitute_vars x1 e1) m)] \<sqinter>
               expression_eval (A' (x' m)) (subst_mem2 (substitute_vars x1 e1) m)\<close> for m
      by (auto simp add: expression_eval e1' subst_expression_eval subst_mem2_twice A' eval_var_subst_that_var dist_x1)
  also have \<open>\<dots>m \<le> (SUP z. \<CC>\<ll>\<aa>[expression_eval (expression x1 (\<lambda>x. x)) (subst_mem2 (substitute_vars x1 e1) m) =
                   expression_eval (e1' z) (subst_mem2 (substitute_vars x1 e1) m)] \<sqinter>
               expression_eval (A' z) (subst_mem2 (substitute_vars x1 e1) m))\<close> for m
    by (meson Sup_upper UNIV_I image_eqI)
  also have \<open>\<dots>m \<le> expression_eval (subst_expression (substitute_vars x1 e1) B) m\<close> for m
    unfolding subst_expression_eval B
    apply simp
    apply (subst expression_eval_map_expression3'')
    using A'_foot e1'_foot by auto
  also have \<open>\<dots>m = expression_eval A'' m\<close> for m
    by (simp add: A''_def)
  finally have \<open>A \<le> A''\<close>
    unfolding less_eq_expression_def le_fun_def by auto
  moreover have \<open>qrhl A'' [assign x e] [] B\<close>
    apply (rule wp1_assign_tac)
    by (auto simp: A''_def x1 e1)
  ultimately show ?thesis
    apply (rule_tac conseq_rule[where A'=A'' and B'=B])
    by auto
qed

lemma sp2_assign_tac:
  fixes A B x v
  assumes x2: "x2 = index_vars False x"
  assumes e2: \<open>e2 = index_expression False e\<close>
  assumes A': \<open>\<And>z. A' z = subst_expression (substitute_vars x2 (const_expression z)) A\<close>
  assumes e2': \<open>\<And>z. e2' z = subst_expression (substitute_vars x2 (const_expression z)) e2\<close>
  assumes B: \<open>B = map_expression3'' (\<lambda>x2' A' e2'. SUP z. A' z \<sqinter> Cla[x2' = e2' z]) (expression x2 (\<lambda>x. x)) A' e2'\<close>
  assumes dist_x: \<open>distinct_qvars x\<close>
  shows \<open>qrhl A [] [assign x e] B\<close>
proof -
  from dist_x have dist_x2: \<open>distinct_qvars x2\<close>
    by (simp add: x2 distinct_qvars_index)
  define A'' where \<open>A'' = subst_expression (substitute_vars x2 e2) B\<close>
  have A'_foot: \<open>expression_vars (A' z) = expression_vars (A' undefined)\<close> for z
    unfolding A' subst_expression_footprint subst_expression_footprint_substitute_vars_const by simp
  have e2'_foot: \<open>expression_vars (e2' z) = expression_vars (e2' undefined)\<close> for z
    unfolding e2' subst_expression_footprint subst_expression_footprint_substitute_vars_const by simp
  define x' where \<open>x' m = eval_variables x2 m\<close> for m
  have [simp]: \<open>subst_mem2 (substitute_vars x2 Expr[x' m]) m = m\<close> for m
    unfolding x'_def by (rule subst_mem2_eval_vars) 
  have \<open>expression_eval A m
    \<le> \<CC>\<ll>\<aa>[expression_eval (expression x2 (\<lambda>x. x)) (subst_mem2 (substitute_vars x2 e2) m) =
                   expression_eval (e2' (x' m)) (subst_mem2 (substitute_vars x2 e2) m)] \<sqinter>
               expression_eval (A' (x' m)) (subst_mem2 (substitute_vars x2 e2) m)\<close> for m
    by (auto simp add: expression_eval e2' subst_mem2_twice subst_expression_eval subst_mem2_eval_vars A' eval_var_subst_that_var dist_x2)
  also have \<open>\<dots>m \<le> (SUP z. \<CC>\<ll>\<aa>[expression_eval (expression x2 (\<lambda>x. x)) (subst_mem2 (substitute_vars x2 e2) m) =
                   expression_eval (e2' z) (subst_mem2 (substitute_vars x2 e2) m)] \<sqinter>
               expression_eval (A' z) (subst_mem2 (substitute_vars x2 e2) m))\<close> for m
    by (meson Sup_upper UNIV_I image_eqI)
  also have \<open>\<dots>m \<le> expression_eval (subst_expression (substitute_vars x2 e2) B) m\<close> for m
    unfolding subst_expression_eval B
    apply simp
    apply (subst expression_eval_map_expression3'')
    using A'_foot e2'_foot by auto
  also have \<open>\<dots>m = expression_eval A'' m\<close> for m
    by (simp add: A''_def)
  finally have \<open>A \<le> A''\<close>
    unfolding less_eq_expression_def le_fun_def by auto
  moreover have \<open>qrhl A'' [] [assign x e] B\<close>
    apply (rule wp2_assign_tac)
    by (auto simp: A''_def x2 e2)
  ultimately show ?thesis
    apply (rule_tac conseq_rule[where A'=A'' and B'=B])
    by auto
qed

definition true_expression where \<open>true_expression A \<longleftrightarrow> (\<forall>m. expression_eval A m)\<close>

lemma sp1_qinit_tac:
  fixes A B x v
  assumes Q1: "Q1 = index_vars True Q"
  assumes e1: \<open>e1 = index_expression True e\<close>
  assumes B: \<open>B = map_expression2 (\<lambda>A e. A \<sqinter> Q1 =\<^sub>q e) A e1\<close>
  assumes distinct_exp: \<open>D = map_expression (\<lambda>A. distinct_qvars_pred_vars A Q1) A\<close>
  assumes lossless_exp: \<open>L = map_expression2 (\<lambda>A e1. A \<le> Cla[norm e1 = 1]) A e1\<close>
  assumes distinct: \<open>true_expression D\<close>
  assumes lossless: \<open>true_expression L\<close>
  shows \<open>qrhl A [qinit Q e] [] B\<close>
proof -
  from distinct
  have [simp]: \<open>distinct_qvars_pred_vars (expression_eval A m) Q1\<close> for m
    by (simp add: distinct_exp true_expression_def)
  then have [simp]: \<open>distinct_qvars Q1\<close>
    using distinct unfolding distinct_qvars_pred_vars_def distinct_qvars_def
    apply transfer
    by auto
  from lossless
  have lossless: \<open>expression_eval A m \<le> Cla[norm (expression_eval e1 m) = 1]\<close> for m
    by (simp add: lossless_exp true_expression_def)
  have *: \<open>norm (expression_eval e1 m) \<noteq> 1 \<Longrightarrow> expression_eval A m \<le> \<bottom>\<close> for m
    using lossless[unfolded less_eq_expression_def le_fun_def, rule_format, of m]
    by simp
  have \<open>expression_eval A m \<le> expression_eval (map_expression2 (\<lambda>e\<^sub>1 B. \<CC>\<ll>\<aa>[norm e\<^sub>1 = 1] \<sqinter> B \<div> e\<^sub>1\<guillemotright>Q1) e1 B) m\<close> for m
    by (auto simp: B intro: inf.cobounded1 inf.cobounded2 *)
  then have *: \<open>A \<le> map_expression2 (\<lambda>e\<^sub>1 B. \<CC>\<ll>\<aa>[norm e\<^sub>1 = 1] \<sqinter> B \<div> e\<^sub>1\<guillemotright>Q1) e1 B\<close>
    by (simp add: less_eq_expression_def le_fun_def)
  show ?thesis
    using * apply (rule conseq_rule[where B'=B])
     apply rule
    apply (rule wp1_qinit_tac)
    using assms by auto
qed

lemma sp2_qinit_tac:
  fixes A B x v
  assumes Q2: "Q2 = index_vars False Q"
  assumes e2: \<open>e2 = index_expression False e\<close>
  assumes B: \<open>B = map_expression2 (\<lambda>A e. A \<sqinter> Q2 =\<^sub>q e) A e2\<close>
  assumes distinct_exp: \<open>D = map_expression (\<lambda>A. distinct_qvars_pred_vars A Q2) A\<close>
  assumes lossless_exp: \<open>L = map_expression2 (\<lambda>A e2. A \<le> Cla[norm e2 = 1]) A e2\<close>
  assumes distinct: \<open>true_expression D\<close>
  assumes lossless: \<open>true_expression L\<close>
  shows \<open>qrhl A [] [qinit Q e] B\<close>
proof -
  from distinct
  have [simp]: \<open>distinct_qvars_pred_vars (expression_eval A m) Q2\<close> for m
    by (simp add: distinct_exp true_expression_def)
  then have [simp]: \<open>distinct_qvars Q2\<close>
    using distinct unfolding distinct_qvars_pred_vars_def distinct_qvars_def
    apply transfer
    by auto
  from lossless
  have lossless: \<open>expression_eval A m \<le> Cla[norm (expression_eval e2 m) = 1]\<close> for m
    by (simp add: lossless_exp true_expression_def)
  have *: \<open>norm (expression_eval e2 m) \<noteq> 1 \<Longrightarrow> expression_eval A m \<le> \<bottom>\<close> for m
    using lossless[unfolded less_eq_expression_def le_fun_def, rule_format, of m]
    by simp
  have \<open>expression_eval A m \<le> expression_eval (map_expression2 (\<lambda>e\<^sub>2 B. \<CC>\<ll>\<aa>[norm e\<^sub>2 = 1] \<sqinter> B \<div> e\<^sub>2\<guillemotright>Q2) e2 B) m\<close> for m
    by (auto simp: B intro: inf.cobounded2 inf.cobounded2 *)
  then have *: \<open>A \<le> map_expression2 (\<lambda>e\<^sub>2 B. \<CC>\<ll>\<aa>[norm e\<^sub>2 = 1] \<sqinter> B \<div> e\<^sub>2\<guillemotright>Q2) e2 B\<close>
    by (simp add: less_eq_expression_def le_fun_def)
  show ?thesis
    using * apply (rule conseq_rule[where B'=B])
     apply rule
    apply (rule wp2_qinit_tac)
    using assms by auto
qed

lemma sp_split_left_right_tac:
  assumes "qrhl B c [] C"
    and "qrhl A [] d B"
  shows "qrhl A c d C"
  by (rule seqREMOVE[OF _ _ assms(2) assms(1)], simp_all)

ML_file "strongest_postcondition.ML"

end
