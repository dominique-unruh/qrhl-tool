theory Strongest_Postcondition
  imports Tactics Basic_Rules Weakest_Precondition
begin

(*
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

lemma expression_eval_map_expression3:
  shows "expression_eval (map_expression3 f e1 e2 e3) x = f (expression_eval e1 x) (expression_eval e2 x) (expression_eval e3 x)"
  unfolding map_expression3_def
  apply (subst expression_eval_map_expression)
  by (auto simp: pair_expression_footprint)

lemma expression_eval_map_expression2':
  assumes "\<And>z. expression_vars (e2 z) = expression_vars (e2 undefined)"
  shows "expression_eval (map_expression2' f e1 e2) x = f (expression_eval e1 x) (\<lambda>z. expression_eval (e2 z) x)"
  unfolding map_expression2'_def
  apply (subst expression_eval_map_expression')
  apply (auto simp: pair_expression_footprint)
  using assms by blast+

lemma subst_mem2_twice: \<open>subst_mem2 (substitute_vars x e) (subst_mem2 (substitute_vars x f) m) = subst_mem2 (substitute_vars x e) m\<close>

lemma subst_mem2_eval_vars: \<open>subst_mem2 (substitute_vars x1 Expr[eval_variables x1 m]) m = m\<close>

lemma subst_expression_footprint_substitute_vars_const: \<open>subst_expression_footprint (substitute_vars x Expr[z]) y = y - set (raw_variables x)\<close>

lemma eval_var_subst_that_var: \<open>eval_variables x (subst_mem2 (substitute_vars x e) m) = expression_eval e m\<close> if \<open>distinct_qvars x\<close>

lemma flatten_tree_index: \<open>flatten_tree (index_vartree side x) = map (index_var_raw side) (flatten_tree x)\<close>
  apply (induction x)
  by (auto simp: index_vartree_def)

lemma distinct_qvars_index: \<open>distinct_qvars (index_vars side x) \<longleftrightarrow> distinct_qvars x\<close>
  unfolding distinct_qvars_def
  apply (transfer fixing: side)
  by (auto simp: flatten_tree_index distinct_map index_var_raw_inject intro!: inj_onI)
*)

lemma sp1_assign_tac:
  fixes A B x v e
  assumes \<open>cregister x\<close>
  defines x1: "x1 \<equiv> cregister_chain cFst x"
  defines e1: \<open>e1 \<equiv> (\<lambda>m. e (fst m))\<close>
  defines A': \<open>\<And>z. A' z \<equiv> (\<lambda>m. A (setter x1 z m))\<close>
  defines e1': \<open>\<And>z. e1' z \<equiv> (\<lambda>m. e1 (setter x1 z m))\<close>
  defines B: \<open>B \<equiv> (\<lambda>m. SUP z. Cla[getter x1 m = e1' z m] \<sqinter> A' z m)\<close>
  shows \<open>qrhl A [assign x e] [] B\<close>
  sorry
(* proof -
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
qed *)

lemma sp2_assign_tac:
  fixes A B x v e
  assumes \<open>cregister x\<close>
  defines x2: "x2 \<equiv> cregister_chain cSnd x"
  defines e2: \<open>e2 \<equiv> (\<lambda>m. e (snd m))\<close>
  defines A': \<open>\<And>z. A' z \<equiv> (\<lambda>m. A (setter x2 z m))\<close>
  defines e2': \<open>\<And>z. e2' z \<equiv> (\<lambda>m. e2 (setter x2 z m))\<close>
  defines B: \<open>B \<equiv> (\<lambda>m. SUP z. Cla[getter x2 m = e2' z m] \<sqinter> A' z m)\<close>
  shows \<open>qrhl A [] [assign x e] B\<close>
  sorry
(* proof -
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
qed *)


definition true_expression where \<open>true_expression A \<longleftrightarrow> (\<forall>m. expression_eval A m)\<close>

lemma sp1_sample_tac:
  fixes A B x v e
  assumes \<open>cregister x\<close>
  defines x1: "x1 \<equiv> cregister_chain cFst x"
  defines e1: \<open>e1 \<equiv> (\<lambda>m. e (fst m))\<close>
  defines A': \<open>\<And>z. A' z \<equiv> (\<lambda>m. A (setter x1 z m))\<close>
  defines e1': \<open>\<And>z. e1' z \<equiv> (\<lambda>m. e1 (setter x1 z m))\<close>
  defines B: \<open>B \<equiv> (\<lambda>m. SUP z. Cla[getter x1 m \<in> supp (e1' z m)] \<sqinter> A' z m)\<close>
  defines lossless_exp: \<open>L \<equiv> (\<lambda>m. A m \<le> Cla[weight (e1 m) = 1])\<close>
  assumes lossless: \<open>true_expression L\<close>
  shows \<open>qrhl A [sample x e] [] B\<close>
  sorry
(* proof -
  from dist_x have dist_x1: \<open>distinct_qvars x1\<close>
    by (simp add: x1 distinct_qvars_index)
  define B' where "\<And>z. B' z = subst_expression (substitute_vars x1 (const_expression z)) B"
  define A'' where "A'' = map_expression2' (\<lambda>e1 B'. Cla[weight e1 = 1] \<sqinter> (INF z\<in>supp e1. B' z)) e1 B'"
  have B'_foot: \<open>expression_vars (B' z) = expression_vars (B' undefined)\<close> for z
  by (simp add: B'_def subst_expression_footprint subst_expression_footprint_substitute_vars_const)
  have A'_foot: \<open>expression_vars (A' z) = expression_vars (A' undefined)\<close> for z
    unfolding A' subst_expression_footprint subst_expression_footprint_substitute_vars_const by simp
  have e1'_foot: \<open>expression_vars (e1' z) = expression_vars (e1' undefined)\<close> for z
    unfolding e1' subst_expression_footprint subst_expression_footprint_substitute_vars_const by simp
  from lossless
  have lossless: \<open>expression_eval A m \<le> Cla[weight (expression_eval e1 m) = 1]\<close> for m
    by (simp add: lossless_exp true_expression_def)
  have *: \<open>expression_eval A m
       \<le> (SUP z'.
              \<CC>\<ll>\<aa>[z \<in> supp (expression_eval e1 (subst_mem2 (substitute_vars x1 Expr[z']) m))] \<sqinter>
              expression_eval A (subst_mem2 (substitute_vars x1 Expr[z']) m))\<close> 
    if \<open>z\<in>supp (expression_eval e1 m)\<close> for z m
    apply (rule SUP_upper2[where i=\<open>eval_variables x1 m\<close>])
     apply simp
    by (simp add: that subst_mem2_eval_vars)
  have \<open>expression_eval A m \<le> expression_eval A'' m\<close> if \<open>weight (expression_eval e1 m) = 1\<close> for m
    using B'_foot apply (simp add: A''_def expression_eval_map_expression2' that B'_def
        subst_expression_eval)
    apply (thin_tac \<open>PROP _\<close>)
    using e1'_foot A'_foot apply (simp add: B expression_eval_map_expression3'')
    apply (thin_tac \<open>PROP _\<close>)
    apply (thin_tac \<open>PROP _\<close>)
    by (simp add: A' expression_eval subst_expression_eval subst_mem2_twice
        * dist_x1 eval_var_subst_that_var e1')
  moreover have \<open>expression_eval A m \<le> expression_eval A'' m\<close> if \<open>weight (expression_eval e1 m) \<noteq> 1\<close> for m
    using lossless[of m] by (simp add: that bot.extremum_unique)
  ultimately have \<open>A \<le> A''\<close>
    unfolding less_eq_expression_def le_fun_def by auto
  moreover have \<open>qrhl A'' [sample x e] [] B\<close>
    apply (rule wp1_sample_tac)
    by (auto simp: B'_def A''_def x1 e1)
  ultimately show ?thesis
    apply (rule_tac conseq_rule[where A'=A'' and B'=B])
    by auto
qed *)


lemma sp2_sample_tac:
  fixes A B x v e
  assumes \<open>cregister x\<close>
  defines x2: "x2 \<equiv> cregister_chain cSnd x"
  defines e2: \<open>e2 \<equiv> (\<lambda>m. e (snd m))\<close>
  defines A': \<open>\<And>z. A' z \<equiv> (\<lambda>m. A (setter x2 z m))\<close>
  defines e2': \<open>\<And>z. e2' z \<equiv> (\<lambda>m. e2 (setter x2 z m))\<close>
  defines B: \<open>B \<equiv> (\<lambda>m. SUP z. Cla[getter x2 m \<in> supp (e2' z m)] \<sqinter> A' z m)\<close>
  defines lossless_exp: \<open>L \<equiv> (\<lambda>m. A m \<le> Cla[weight (e2 m) = 2])\<close>
  assumes lossless: \<open>true_expression L\<close>
  shows \<open>qrhl A [] [sample x e] B\<close>
  sorry
(* proof -
  from dist_x have dist_x2: \<open>distinct_qvars x2\<close>
    by (simp add: x2 distinct_qvars_index)
  define B' where "\<And>z. B' z = subst_expression (substitute_vars x2 (const_expression z)) B"
  define A'' where "A'' = map_expression2' (\<lambda>e2 B'. Cla[weight e2 = 1] \<sqinter> (INF z\<in>supp e2. B' z)) e2 B'"
  have B'_foot: \<open>expression_vars (B' z) = expression_vars (B' undefined)\<close> for z
  by (simp add: B'_def subst_expression_footprint subst_expression_footprint_substitute_vars_const)
  have A'_foot: \<open>expression_vars (A' z) = expression_vars (A' undefined)\<close> for z
    unfolding A' subst_expression_footprint subst_expression_footprint_substitute_vars_const by simp
  have e2'_foot: \<open>expression_vars (e2' z) = expression_vars (e2' undefined)\<close> for z
    unfolding e2' subst_expression_footprint subst_expression_footprint_substitute_vars_const by simp
  from lossless
  have lossless: \<open>expression_eval A m \<le> Cla[weight (expression_eval e2 m) = 1]\<close> for m
    by (simp add: lossless_exp true_expression_def)
  have *: \<open>expression_eval A m
       \<le> (SUP z'.
              \<CC>\<ll>\<aa>[z \<in> supp (expression_eval e2 (subst_mem2 (substitute_vars x2 Expr[z']) m))] \<sqinter>
              expression_eval A (subst_mem2 (substitute_vars x2 Expr[z']) m))\<close> 
    if \<open>z\<in>supp (expression_eval e2 m)\<close> for z m
    apply (rule SUP_upper2[where i=\<open>eval_variables x2 m\<close>])
     apply simp
    by (simp add: that subst_mem2_eval_vars)
  have \<open>expression_eval A m \<le> expression_eval A'' m\<close> if \<open>weight (expression_eval e2 m) = 1\<close> for m
    using B'_foot apply (simp add: A''_def expression_eval_map_expression2' that B'_def
        subst_expression_eval)
    apply (thin_tac \<open>PROP _\<close>)
    using e2'_foot A'_foot apply (simp add: B expression_eval_map_expression3'')
    apply (thin_tac \<open>PROP _\<close>)
    apply (thin_tac \<open>PROP _\<close>)
    by (simp add: A' expression_eval subst_expression_eval subst_mem2_twice
        * dist_x2 eval_var_subst_that_var e2')
  moreover have \<open>expression_eval A m \<le> expression_eval A'' m\<close> if \<open>weight (expression_eval e2 m) \<noteq> 1\<close> for m
    using lossless[of m] by (simp add: that bot.extremum_unique)
  ultimately have \<open>A \<le> A''\<close>
    unfolding less_eq_expression_def le_fun_def by auto
  moreover have \<open>qrhl A'' [] [sample x e] B\<close>
    apply (rule wp2_sample_tac)
    by (auto simp: B'_def A''_def x2 e2)
  ultimately show ?thesis
    apply (rule_tac conseq_rule[where A'=A'' and B'=B])
    by auto
qed *)

lemma sp1_qinit_tac:
  fixes A B x v e
  assumes \<open>qregister Q\<close>
  defines Q1: "Q1 \<equiv> qregister_chain qFst Q"
  defines e1: \<open>e1 \<equiv> (\<lambda>m. e (fst m))\<close>
  defines B: \<open>B \<equiv> (\<lambda>m. A m \<sqinter> Q1 =\<^sub>q e1 m)\<close>
  defines distinct_exp: \<open>D \<equiv> (\<lambda>m. distinct_qvars_pred_vars (A m) Q1)\<close>
  defines lossless_exp: \<open>L \<equiv> (\<lambda>m. A m \<le> Cla[norm (e1 m) = 1])\<close>
  assumes distinct: \<open>true_expression D\<close>
  assumes lossless: \<open>true_expression L\<close>
  shows \<open>qrhl A [qinit Q e] [] B\<close>
  sorry
(* proof -
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
    by (auto simp: B intro: inf.cobounded1 inf.cobounded2 * )
  then have *: \<open>A \<le> map_expression2 (\<lambda>e\<^sub>1 B. \<CC>\<ll>\<aa>[norm e\<^sub>1 = 1] \<sqinter> B \<div> e\<^sub>1\<guillemotright>Q1) e1 B\<close>
    by (simp add: less_eq_expression_def le_fun_def)
  show ?thesis
    using * apply (rule conseq_rule[where B'=B])
     apply rule
    apply (rule wp1_qinit_tac)
    using assms by auto
qed *)

lemma sp2_qinit_tac:
  fixes A B x v e
  assumes \<open>qregister Q\<close>
  defines Q2: "Q2 \<equiv> qregister_chain qSnd Q"
  defines e2: \<open>e2 \<equiv> (\<lambda>m. e (snd m))\<close>
  defines B: \<open>B \<equiv> (\<lambda>m. A m \<sqinter> Q2 =\<^sub>q e2 m)\<close>
  defines distinct_exp: \<open>D \<equiv> (\<lambda>m. distinct_qvars_pred_vars (A m) Q2)\<close>
  defines lossless_exp: \<open>L \<equiv> (\<lambda>m. A m \<le> Cla[norm (e2 m) = 2])\<close>
  assumes distinct: \<open>true_expression D\<close>
  assumes lossless: \<open>true_expression L\<close>
  shows \<open>qrhl A [] [qinit Q e] B\<close>
    sorry
(* proof -
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
    by (auto simp: B intro: inf.cobounded2 inf.cobounded2 * )
  then have *: \<open>A \<le> map_expression2 (\<lambda>e\<^sub>2 B. \<CC>\<ll>\<aa>[norm e\<^sub>2 = 1] \<sqinter> B \<div> e\<^sub>2\<guillemotright>Q2) e2 B\<close>
    by (simp add: less_eq_expression_def le_fun_def)
  show ?thesis
    using * apply (rule conseq_rule[where B'=B])
     apply rule
    apply (rule wp2_qinit_tac)
    using assms by auto
qed *)

lemma sp1_measure_tac:
  fixes x Q e A
  assumes \<open>cregister x\<close> \<open>qregister Q\<close>
  defines x1: "x1 \<equiv> cregister_chain cFst x"
  defines Q1: "Q1 \<equiv> qregister_chain qFst Q"
  defines e1: \<open>e1 \<equiv> (\<lambda>m. e (fst m))\<close>
  defines A': \<open>\<And>z. A' z \<equiv> (\<lambda>m. A (setter x1 z m))\<close>
  defines e1': \<open>\<And>z. e1' z \<equiv> (\<lambda>m. e1 (setter x1 z m))\<close>
  defines B: \<open>B \<equiv> (\<lambda>m. SUP z r. Cla[getter x1 m = r] \<sqinter> ((mproj (e1' z m) r \<guillemotright> Q1) *\<^sub>S A' z m))\<close>
  defines lossless_exp: \<open>L \<equiv> (\<lambda>m. A m \<le> Cla[mtotal (e1 m)])\<close>
  assumes lossless: \<open>true_expression L\<close>
  shows "qrhl A [measurement x Q e] [] B"
(* Handwritten proof: Quicksheets 2022, pages 150-151. *)
  sorry
(* proof -
  define B' where \<open>B' z = subst_expression (substitute_vars x1 Expr[z]) B\<close> for z
  define A'' where \<open>A'' = map_expression2' (\<lambda>e\<^sub>1 B'. let M = e\<^sub>1 in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (INF z. let P = mproj M z\<guillemotright>Q1 *\<^sub>S \<top> in B' z \<sqinter> P + - P)) e1 B'\<close>
  have foot_B': \<open>expression_vars (B' z) = expression_vars (B' undefined)\<close> for z
    by -
  have foot_e1: \<open>expression_vars (e1' z) = expression_vars (e1' undefined)\<close> for z
    by -
  have foot_A': \<open>expression_vars (A' z) = expression_vars (A' undefined)\<close> for z
    by -
  have \<open>expression_eval A'' m = xxx\<close> for m
    using foot_B' apply (simp add: A''_def expression_eval_map_expression2')
    apply (thin_tac \<open>PROP _\<close>)
    using foot_e1 foot_A' apply (simp add: B'_def B subst_expression_eval expression_eval_map_expression3'')
    apply (thin_tac \<open>PROP _\<close>)
    apply (thin_tac \<open>PROP _\<close>)
    apply (subst expression_eval_map_expression3'')
  have \<open>A \<le> A''\<close>
    by -
  then show ?thesis
    apply (rule conseq_rule[where B'=B])
     apply rule
    apply (rule wp1_measure_tac)
    using assms B'_def A''_def by auto
qed *)

lemma sp2_measure_tac:
  fixes x Q e A
  assumes \<open>cregister x\<close> \<open>qregister Q\<close>
  defines x2: "x2 \<equiv> cregister_chain cSnd x"
  defines Q2: "Q2 \<equiv> qregister_chain qSnd Q"
  defines e2: \<open>e2 \<equiv> (\<lambda>m. e (snd m))\<close>
  defines A': \<open>\<And>z. A' z \<equiv> (\<lambda>m. A (setter x2 z m))\<close>
  defines e2': \<open>\<And>z. e2' z \<equiv> (\<lambda>m. e2 (setter x2 z m))\<close>
  defines B: \<open>B \<equiv> (\<lambda>m. SUP z r. Cla[getter x2 m = r] \<sqinter> ((mproj (e2' z m) r \<guillemotright> Q2) *\<^sub>S A' z m))\<close>
  defines lossless_exp: \<open>L \<equiv> (\<lambda>m. A m \<le> Cla[mtotal (e2 m)])\<close>
  assumes lossless: \<open>true_expression L\<close>
  shows "qrhl A [] [measurement x Q e] B"
  sorry

lemma sp1_cons_tac:
  assumes "qrhl A' ps [] B"
  assumes "qrhl A [p] [] A'"
  shows "qrhl A (p#ps) [] B"
  using assms seqREMOVE by fastforce

lemma sp2_cons_tac:
  assumes "qrhl A' [] ps B"
  assumes "qrhl A [] [p] A'"
  shows "qrhl A [] (p#ps) B"
  using assms seqREMOVE by fastforce

lemma sp_split_left_right_tac:
  assumes "qrhl B c [] C"
    and "qrhl A [] d B"
  shows "qrhl A c d C"
  by (rule seqREMOVE[OF _ _ assms(2) assms(1)], simp_all)

lemma sp1_block_tac:
  assumes "qrhl A p [] B"
  shows "qrhl A [block p] [] B"
  by (simp add: assms wp1_block_tac)

lemma sp2_block_tac:
  assumes "qrhl A [] p B"
  shows "qrhl A [] [block p] B"
  by (simp add: assms wp2_block_tac)

lemma sp1_if_tac:
  fixes B_true B_false e A
  defines B: \<open>B \<equiv> (\<lambda>m. B_true m \<squnion> B_false m)\<close>
  defines e1: \<open>e1 \<equiv> (\<lambda>m. e (fst m))\<close>
  defines A_false: \<open>A_false \<equiv> (\<lambda>m. Cla[\<not> e1 m] \<sqinter> A m)\<close>
  defines A_true: \<open>A_true \<equiv> (\<lambda>m. Cla[e1 m] \<sqinter> A m)\<close>
  assumes wp_false: \<open>qrhl A_false p2 [] B_false\<close>
  assumes wp_true: \<open>qrhl A_true p1 [] B_true\<close>
  shows \<open>qrhl A [ifthenelse e p1 p2] [] B\<close>
  sorry
(* proof -
  have \<open>B \<ge> B_true\<close>
    by (auto simp: less_eq_expression_def le_fun_def B)
  with wp_true have wp_true': \<open>qrhl A_true p1 [] B\<close>
    using conseq_rule by blast
  have \<open>B \<ge> B_false\<close>
    by (auto simp: less_eq_expression_def le_fun_def B)
  with wp_false have wp_false': \<open>qrhl A_false p2 [] B\<close>
    using conseq_rule by blast
  define A' where \<open>A' = map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (\<CC>\<ll>\<aa>[\<not> e\<^sub>1] + wp_true) \<sqinter> (\<CC>\<ll>\<aa>[e\<^sub>1] + wp_false)) e1 A_true A_false\<close>
  have \<open>qrhl A' [ifthenelse e p1 p2] [] B\<close>
    using e1 wp_true' wp_false' A'_def 
    by (rule wp1_if_tac)
  moreover have \<open>A' \<ge> A\<close>
    by (auto simp add: less_eq_expression_def le_fun_def A'_def expression_eval_map_expression3 A_true A_false)
  ultimately show ?thesis
    using conseq_rule by blast
qed *)

lemma sp2_if_tac:
  fixes B_true B_false e A
  defines B: \<open>B \<equiv> (\<lambda>m. B_true m \<squnion> B_false m)\<close>
  defines e2: \<open>e2 \<equiv> (\<lambda>m. e (snd m))\<close>
  defines A_false: \<open>A_false \<equiv> (\<lambda>m. Cla[\<not> e2 m] \<sqinter> A m)\<close>
  defines A_true: \<open>A_true \<equiv> (\<lambda>m. Cla[e2 m] \<sqinter> A m)\<close>
  assumes wp_false: \<open>qrhl A_false [] p2 B_false\<close>
  assumes wp_true: \<open>qrhl A_true [] p2 B_true\<close>
  shows \<open>qrhl A [] [ifthenelse e p2 p2] B\<close>
    sorry
(* proof -
  have \<open>B \<ge> B_true\<close>
    by (auto simp: less_eq_expression_def le_fun_def B)
  with wp_true have wp_true': \<open>qrhl A_true [] p1 B\<close>
    using conseq_rule by blast
  have \<open>B \<ge> B_false\<close>
    by (auto simp: less_eq_expression_def le_fun_def B)
  with wp_false have wp_false': \<open>qrhl A_false [] p2 B\<close>
    using conseq_rule by blast
  define A' where \<open>A' = map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (\<CC>\<ll>\<aa>[\<not> e\<^sub>1] + wp_true) \<sqinter> (\<CC>\<ll>\<aa>[e\<^sub>1] + wp_false)) e2 A_true A_false\<close>
  have \<open>qrhl A' [] [ifthenelse e p1 p2] B\<close>
    using e2 wp_true' wp_false' A'_def 
    by (rule wp2_if_tac)
  moreover have \<open>A' \<ge> A\<close>
    by (auto simp add: less_eq_expression_def le_fun_def A'_def expression_eval_map_expression3 A_true A_false)
  ultimately show ?thesis
    using conseq_rule by blast
qed *)


lemma sp1_qapply_tac:
  fixes A e Q
  assumes \<open>qregister Q\<close>
  defines Q1: "Q1 \<equiv> qregister_chain qFst Q"
  defines e1: \<open>e1 \<equiv> (\<lambda>m. e (fst m))\<close>
  defines B: \<open>B \<equiv> (\<lambda>m. (e1 m \<guillemotright> Q1) *\<^sub>S A m)\<close>
  defines lossless_exp: \<open>L \<equiv> (\<lambda>m. A m \<le> Cla[unitary (e1 m)])\<close> (* unitary can probably be weakened to isometry using a different proof *)
  assumes lossless: \<open>true_expression L\<close>
  shows "qrhl A [qapply Q e] [] B"
  sorry
(* proof -
  from distinct have dist_Q1[simp]: \<open>distinct_qvars Q1\<close>
    by (simp add: Q1 distinct_qvars_index)
  define A' where \<open>A' = map_expression2 (\<lambda>e\<^sub>1 B. \<CC>\<ll>\<aa>[isometry e\<^sub>1] \<sqinter> ((e\<^sub>1\<guillemotright>Q1)* *\<^sub>S (B \<sqinter> (e\<^sub>1\<guillemotright>Q1 *\<^sub>S \<top>)))) e1 B\<close>

  have \<open>qrhl A' [qapply Q e] [] B\<close>
    using Q1 e1 A'_def apply (rule wp1_qapply_tac)
    by -
  moreover 
  have \<open>A \<le> A'\<close>
  proof (unfold less_eq_expression_def le_fun_def, rule allI)
    fix m
    let ?A = \<open>expression_eval A m\<close>
    let ?e1 = \<open>expression_eval e1 m\<close>
    let ?A' = \<open>expression_eval A' m\<close>
    from lossless
    have \<open>?A \<le> ?A \<sqinter> Cla[unitary ?e1]\<close>
      by (simp add: lossless_exp true_expression_def)
    also have \<open>?A \<sqinter> Cla[unitary ?e1] \<le> ?A'\<close>
      by (auto simp add: A'_def B expression_eval_map_expression3
          simp flip: cblinfun_compose_image adjoint_lift)
    finally show \<open>?A \<le> ?A'\<close>
      by -
  qed
  ultimately show ?thesis
    using conseq_rule by blast
qed *)

lemma sp2_qapply_tac:
  fixes A e Q
  assumes \<open>qregister Q\<close>
  defines Q2: "Q2 \<equiv> qregister_chain qSnd Q"
  defines e2: \<open>e2 \<equiv> (\<lambda>m. e (snd m))\<close>
  defines B: \<open>B \<equiv> (\<lambda>m. (e2 m \<guillemotright> Q2) *\<^sub>S A m)\<close>
  assumes lossless_exp: \<open>L = (\<lambda>m. A m \<le> Cla[unitary (e2 m)])\<close> (* unitary can probably be weakened to isometry using a different proof *)
  assumes lossless: \<open>true_expression L\<close>
  shows "qrhl A [] [qapply Q e] B"
    sorry
(* proof -
  from distinct have dist_Q2[simp]: \<open>distinct_qvars Q2\<close>
    by (simp add: Q2 distinct_qvars_index)
  define A' where \<open>A' = map_expression2 (\<lambda>e\<^sub>2 B. \<CC>\<ll>\<aa>[isometry e\<^sub>2] \<sqinter> ((e\<^sub>2\<guillemotright>Q2)* *\<^sub>S (B \<sqinter> (e\<^sub>2\<guillemotright>Q2 *\<^sub>S \<top>)))) e2 B\<close>

  have \<open>qrhl A' [] [qapply Q e] B\<close>
    using Q2 e2 A'_def apply (rule wp2_qapply_tac)
    by -
  moreover 
  have \<open>A \<le> A'\<close>
  proof (unfold less_eq_expression_def le_fun_def, rule allI)
    fix m
    let ?A = \<open>expression_eval A m\<close>
    let ?e2 = \<open>expression_eval e2 m\<close>
    let ?A' = \<open>expression_eval A' m\<close>
    from lossless
    have \<open>?A \<le> ?A \<sqinter> Cla[unitary ?e2]\<close>
      by (simp add: lossless_exp true_expression_def)
    also have \<open>?A \<sqinter> Cla[unitary ?e2] \<le> ?A'\<close>
      by (auto simp add: A'_def B expression_eval_map_expression3
          simp flip: cblinfun_compose_image adjoint_lift)
    finally show \<open>?A \<le> ?A'\<close>
      by -
  qed
  ultimately show ?thesis
    using conseq_rule by blast
qed *)

ML_file "strongest_postcondition.ML"

end
