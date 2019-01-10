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

lemma substitution1_variable_index_flip: "substitution1_variable (index_flip_substitute1 s) = 
  index_flip_var_raw (substitution1_variable s)"
  apply transfer by auto

lemma substitution1_function_index_flip: "substitution1_function (index_flip_substitute1 s) = 
  substitution1_function s \<circ> index_flip_mem2"
  apply (cases "Rep_substitution1 s")
  by (simp add: substitution1_function.rep_eq index_flip_substitute1.rep_eq)

lemma index_flip_var_raw_substitution1_footprint: "index_flip_var_raw ` substitution1_footprint s =
  substitution1_footprint (index_flip_substitute1 s)"
  sorry

lemma index_flip_substitute1_twice[simp]: "index_flip_substitute1 (index_flip_substitute1 s) = s"
  apply transfer by (auto simp: image_iff)

lemma Ex_substitute: "(\<exists>s. P s) \<longleftrightarrow> (\<exists>s. P (f s))" if "surj f" for f::"'x\<Rightarrow>'y" and P
  using that by (metis UNIV_I bex_imageD)

lemma map_option_Some_eq: "map_option f e = Some (f y) \<longleftrightarrow> e = Some y" if "inj f"
  by (simp add: inj_eq that)

lemma tmpREMOVE: "a b c \<Longrightarrow> Transfer.Rel a b c" unfolding Transfer.Rel_def by simp

lemma left_unique_rel_mem2[transfer_rule]: assumes "left_total R" shows "left_unique (rel_mem2 R)"
proof -
  have left_unique_fun: "left_unique (rel_fun R ((=)))"
    apply (rule left_unique_fun)
    using assms left_unique_eq by auto
  have "m=m'" if "rel_mem2 R m m2" and "rel_mem2 R m' m2" for m m' m2
  proof -
    from that have "rel_fun R (=) (Rep_mem2 m) (Rep_mem2 m2)" by (simp add: rel_mem2.rep_eq)
    moreover from that have "rel_fun R (=) (Rep_mem2 m') (Rep_mem2 m2)" by (simp add: rel_mem2.rep_eq)
    ultimately have "Rep_mem2 m = Rep_mem2 m'"
      by (rule left_unique_fun[unfolded left_unique_def, rule_format])
    then show "m = m'"
      using Rep_mem2_inject by auto 
  qed
  then show ?thesis
    by (simp add: left_uniqueI)
qed

lemma rel_mem2_flip[simp]: "(rel_mem2 x)^--1 = (rel_mem2 x^--1)"
    apply (rule ext)+ unfolding conversep_iff apply transfer
    by (auto simp: rel_fun_def)

lemma right_unique_rel_mem2[transfer_rule]: assumes "right_total R" shows "right_unique (rel_mem2 R)"
  apply (subst conversep_conversep[of R, symmetric])
  apply (subst rel_mem2_flip[symmetric])
  apply (simp del: rel_mem2_flip)
  apply (rule left_unique_rel_mem2)
  using assms by simp

lemma bi_unique_rel_mem2[transfer_rule]: assumes "bi_total R" shows "bi_unique (rel_mem2 R)"
  using assms bi_total_alt_def bi_unique_alt_def left_unique_rel_mem2 right_unique_rel_mem2 by blast

definition "type_preserving_var_rel R \<longleftrightarrow> (\<forall>v w. R v w \<longrightarrow> variable_raw_domain v = variable_raw_domain w)"

lemma left_total_rel_mem2[transfer_rule]: 
  assumes "left_unique R" and "right_total R" and "type_preserving_var_rel R"
  shows "left_total (rel_mem2 R)"
proof -
  have "\<exists>m2. rel_mem2 R m1 m2" for m1
  proof (transfer fixing: R, auto)
    fix m1 
    assume m1v: "\<forall>v. m1 v \<in> variable_raw_domain v"
    have left_total_fun: "left_total (rel_fun R (=))"
      apply (rule left_total_fun)
      using \<open>left_unique R\<close> by (auto simp: left_total_eq)
    then obtain m2 where m2: "rel_fun R (=) m1 m2" 
      using left_totalE by auto
    have m2v: "m2 v \<in> variable_raw_domain v" for v
    proof -
      obtain w where "R w v"
        apply atomize_elim using \<open>right_total R\<close> unfolding right_total_def by simp
      with m2 have m1m2: "m1 w = m2 v"
        by (rule rel_funD)
      from \<open>R w v\<close> \<open>type_preserving_var_rel R\<close> have "variable_raw_domain v = variable_raw_domain w"
        unfolding type_preserving_var_rel_def by simp
      with m1v[rule_format, of w] m1m2 
      show ?thesis by auto
    qed
    from m2 m2v 
    show "\<exists>x. (\<forall>v. x v \<in> variable_raw_domain v) \<and> rel_fun R (=) m1 x"
      by auto
  qed
  then show ?thesis
    by (rule left_totalI)
qed

lemma type_preserving_var_rel_flip[simp]: "type_preserving_var_rel R\<inverse>\<inverse> \<longleftrightarrow> type_preserving_var_rel R"
  unfolding type_preserving_var_rel_def by auto

lemma right_total_rel_mem2[transfer_rule]: 
  assumes "right_unique R" and "left_total R" and "type_preserving_var_rel R"
  shows "right_total (rel_mem2 R)"
  apply (subst conversep_conversep[of R, symmetric])
  apply (subst rel_mem2_flip[symmetric])
  apply (simp del: rel_mem2_flip)
  apply (rule left_total_rel_mem2)
  using assms by auto

lemma bi_total_rel_mem2[transfer_rule]: 
  assumes "bi_unique R" and "bi_total R" and "type_preserving_var_rel R"
  shows "bi_total (rel_mem2 R)"
  by (meson assms bi_total_alt_def bi_unique_alt_def left_total_rel_mem2 right_total_rel_mem2)


lemma left_unique_rel_expression[transfer_rule]:
  assumes "left_unique R" and "left_unique S" and "right_total R" and "type_preserving_var_rel R"
  shows "left_unique (rel_expression R S)"
proof -
  have "e = f" if "rel_expression R S e g" and "rel_expression R S f g" for e f g
  proof -
    obtain vse E where e: "Rep_expression e = (vse,E)" by (atomize_elim, auto)
    obtain vsf F where f: "Rep_expression f = (vsf,F)" by (atomize_elim, auto)
    obtain vsg G where g: "Rep_expression g = (vsg,G)" by (atomize_elim, auto)
    from that have "rel_prod (rel_set R) (rel_fun (rel_mem2 R) S) (vse,E) (vsg,G)"
      unfolding rel_expression.rep_eq e g by simp
    then have vseg: "rel_set R vse vsg" and EG: "(rel_fun (rel_mem2 R) S) E G" by auto

    from that have "rel_prod (rel_set R) (rel_fun (rel_mem2 R) S) (vsf,F) (vsg,G)"
      unfolding rel_expression.rep_eq f g by simp
    then have vsfg: "rel_set R vsf vsg" and FG: "(rel_fun (rel_mem2 R) S) F G" by auto

    from vseg vsfg have "vse = vsf"
      using \<open>left_unique R\<close>
      by (meson left_uniqueD left_unique_rel_set) 

    have left_unique_fun: "left_unique (rel_fun (rel_mem2 R) S)"
      apply (rule left_unique_fun)
       apply (rule left_total_rel_mem2)
      using assms by auto
    from EG FG have "E = F"
      using left_unique_fun
      by (meson left_uniqueD)

    from \<open>vse = vsf\<close> \<open>E = F\<close>
    show "e = f"
      using Rep_expression_inject e f by fastforce
    qed
  then show ?thesis
    unfolding left_unique_def by simp
qed

lemma rel_expression_flip[simp]: "(rel_expression R S)^--1 = rel_expression R^--1 S^--1"
  apply (rule ext)+ unfolding conversep_iff apply transfer
  using rel_mem2_flip[unfolded conversep_iff]
  apply (auto simp: rel_fun_def rel_set_def)
  by (metis (full_types))+

lemma right_unique_rel_expression[transfer_rule]:
  assumes "right_unique R" and "right_unique S" and "left_total R" and "type_preserving_var_rel R"
  shows "right_unique (rel_expression R S)"
  apply (subst conversep_conversep[of R, symmetric])
  apply (subst conversep_conversep[of S, symmetric])
  apply (subst rel_expression_flip[symmetric])
  apply (simp del: rel_expression_flip)
  apply (rule left_unique_rel_expression)
  using assms by auto

lemma bi_unique_rel_expression[transfer_rule]:
  assumes "bi_unique R" and "bi_unique S" and "bi_total R" and "type_preserving_var_rel R"
  shows "bi_unique (rel_expression R S)"
  using assms by (meson bi_total_alt_def bi_unique_alt_def left_unique_rel_expression right_unique_rel_expression)

lemma rel_substitute1_flip[simp]: "(rel_substitute1 R S)^--1 = rel_substitute1 R^--1 S^--1"
  apply (rule ext)+ unfolding conversep_iff apply transfer by auto

lemma left_unique_rel_substitute1[transfer_rule]: 
  assumes "left_unique R"
  assumes "left_unique S"
  shows "left_unique (rel_substitute1 R S)"
proof -
  have "s1 = s2" if "rel_substitute1 R S s1 t" and "rel_substitute1 R S s2 t" for s1 s2 t
  proof -
    obtain xs1 vss1 es1 where s1: "Rep_substitution1 s1 = (xs1,vss1,es1)" by (meson prod_cases3)
    then have "finite vss1" and foot1: "(\<forall>w\<in>vss1. Rep_mem2 m1 w = Rep_mem2 m2 w) \<longrightarrow> es1 m1 = es1 m2" for m1 m2
      using Rep_substitution1[of s1] by auto
    obtain xs2 vss2 es2 where s2: "Rep_substitution1 s2 = (xs2,vss2,es2)" by (meson prod_cases3)
    then have "finite vss2" and foot2: "(\<forall>w\<in>vss2. Rep_mem2 m1 w = Rep_mem2 m2 w) \<longrightarrow> es2 m1 = es2 m2" for m1 m2
      using Rep_substitution1[of s2] by auto
    obtain xt vst et where t: "Rep_substitution1 t = (xt,vst,et)" by (meson prod_cases3)

    from that have "rel_prod R
     (\<lambda>(vss1, es1) (vst, et).
         range es1 \<subseteq> range EMBEDDING('a) \<and>
         range et \<subseteq> range EMBEDDING('b) \<and>
         S (Abs_expression (vss1, inv EMBEDDING('a) \<circ> es1)) (Abs_expression (vst, inv EMBEDDING('b) \<circ> et)))
     (xs1, vss1, es1) (xt, vst, et)"
      unfolding rel_substitute1.rep_eq s1 t by simp
    then have R1: "R xs1 xt" and range_es1: "range es1 \<subseteq> range EMBEDDING('a)" and "range et \<subseteq> range EMBEDDING('b)" 
      and S1: "S (Abs_expression (vss1, inv EMBEDDING('a) \<circ> es1)) (Abs_expression (vst, inv EMBEDDING('b) \<circ> et))"
      by auto

    from that have "rel_prod R
     (\<lambda>(vss2, es2) (vst, et).
         range es2 \<subseteq> range EMBEDDING('a) \<and>
         range et \<subseteq> range EMBEDDING('b) \<and>
         S (Abs_expression (vss2, inv EMBEDDING('a) \<circ> es2)) (Abs_expression (vst, inv EMBEDDING('b) \<circ> et)))
     (xs2, vss2, es2) (xt, vst, et)"
      unfolding rel_substitute1.rep_eq s2 t by simp
    then have R2: "R xs2 xt" and range_es2: "range es2 \<subseteq> range EMBEDDING('a)" and "range et \<subseteq> range EMBEDDING('b)" 
      and S2: "S (Abs_expression (vss2, inv EMBEDDING('a) \<circ> es2)) (Abs_expression (vst, inv EMBEDDING('b) \<circ> et))"
      by auto

    from R1 R2 have "xs1 = xs2"
      using \<open>left_unique R\<close>
      by (meson left_uniqueD)

    from S1 S2 have AbsS: "Abs_expression (vss1, inv EMBEDDING('a) \<circ> es1) = Abs_expression (vss2, inv EMBEDDING('a) \<circ> es2)"
      using \<open>left_unique S\<close>
      by (meson left_uniqueD)
    have "(vss1, inv EMBEDDING('a) \<circ> es1) = (vss2, inv EMBEDDING('a) \<circ> es2)"
      apply (rule Abs_expression_inject[THEN iffD1, OF _ _ AbsS])
      using foot1 foot2 \<open>finite vss1\<close> \<open>finite vss2\<close> by force+
    then have "vss1 = vss2" and inv: "inv EMBEDDING('a) o es1 = inv EMBEDDING('a) o es2" by auto
    with range_es1 range_es2 have "es1 = es2"
      by (smt fun.inj_map_strong inv_into_injective subsetCE) 

    from \<open>xs1 = xs2\<close> and \<open>vss1 = vss2\<close> and \<open>es1 = es2\<close>
    show "s1 = s2"
      using Rep_substitution1_inject s1 s2 by fastforce
    qed
  then show ?thesis
    unfolding left_unique_def by simp
qed

lemma right_unique_rel_substitute1[transfer_rule]:
  assumes "right_unique R" and "right_unique S"
  shows "right_unique (rel_substitute1 R S)"
  apply (subst conversep_conversep[of R, symmetric])
  apply (subst conversep_conversep[of S, symmetric])
  apply (subst rel_substitute1_flip[symmetric])
  apply (simp del: rel_substitute1_flip)
  apply (rule left_unique_rel_substitute1)
  using assms by auto

lemma bi_unique_rel_substitute1[transfer_rule]:
  assumes "bi_unique R" and "bi_unique S"
  shows "bi_unique (rel_substitute1 R S)"
  using assms by (meson bi_total_alt_def bi_unique_alt_def left_unique_rel_substitute1 right_unique_rel_substitute1)

lemma rel_set_subst_expression_footprint:
  includes lifting_syntax
  assumes "bi_unique R" and "bi_total R" and "type_preserving_var_rel R"
  defines "subR == rel_substitute1 R (rel_expression R (=))" (* TODO must be (=) ? *)
  assumes "list_all2 subR s1 s2"
  assumes "rel_set R vs1 vs2" 
  shows "rel_set R (subst_expression_footprint s1 vs1) (subst_expression_footprint s2 vs2)"
proof (rule rel_setI)

  have goal: "\<exists>y\<in>subst_expression_footprint s2 vs2. R x y" if "x \<in> subst_expression_footprint s1 vs1" 
    and [transfer_rule]: "list_all2 subR s1 s2"
    and [transfer_rule]: "rel_set R vs1 vs2"
    and [transfer_rule]: "bi_unique R"
    and [transfer_rule]: "bi_total R"
    and [transfer_rule]: "type_preserving_var_rel R"
    and subR_def: "subR = rel_substitute1 R (rel_expression R (=))"
  for x s1 s2 vs1 vs2 R subR
  proof -
    have [transfer_rule]: "(subR ===> R) substitution1_variable substitution1_variable"
      unfolding subR_def by (rule rel_substitute1_substitution1_variable)
    have [transfer_rule]: "(subR ===> rel_set R) substitution1_footprint substitution1_footprint"
      unfolding subR_def by (rule rel_substitute1_substitution1_footprint)
    have [transfer_rule]: "bi_unique subR" 
      unfolding subR_def
      using \<open>bi_unique R\<close> apply (rule bi_unique_rel_substitute1)
      apply (rule bi_unique_rel_expression)
      using that bi_unique_eq by auto
    show ?thesis
    proof (cases "x \<in> vs1 - substitution1_variable ` set s1")
      case False
      with that obtain sx vx where x_sx: "x \<in> substitution1_footprint sx" 
        and Some1: "Some sx = find (\<lambda>s. substitution1_variable s = vx) s1" 
        and sx_vs1: "substitution1_variable sx \<in> vs1"
        unfolding subst_expression_footprint_def by auto
      from Some1 obtain i where s1i: "s1!i = sx" and lens1: "i < length s1"
        by (metis find_Some_iff) 
      define sy where "sy = s2!i"
      then have [transfer_rule]: "subR sx sy" (* and "i < length s2" *)
        using s1i lens1 \<open>list_all2 subR s1 s2\<close> list_all2_conv_all_nth by blast
      from Some1 have vx_def: "vx = substitution1_variable sx"
        by (metis (mono_tags) find_Some_iff)
      define vy where "vy = substitution1_variable sy"
      have [transfer_rule]: "R vx vy" unfolding vy_def vx_def
        by (meson \<open>(subR ===> R) substitution1_variable substitution1_variable\<close> \<open>subR sx sy\<close> rel_funD)
      from sx_vs1 have "vx : vs1"
        by (simp add: vx_def)
      have Some2: "Some sy = find (\<lambda>s. substitution1_variable s = vy) s2"
        apply (transfer fixing: sy vy s1) 
        by (fact Some1)
      have sy_vs2: "substitution1_variable sy \<in> vs2"
        apply (transfer fixing: sy vs2)
        by (fact sx_vs1)
      have "rel_set R (substitution1_footprint sx) (substitution1_footprint sy)"
        by (meson \<open>(subR ===> rel_set R) substitution1_footprint substitution1_footprint\<close> \<open>subR sx sy\<close> rel_funD)
      with x_sx obtain y where Rxy: "R x y" and y_sy: "y \<in> substitution1_footprint sy"
        by (meson rel_set_def)
      from Some2 sy_vs2 y_sy have "y\<in>subst_expression_footprint s2 vs2"
        unfolding subst_expression_footprint_def by auto
      with Rxy show ?thesis by auto
    next
      case True
      have "rel_set R (vs1 - substitution1_variable ` set s1) (vs2 - substitution1_variable ` set s2)"
        by transfer_prover
      with True obtain y where "y \<in> vs2 - substitution1_variable ` set s2" and Rxy: "R x y"
        by (meson rel_set_def)
      then have "y\<in>subst_expression_footprint s2 vs2"
        unfolding subst_expression_footprint_def by auto
      with Rxy show ?thesis by auto 
    qed
  qed
  show "\<exists>y\<in>subst_expression_footprint s2 vs2. R x y" if "x \<in> subst_expression_footprint s1 vs1" for x
    apply (rule goal) using assms that by simp_all
  show "\<exists>x\<in>subst_expression_footprint s1 vs1. R x y" if "y \<in> subst_expression_footprint s2 vs2" for y
    apply (subst conversep_iff[of R, symmetric])
    apply (rule goal[where R="conversep R" and subR="conversep subR"]) 
          apply (simp_all add: list.rel_flip)
    using that assms by (simp_all add: subR_def)
qed

lemma rel_substitution1_function:
  includes lifting_syntax
  fixes R
  defines "subR == rel_substitute1 R (rel_expression R (=))"
  shows "(subR ===> rel_mem2 R ===> (=)) substitution1_function substitution1_function"
proof (rule rel_funI, rule rel_funI, rename_tac s1 s2 m1 m2)
  fix s1 s2 m1 m2
  assume s12: "subR s1 s2"
  assume m12: "rel_mem2 R m1 m2"
  show "substitution1_function s1 m1 = substitution1_function s2 m2"
    using s12 m12 unfolding subR_def 
    apply transfer unfolding rel_fun_def rel_set_def apply auto
    by (meson inv_into_injective range_subsetD)
qed

lemma rel_subst_mem2:
  includes lifting_syntax
  fixes R
  assumes [transfer_rule]: "bi_unique R"
  defines "subR == rel_substitute1 R (rel_expression R (=))"
  shows "(list_all2 subR ===> rel_mem2 R ===> rel_mem2 R) subst_mem2 subst_mem2"
proof (rule rel_funI, rule rel_funI)
  fix s1 s2 m1 m2
  assume s12[unfolded subR_def, transfer_rule]: "list_all2 subR s1 s2"
  assume m12[transfer_rule]: "rel_mem2 R m1 m2"
  show "rel_mem2 R (subst_mem2 s1 m1) (subst_mem2 s2 m2)"
    unfolding rel_mem2.rep_eq subst_mem2.rep_eq 
  proof (rule rel_funI, rename_tac v1 v2) 
    fix v1 v2
    assume v12[transfer_rule]: "R v1 v2"
    note rel_substitute1_substitution1_variable[transfer_rule]
    define find1 find2 where "find1 = find (\<lambda>s. substitution1_variable s = v1) s1" and "find2 = find (\<lambda>s. substitution1_variable s = v2) s2"
    have find12: "(rel_option subR) find1 find2" 
      unfolding find1_def find2_def subR_def
      by transfer_prover
    show "(case find1 of None \<Rightarrow> Rep_mem2 m1 v1 | Some s \<Rightarrow> substitution1_function s m1) =
          (case find2 of None \<Rightarrow> Rep_mem2 m2 v2 | Some s \<Rightarrow> substitution1_function s m2)"
    proof (cases "find1")
      case None
      with find12 have None2: "find2 = None" by auto
      show ?thesis
        unfolding None None2 apply simp
        by (metis (full_types) v12 m12 rel_fun_def rel_mem2.rep_eq)
    next
      case (Some s1')
      with find12 obtain s2' where Some2: "find2 = Some s2'" and [transfer_rule]: "subR s1' s2'"
        by (meson option_rel_Some1)
      have [transfer_rule]: "(subR ===> rel_mem2 R ===> (=)) substitution1_function substitution1_function"
         unfolding subR_def by (rule rel_substitution1_function)
      show ?thesis
        unfolding Some Some2 apply simp by transfer_prover
    qed
  qed
qed

lemma rel_expression_subst_expression [transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique R" and [transfer_rule]: "bi_total R" and [transfer_rule]: "type_preserving_var_rel R" (* TODO cleanup *)
  defines "subR == rel_substitute1 R (rel_expression R (=))"
  shows "(list_all2 subR ===> rel_expression R (=) ===> rel_expression R (=)) 
         subst_expression subst_expression"
proof -
  have "rel_expression R (=) (subst_expression s1 e1) (subst_expression s2 e2)" 
    if subR_s1_s2[transfer_rule]: "list_all2 subR s1 s2" and R_e1_e2: "rel_expression R (=) e1 e2" 
    for s1 s2 and e1 e2 :: "'b expression"
  proof -
    define vs1 E1 vs2 E2 where "vs1 = expression_vars e1" and "E1 = expression_eval e1"
      and "vs2 = expression_vars e2" and "E2 = expression_eval e2"
    have [unfolded subR_def, transfer_rule]: "(subR ===> rel_prod R (rel_prod (rel_set R) (rel_mem2 R ===> (=)))) Rep_substitution1 Rep_substitution1"
      unfolding subR_def apply (rule rel_substitute1_Rep_substitution1) by simp
    have [transfer_rule]: "(subR ===> R) substitution1_variable substitution1_variable"
      unfolding subR_def by (rule rel_substitute1_substitution1_variable)
    have [transfer_rule]: "bi_unique subR" 
      unfolding subR_def
      using \<open>bi_unique R\<close> apply (rule bi_unique_rel_substitute1)
      apply (rule bi_unique_rel_expression)
      using assms bi_unique_eq by auto
    have [transfer_rule]: "(subR ===> rel_set R) substitution1_footprint substitution1_footprint"
      unfolding subR_def by (rule rel_substitute1_substitution1_footprint)
    have R_vs1_vs2[transfer_rule]: "rel_set R vs1 vs2"
      unfolding vs1_def vs2_def using R_e1_e2 apply transfer by auto
    have foot: "rel_set R (subst_expression_footprint s1 vs1) (subst_expression_footprint s2 vs2)"
      apply (rule rel_set_subst_expression_footprint)
      using assms R_vs1_vs2 subR_s1_s2 unfolding subR_def by auto
    have E1E2: "(rel_mem2 R ===> (=)) E1 E2" 
      unfolding E1_def E2_def apply (rule rel_funI)
      using R_e1_e2 apply transfer 
      unfolding rel_mem2.rep_eq rel_fun_def by auto
    have subst_mem2_s1_s2: "(rel_mem2 R ===> rel_mem2 R) (subst_mem2 s1) (subst_mem2 s2)"
      using rel_subst_mem2 subR_s1_s2 \<open>bi_unique R\<close>
      by (metis rel_fun_def subR_def)
    from E1E2 subst_mem2_s1_s2 have subst: "(rel_mem2 R ===> (=)) (E1 \<circ> subst_mem2 s1) (E2 \<circ> subst_mem2 s2)"
      by (smt comp_def rel_funD rel_funI)
    show ?thesis
      unfolding rel_expression.rep_eq subst_expression.rep_eq using foot subst
      by (simp add: Rep_expression_components E1_def E2_def vs1_def vs2_def)
  qed

  then show ?thesis
     unfolding subR_def
    apply (rule_tac rel_funI)+ by assumption
qed

definition "rel_flip_index x y \<longleftrightarrow> index_flip_var_raw x = y"
lemma rel_flip_index_def': "rel_flip_index x y \<longleftrightarrow> x = index_flip_var_raw y"
    unfolding rel_flip_index_def by auto

lemma bi_unique_rel_flip_index: "bi_unique rel_flip_index" 
  apply (rule bi_uniqueI)
   apply (rule left_uniqueI, unfold rel_flip_index_def', auto)[1]
  by (rule right_uniqueI, unfold rel_flip_index_def, auto)[1]

lemma bi_total_rel_flip_index: "bi_total rel_flip_index"
  apply (rule bi_totalI)
   apply (rule left_totalI, unfold rel_flip_index_def, auto)[1]
  by (rule right_totalI, unfold rel_flip_index_def', auto)[1]

lemma type_preserving_rel_flip_index: "type_preserving_var_rel rel_flip_index"
    unfolding type_preserving_var_rel_def rel_flip_index_def by auto 

lemma rel_flip_index_conversep[simp]: "rel_flip_index\<inverse>\<inverse> = rel_flip_index"
  apply (rule ext)+ unfolding conversep_iff using rel_flip_index_def rel_flip_index_def' by auto

lemma index_flip_subst_expression: 
  fixes \<sigma> :: "substitution1 list" and e :: "'a::universe expression"
  shows "index_flip_expression (subst_expression \<sigma> e) 
        = subst_expression (map index_flip_substitute1 \<sigma>) (index_flip_expression e)"
proof -
  define subR where "subR = (rel_substitute1x rel_flip_index rel_flip_index)" 
  
  have rel_set_rel_flip_index: "rel_set rel_flip_index x y \<longleftrightarrow> index_flip_var_raw ` x = y" for x y
    unfolding rel_set_def rel_flip_index_def by auto

  include lifting_syntax
  note bi_unique_rel_flip_index[transfer_rule]
  note bi_total_rel_flip_index[transfer_rule]
  note type_preserving_rel_flip_index[transfer_rule]

  have rel_fun_flip[simp]: "(x ===> y)^--1 = (x^--1 ===> y^--1)" for x :: "'c\<Rightarrow>'d\<Rightarrow>bool" and y :: "'e\<Rightarrow>'f\<Rightarrow>bool" 
    unfolding rel_fun_def by auto

  have "rel_expression rel_flip_index (=) e (index_flip_expression e)" for e :: "'c expression"
  proof (unfold rel_expression.rep_eq index_flip_expression.rep_eq, cases "Rep_expression e", auto)
    fix vs f assume "Rep_expression e = (vs,f)"
    show "rel_set rel_flip_index vs (index_flip_var_raw ` vs)"
      by (rule rel_setI, unfold rel_flip_index_def, auto)
    show "(rel_mem2 rel_flip_index ===> (=)) f (\<lambda>m. f (index_flip_mem2 m))"
      apply (rule conversepD[of "(rel_mem2 rel_flip_index ===> (=))"])
      unfolding rel_fun_flip apply simp
      unfolding rel_fun_def rel_mem2.rep_eq rel_flip_index_def'
      unfolding rel_flip_index_def' apply transfer by auto
  qed
  then have [transfer_rule]: "((=) ===> rel_expression rel_flip_index (=)) (%x. x) index_flip_expression"
    unfolding rel_fun_def by auto

  have rel_flip_index_index_flip_var_raw: "rel_flip_index v (index_flip_var_raw v)" for v
    by (simp add: rel_flip_index_def)
  have rel_set_rel_flip_index_index_flip_var_raw: "rel_set rel_flip_index vs (index_flip_var_raw ` vs)" for vs
    by (subst rel_set_rel_flip_index, rule)
  have Fx: "F x = (F \<circ> index_flip_mem2) y" if "rel_mem2 rel_flip_index x y" for F::"mem2\<Rightarrow>'c" and x y
    using that apply transfer apply (auto simp: rel_flip_index_def[abs_def])
    by (metis (full_types) rel_fun_def)
  then have inv_embedding_index_flip_mem2: "(rel_mem2 rel_flip_index ===> (=)) (inv embedding \<circ> f) (inv embedding \<circ> (f \<circ> index_flip_mem2))" for f
    apply (rule_tac rel_funI) by simp

  have 1: "rel_prod rel_flip_index (\<lambda>(vs1, f1) (vs2, f2). 
              rel_prod (rel_set rel_flip_index) (rel_mem2 rel_flip_index ===> (=)) 
                       (vs1, inv embedding \<circ> f1) (vs2, inv embedding \<circ> f2))
              (v, vs, f) (index_flip_var_raw v, index_flip_var_raw ` vs, f \<circ> index_flip_mem2)" for v vs f
    by (auto intro: rel_flip_index_index_flip_var_raw rel_set_rel_flip_index_index_flip_var_raw inv_embedding_index_flip_mem2)

(*   define niceS where "niceS s \<longleftrightarrow> variable_raw_domain (substitution1_variable s) = range (embedding::'a\<Rightarrow>_)" for s
  define niceR where "niceR s1 s2 \<longleftrightarrow> s1=s2 \<and> niceS s1" for s1 s2 *)

  have "rel_substitute1x rel_flip_index rel_flip_index s (index_flip_substitute1 s)" (* if "niceS s" *) for s
    unfolding rel_substitute1x_def  
    using Fx by (auto simp: rel_flip_index_def substitution1_variable_index_flip substitution1_function_index_flip rel_fun_def)

  then have index_flip_substitute1_transfer [transfer_rule]:
    "((=) ===> subR) (%x. x) index_flip_substitute1"
    unfolding subR_def rel_fun_def by auto
(*   have [transfer_rule]: "bi_unique (rel_expression rel_flip_index (=))"
    sorry *)
  have "index_flip_expression e = f" if that[transfer_rule]: "rel_expression rel_flip_index (=) e f" for e f :: "'c expression"
    apply transfer by rule
  then have [transfer_rule]: "(rel_expression rel_flip_index (=) ===> rel_expression (=) (=)) index_flip_expression id"
    apply (rule_tac rel_funI) by (simp add: rel_expression_eq)

  have [transfer_rule]: "(list_all2 subR ===> rel_expression rel_flip_index (=) ===> rel_expression rel_flip_index (=))
   subst_expression subst_expression"
    unfolding subR_def by transfer_prover

  have "(rel_expression (=) (=))
        (index_flip_expression (subst_expression \<sigma> e))
        (id (subst_expression (map index_flip_substitute1 \<sigma>) (index_flip_expression e)))"
    apply transfer_prover_start
           apply transfer_step
           apply transfer_step
           apply transfer_step
           apply transfer_step
           apply transfer_step
           apply transfer_step
           apply transfer_step
    by simp
  then
  show "index_flip_expression (subst_expression \<sigma> e) = subst_expression (map index_flip_substitute1 \<sigma>) (index_flip_expression e)"
    unfolding rel_expression_eq id_def by assumption
qed


(* TODO move *)
lemma index_flip_subst_expression: 
  fixes \<sigma> :: "substitution1 list" and e :: "'a::universe expression"
  shows "index_flip_expression (subst_expression \<sigma> e) 
        = subst_expression (map index_flip_substitute1 \<sigma>) (index_flip_expression e)"
proof -
  define subR where "subR = (rel_substitute1 rel_flip_index (rel_expression rel_flip_index ((=)::'a\<Rightarrow>'a\<Rightarrow>bool)))" 
  
  have rel_set_rel_flip_index: "rel_set rel_flip_index x y \<longleftrightarrow> index_flip_var_raw ` x = y" for x y
    unfolding rel_set_def rel_flip_index_def by auto

  include lifting_syntax
  note bi_unique_rel_flip_index[transfer_rule]
  note bi_total_rel_flip_index[transfer_rule]
  note type_preserving_rel_flip_index[transfer_rule]

  have rel_fun_flip[simp]: "(x ===> y)^--1 = (x^--1 ===> y^--1)" for x :: "'c\<Rightarrow>'d\<Rightarrow>bool" and y :: "'e\<Rightarrow>'f\<Rightarrow>bool" 
    unfolding rel_fun_def by auto


  have "rel_expression rel_flip_index (=) e (index_flip_expression e)" for e :: "'c expression"
  proof (unfold rel_expression.rep_eq index_flip_expression.rep_eq, cases "Rep_expression e", auto)
    fix vs f assume "Rep_expression e = (vs,f)"
    show "rel_set rel_flip_index vs (index_flip_var_raw ` vs)"
      by (rule rel_setI, unfold rel_flip_index_def, auto)
    show "(rel_mem2 rel_flip_index ===> (=)) f (\<lambda>m. f (index_flip_mem2 m))"
      apply (rule conversepD[of "(rel_mem2 rel_flip_index ===> (=))"])
      unfolding rel_fun_flip apply simp
      unfolding rel_fun_def rel_mem2.rep_eq rel_flip_index_def'
      unfolding rel_flip_index_def' apply transfer by auto
  qed
  then have [transfer_rule]: "((=) ===> rel_expression rel_flip_index (=)) (%x. x) index_flip_expression"
    unfolding rel_fun_def by auto

  have rel_flip_index_index_flip_var_raw: "rel_flip_index v (index_flip_var_raw v)" for v
    by (simp add: rel_flip_index_def)
  have rel_set_rel_flip_index_index_flip_var_raw: "rel_set rel_flip_index vs (index_flip_var_raw ` vs)" for vs
    by (subst rel_set_rel_flip_index, rule)
  have "F x = (F \<circ> index_flip_mem2) y" if "rel_mem2 rel_flip_index x y" for F::"mem2\<Rightarrow>'c" and x y
    using that apply transfer apply (auto simp: rel_flip_index_def[abs_def])
    by (metis (full_types) rel_fun_def)
  then have inv_embedding_index_flip_mem2: "(rel_mem2 rel_flip_index ===> (=)) (inv embedding \<circ> f) (inv embedding \<circ> (f \<circ> index_flip_mem2))" for f
    apply (rule_tac rel_funI) by simp

  have 1: "rel_prod rel_flip_index (\<lambda>(vs1, f1) (vs2, f2). 
              rel_prod (rel_set rel_flip_index) (rel_mem2 rel_flip_index ===> (=)) 
                       (vs1, inv embedding \<circ> f1) (vs2, inv embedding \<circ> f2))
              (v, vs, f) (index_flip_var_raw v, index_flip_var_raw ` vs, f \<circ> index_flip_mem2)" for v vs f
    by (auto intro: rel_flip_index_index_flip_var_raw rel_set_rel_flip_index_index_flip_var_raw inv_embedding_index_flip_mem2)

  define niceS where "niceS s \<longleftrightarrow> variable_raw_domain (substitution1_variable s) = range (embedding::'a\<Rightarrow>_)" for s
  define niceR where "niceR s1 s2 \<longleftrightarrow> s1=s2 \<and> niceS s1" for s1 s2

  have "rel_substitute1 rel_flip_index (rel_expression rel_flip_index ((=)::'a\<Rightarrow>_\<Rightarrow>_)) s (index_flip_substitute1 s)" if "niceS s" for s
    using [[show_types, show_consts]]
    using that[unfolded niceS_def]
    apply transfer apply (case_tac s) using 1 by auto
  then have index_flip_substitute1_transfer [transfer_rule]: 
    "(niceR ===> subR) (%x. x) index_flip_substitute1"
    unfolding niceR_def subR_def rel_fun_def by auto
(*   have [transfer_rule]: "bi_unique (rel_expression rel_flip_index (=))"
    sorry *)
  have "index_flip_expression e = f" if that[transfer_rule]: "rel_expression rel_flip_index (=) e f" for e f :: "'c expression"
    apply transfer by rule
  then have [transfer_rule]: "(rel_expression rel_flip_index (=) ===> rel_expression (=) (=)) index_flip_expression id"
    apply (rule_tac rel_funI) by (simp add: rel_expression_eq)

  have [transfer_rule]: "(list_all2 subR ===> rel_expression rel_flip_index (=) ===> rel_expression rel_flip_index (=))
   subst_expression subst_expression"
    unfolding subR_def by transfer_prover

  have "(rel_expression (=) (=))
        (index_flip_expression (subst_expression \<sigma> e))
        (id (subst_expression (map index_flip_substitute1 \<sigma>) (index_flip_expression e)))"
    apply transfer_prover_start
           apply transfer_step
           apply transfer_step
           apply transfer_step
           apply transfer_step
           apply transfer_step
           apply transfer_step
           apply transfer_step
           apply transfer_step
    find_theorems map name:transfer
    by simp
  then
  show "index_flip_expression (subst_expression \<sigma> e) = subst_expression (map index_flip_substitute1 \<sigma>) (index_flip_expression e)"
    unfolding rel_expression_eq id_def by assumption
qed

(* (* TODO move *)
lemma index_flip_subst_expression: "index_flip_expression (subst_expression \<sigma> e) 
  = subst_expression (map index_flip_substitute1 \<sigma>) (index_flip_expression e)"
proof -
  have image: "x \<in> index_flip_var_raw ` X \<longleftrightarrow> index_flip_var_raw x \<in> X" for x X
    by force
  have uni_split: "A=A' \<Longrightarrow> B=B' \<Longrightarrow> A\<union>B = A'\<union>B'" for A B A' B' :: "'x set" 
    by auto
  have UNI_split: "X = Y \<Longrightarrow> \<Union>X = \<Union>Y" for X Y :: "'x set set" by auto
  have index_flip_substitute1_inj: "inj index_flip_substitute1" sorry

(* IDEA: Use transfer to show the equality, by relating the lhs/rhs via index_flip_var_raw *)

  define vs where "vs = expression_vars e"
  have "expression_vars (index_flip_expression (subst_expression \<sigma> e)) = 
        index_flip_var_raw ` subst_expression_footprint \<sigma> vs"
    by (simp add: subst_expression_footprint vs_def)
  have "\<dots> = index_flip_var_raw ` Union {substitution1_footprint s | s v. 
        Some s = find (\<lambda>s. substitution1_variable s = v) \<sigma> \<and> substitution1_variable s \<in> vs}
        \<union> index_flip_var_raw ` (vs - substitution1_variable ` set \<sigma>)" (is "_ = _ \<union> ?v")
    unfolding subst_expression_footprint_def by auto
  have "\<dots>
      = Union {index_flip_var_raw ` substitution1_footprint s | s v. 
        Some s = find (\<lambda>s. substitution1_variable s = v) \<sigma> \<and> substitution1_variable s \<in> vs} \<union> ?v" 
        (is "_ = Union {_ | s v. ?l s v \<and> ?r s v} \<union> _")
    by auto
  also have "\<dots> = Union {substitution1_footprint (index_flip_substitute1 s) | s v. ?l s v \<and> ?r s v} \<union> ?v"
    by (auto simp: index_flip_var_raw_substitution1_footprint)
  also have "\<dots> = Union {substitution1_footprint (index_flip_substitute1 (index_flip_substitute1 s)) | s v. 
        Some (index_flip_substitute1 s) = find (\<lambda>s. substitution1_variable s = index_flip_var_raw v) \<sigma> 
        \<and> substitution1_variable (index_flip_substitute1 s) \<in> vs} \<union> ?v"
        (is "_ = Union {_ | s v. ?l s v \<and> ?r s v} \<union> _")
    apply (subst Ex_substitute[where f=index_flip_substitute1])
    using index_flip_substitute1_twice surjI apply blast 
    apply (subst Ex_substitute[where f=index_flip_var_raw])
    using index_flip_var_twice surjI apply blast 
    by simp
  also have "\<dots> = Union {substitution1_footprint s | s v. ?l s v \<and> ?r s v} \<union> ?v"
    by (simp add: substitution1_variable_index_flip) 
  also have "\<dots> = Union {substitution1_footprint s | s v. 
         Some s = map_option index_flip_substitute1 (find (\<lambda>s. substitution1_variable s = index_flip_var_raw v) \<sigma>)
          \<and> ?r s v} \<union> ?v"
    using map_option_Some_eq[OF index_flip_substitute1_inj] index_flip_substitute1_twice
    by (metis (no_types, lifting))
  also have "\<dots> = Union {substitution1_footprint s | s v. 
         Some s = (find (\<lambda>s. substitution1_variable (index_flip_substitute1 s) = v) (map index_flip_substitute1 \<sigma>))
          \<and> ?r s v} \<union> ?v"
      (is "_ = Union {_ | s v. ?l s v \<and> ?r s v} \<union> _")
    using find_map[where f=index_flip_substitute1 and l=\<sigma>] index_flip_substitute1_twice 
    apply (subst find_map, auto) by (metis index_flip_var_twice)
  also have "\<dots> = Union {substitution1_footprint s | s v. 
         ?l s v \<and> substitution1_variable s \<in> index_flip_var_raw ` vs} \<union> ?v"
      (is "_ = ?u \<union> ?v")
    by (simp add: image substitution1_variable_index_flip)
  also have "\<dots> = ?u \<union> (index_flip_var_raw ` vs - index_flip_var_raw ` substitution1_variable ` set \<sigma>)" 

  also have "\<dots> = subst_expression_footprint (map index_flip_substitute1 \<sigma>) (index_flip_var_raw ` vs)"
    unfolding subst_expression_footprint_def 
    apply (unfold image_Un, rule uni_split)
    apply (subst image, subst find_map)
    by xxx
  find_theorems " (_ \<union> _) =  (_ \<union> _)"

  have "expression_vars (subst_expression (map index_flip_substitute1 \<sigma>) (index_flip_expression e))
      = subst_expression_footprint (map index_flip_substitute1 \<sigma>) (index_flip_var_raw ` vs)"
    by (simp add: subst_expression_footprint vs_def)
  have "... = xxx"
    unfolding subst_expression_footprint_def find_map vimage 
substitution1_variable_index_flip

  obtain vs E where e: "(vs,E) = Rep_expression e"
    by (xmetis surj_pair) by auto
  find_theorems "expression_vars" subst_expression
  then show ?thesis sorry
qed
  apply (subst Rep_expression_inject[symmetric])
  unfolding index_flip_expression.rep_eq subst_expression.rep_eq
  apply (cases "Rep_expression e") apply simp
  by (cheat index_flip_subst_expression) *)

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
      index_flip_expression_index_expression
      index_flip_map_expression2' o_def)
  by (rule sample1_rule)

end
