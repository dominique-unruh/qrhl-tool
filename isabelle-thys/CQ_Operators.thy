theory CQ_Operators
  imports Kraus_Maps
begin

definition \<open>cq_map_rel \<EE> \<FF> \<longleftrightarrow> (\<forall>x. kraus_family_norm (\<EE> x) \<le> 1 \<and> kraus_equivalent' (\<EE> x) (\<FF> x))\<close>
  for \<EE> \<FF> :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'cl2) kraus_family\<close>

typedef ('cl,'qu) cq_operator = \<open>{\<rho> :: 'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class. (\<forall>c. \<rho> c \<ge> 0) \<and> 
                          (\<lambda>c. trace_tc (\<rho> c)) summable_on UNIV \<and> (\<Sum>\<^sub>\<infinity>c. trace_tc (\<rho> c)) \<le> 1}\<close>
  apply (rule exI[of _ \<open>\<lambda>_. 0\<close>])
  by auto
setup_lifting type_definition_cq_operator

lift_definition fixed_cl_cq_operator :: \<open>'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class \<Rightarrow> ('cl,'qu) cq_operator\<close> is
  \<open>\<lambda>c (\<rho>::('qu ell2, 'qu ell2) trace_class) d. if \<rho> \<ge> 0 \<and> trace_tc \<rho> \<le> 1 then of_bool (c=d) *\<^sub>R \<rho> else 0\<close>
proof (rename_tac c \<rho>, intro conjI allI)
  fix c d :: 'cl and \<rho> :: \<open>('qu ell2, 'qu ell2) trace_class\<close>
  show \<open>0 \<le> (if \<rho> \<ge> 0 \<and> trace_tc \<rho> \<le> 1 then of_bool (c = d) *\<^sub>R \<rho> else 0)\<close>
    by simp
  show \<open>(\<lambda>d. trace_tc (if \<rho> \<ge> 0 \<and> trace_tc \<rho> \<le> 1 then of_bool (c = d) *\<^sub>R \<rho> else 0)) summable_on UNIV\<close>
  proof (cases \<open>\<rho> \<ge> 0 \<and> trace_tc \<rho> \<le> 1\<close>)
    case True
    have \<open>(\<lambda>d. trace_tc (of_bool (c = d) *\<^sub>R \<rho>)) summable_on UNIV\<close>
      apply (rule finite_nonzero_values_imp_summable_on)
      by auto
    with True show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by auto
  qed
  show \<open>(\<Sum>\<^sub>\<infinity>d. trace_tc (if \<rho> \<ge> 0 \<and> trace_tc \<rho> \<le> 1 then of_bool (c = d) *\<^sub>R \<rho> else 0)) \<le> 1\<close>
  proof (cases \<open>\<rho> \<ge> 0 \<and> trace_tc \<rho> \<le> 1\<close>)
    case True
    have \<open>(\<Sum>\<^sub>\<infinity>d. trace_tc (of_bool (c = d) *\<^sub>R \<rho>)) = trace_tc \<rho>\<close>
      apply (subst infsum_single[where i=c])
      by auto
    also have \<open>trace_tc \<rho> \<le> 1\<close>
      using True by blast
    finally show ?thesis
      by (simp add: True)
  next
    case False
    then show ?thesis
      by auto
  qed
qed


quotient_type ('cl1,'qu1,'cl2,'qu2) cq_map = \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'cl2) kraus_family\<close> /
  partial: cq_map_rel
proof (rule part_equivpI)
  show \<open>\<exists>x. cq_map_rel x x\<close>
    apply (rule exI[of _ \<open>\<lambda>_. 0\<close>])
    by (simp add: cq_map_rel_def)
  show \<open>symp cq_map_rel\<close>
  proof (rule sympI)
    fix \<EE> \<FF> assume asm: \<open>cq_map_rel \<EE> \<FF>\<close>
    then have eq1: \<open>kraus_equivalent' (\<EE> x) (\<FF> x)\<close> for x
      unfolding cq_map_rel_def by blast
    then have eq2: \<open>kraus_equivalent' (\<FF> x) (\<EE> x)\<close> for x
      using kraus_equivalent'_sym by blast
    from eq1 have eq3: \<open>kraus_equivalent (\<EE> x) (\<FF> x)\<close> for x
      by (rule kraus_equivalent'_imp_equivalent)
    have \<open>kraus_family_norm (\<EE> x) \<le> 1\<close> for x
      using asm unfolding cq_map_rel_def by blast
    with eq3
    have norm: \<open>kraus_family_norm (\<FF> x) \<le> 1\<close> for x
      by (metis kraus_family_norm_welldefined)
    with eq2 show \<open>cq_map_rel \<FF> \<EE>\<close>
      by (simp add: cq_map_rel_def)
  qed
  show \<open>transp cq_map_rel\<close>
    apply (auto intro!: transpI simp: cq_map_rel_def)
    using kraus_equivalent'_trans by blast
qed
(* setup_lifting type_definition_cq_map *)

lift_definition cq_map_id :: \<open>('cl,'qu,'cl,'qu) cq_map\<close> is 
  \<open>\<lambda>c. kraus_family_map_outcome (\<lambda>(). c) kraus_family_id\<close>
  by (simp add: cq_map_rel_def)

lift_definition cq_map_apply :: \<open>('cl1,'qu1,'cl2,'qu2) cq_map \<Rightarrow> ('cl1,'qu1) cq_operator \<Rightarrow> ('cl2,'qu2) cq_operator\<close> is
  \<open>\<lambda>\<EE> \<rho> c. (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))\<close>
proof (rename_tac \<EE> \<EE>' \<rho>, intro conjI allI ext)
  fix \<EE> \<EE>' :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'cl2) kraus_family\<close>
  assume rel: \<open>cq_map_rel \<EE> \<EE>'\<close>
  then have norm_\<EE>: \<open>kraus_family_norm (\<EE> x) \<le> 1\<close> for x
    unfolding cq_map_rel_def by blast
  fix \<rho> :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu1 ell2) trace_class\<close> and c
  assume \<open>(\<forall>c. 0 \<le> \<rho> c) \<and> (\<lambda>c. trace_tc (\<rho> c)) summable_on UNIV \<and> (\<Sum>\<^sub>\<infinity>c. trace_tc (\<rho> c)) \<le> 1\<close>
  then have \<rho>_pos: \<open>0 \<le> \<rho> c\<close> and \<rho>_sum: \<open>(\<lambda>c. trace_tc (\<rho> c)) summable_on UNIV\<close> and \<rho>_leq1: \<open>(\<Sum>\<^sub>\<infinity>c. trace_tc (\<rho> c)) \<le> 1\<close> for c
    by auto
  from \<rho>_pos
  show \<open>0 \<le> (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))\<close>
    by (auto intro!: infsum_nonneg_traceclass kraus_family_map'_pos)


  from \<rho>_pos
  have 9: \<open>trace_tc (kraus_family_map (\<EE> d) (\<rho> d)) \<le> kraus_family_norm (\<EE> d) * trace_tc (\<rho> d)\<close> for d
    by (smt (verit) Extra_Ordered_Fields.complex_of_real_cmod cmod_mono complex_of_real_nn_iff 
        kraus_family_map_bounded_pos abs_pos kraus_family_map_pos nn_comparable norm_tc_pos of_real_hom.hom_mult 
        of_real_hom.injectivity trace_tc_0 trace_tc_mono) 
  from \<rho>_pos have 10: \<open>\<dots>d \<le> trace_tc (\<rho> d)\<close> for d
    by (smt (verit, del_insts) Rings.mult_sign_intros(1) cmod_Re complex_of_real_leq_1_iff complex_of_real_nn_iff kraus_family_norm_geq0 less_eq_complex_def mult_left_le_one_le norm_\<EE> norm_ge_zero norm_mult norm_one trace_tc_pos)
  have 0: \<open>0 \<le> Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close> for c d
    by (metis Re_complex_of_real \<rho>_pos kraus_family_map'_pos norm_cblinfun_mono_trace_class norm_tc_pos norm_zero order_eq_refl)
  have 3: \<open>(\<Sum>\<^sub>\<infinity>c. kraus_family_map' {c} (\<EE> d) (\<rho> d)) = kraus_family_map (\<EE> d) (\<rho> d)\<close> for d
  proof -
    have \<open>(\<Sum>\<^sub>\<infinity>c. kraus_family_map' {c} (\<EE> d) (\<rho> d)) = (\<Sum>\<^sub>\<infinity>X\<in>range (\<lambda>c. {c}). kraus_family_map' X (\<EE> d) (\<rho> d))\<close>
      by (simp add: infsum_reindex o_def)
    also have \<open>\<dots> = kraus_family_map' (\<Union>(range (\<lambda>c. {c}))) (\<EE> d) (\<rho> d)\<close>
      apply (rule kraus_family_map'_union_infsum)
      by auto
    also have \<open>\<dots> = kraus_family_map (\<EE> d) (\<rho> d)\<close>
      by simp
    finally show ?thesis
      by -
  qed
  have 4: \<open>(\<lambda>c. kraus_family_map' {c} (\<EE> d) (\<rho> d)) summable_on UNIV\<close> for d
  proof -
    have \<open>(\<lambda>X. kraus_family_map' X (\<EE> d) (\<rho> d)) summable_on range (\<lambda>c. {c})\<close> for d
      apply (rule kraus_family_map'_union_summable_on)
      by auto
    then show ?thesis
      apply (rule summable_on_reindex[THEN iffD1, unfolded o_def, rotated])
      by simp
  qed
  have 16: \<open>bounded_linear (\<lambda>x. Re (trace_tc x))\<close> for x :: \<open>('qu ell2,'qu ell2) trace_class\<close>
    by (intro bounded_linear_compose[OF bounded_linear_Re] bounded_linear_intros)
  from 3 4 have 5: \<open>(\<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) = Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))\<close> for d
    apply (subst infsum_bounded_linear[where h=\<open>Re o trace_tc\<close>, unfolded o_def])
    using 16 by auto
  have 13: \<open>0 \<le> Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))\<close> for d
    by (metis Re_complex_of_real \<rho>_pos kraus_family_map_pos norm_cblinfun_mono_trace_class norm_tc_pos norm_zero order_eq_refl)
  from \<rho>_sum   have 12:  \<open>(\<lambda>d. Re (trace_tc (\<rho> d))) summable_on UNIV\<close>
    using summable_on_Re by blast
  from 9 10 have 14: \<open>Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d))) \<le> Re (trace_tc (\<rho> d))\<close> for d
    apply (auto intro!: Re_mono)
    using basic_trans_rules(23) by blast
  have 6: \<open>(\<lambda>d. Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (rule summable_on_comparison_test[where f=\<open>\<lambda>d. Re (trace_tc (\<rho> d))\<close>])
    using 12 13 14 by auto
  from 6 have 11: \<open>(\<Sum>\<^sub>\<infinity>d. Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))) \<le> (\<Sum>\<^sub>\<infinity>d. Re (trace_tc (\<rho> d)))\<close>
    apply (rule infsum_mono)
    using 12 14 by auto
  have 28: \<open>norm (\<rho> d) = Re (trace_tc (\<rho> d))\<close> for d
    by (metis Re_complex_of_real \<rho>_pos norm_tc_pos)
  have 27: \<open>\<rho> summable_on UNIV\<close>
    apply (rule abs_summable_summable)
    using 12 28 by auto
  have 15: \<open>(\<Sum>\<^sub>\<infinity>d. Re (trace_tc (\<rho> d))) \<le> 1\<close>
    apply (subst infsum_bounded_linear[where h=\<open>Re o trace_tc\<close>, unfolded o_def])
    using 16 27 28 \<rho>_sum \<rho>_leq1 \<rho>_pos
      apply auto
    by (smt (verit) Infinite_Sum.infsum_nonneg_complex abs_summable_on_comparison_test cmod_mono complex_Re_le_cmod infsum_Re infsum_cong norm_infsum_bound norm_one summable_on_iff_abs_summable_on_complex trace_tc_norm trace_tc_pos)
  from 5 6 have 2: \<open>(\<lambda>d. \<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    by simp
  have 17: \<open>(\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) \<le> 1\<close>
    using 5 15 11
    by auto
  have 29: \<open>(\<lambda>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close> for d
    apply (rule summable_on_bounded_linear[where h=\<open>\<lambda>x. Re (trace_tc x)\<close>])
    using 16 4 by auto
  have 18: \<open>(\<lambda>(d,c). Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on (UNIV \<times> UNIV)\<close>
    apply (rule summable_on_SigmaI[where g=\<open>\<lambda>d. \<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close>])
    using 0 5 6 29 by (auto intro!: has_sumI)
  have 21: \<open>(\<lambda>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close> for c
    using summable_on_SigmaD1[OF summable_on_swap[THEN iffD1, OF 18]]
    by auto
  have 22: \<open>(\<lambda>c. \<Sum>\<^sub>\<infinity>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (rule summable_on_Sigma_banach)
    apply (rule summable_on_swap[THEN iffD2])
    using 18 by simp
  have 20: \<open>(\<lambda>(c, d). Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (subst asm_rl[of \<open>UNIV = UNIV \<times> UNIV\<close>], simp)
    apply (rule summable_on_SigmaI[where g=\<open>\<lambda>c. \<Sum>\<^sub>\<infinity>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close>])
    using 21 22 0 by (auto intro!: has_sum_infsum)
  from 17 18 20 have 19: \<open>(\<Sum>\<^sub>\<infinity>c. \<Sum>\<^sub>\<infinity>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) \<le> 1\<close>
    apply (subst infsum_swap_banach)
    by auto
  have 36: \<open>norm (kraus_family_map' {c} (\<EE> d) (\<rho> d)) = Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close> for c d
    apply (rule norm_tc_pos_Re)
    by (simp add: \<rho>_pos kraus_family_map'_pos)
  from 36 have 35: \<open>(\<lambda>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)) abs_summable_on UNIV\<close> for c
    by (simp add: 36 21)
  from 35 have 34: \<open>(\<lambda>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)) summable_on UNIV\<close> for c
    by (rule abs_summable_summable)
  from 22 have 23: \<open>(\<lambda>c. Re (trace_tc (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (rule summable_on_cong[THEN iffD1, rotated])
    using 16 34 by (rule infsum_bounded_linear[unfolded o_def])
  have 25: \<open>(\<Sum>\<^sub>\<infinity>c. \<Sum>\<^sub>\<infinity>d. trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d))) \<ge> 0\<close>
    by (auto intro!: infsum_nonneg_complex trace_tc_pos kraus_family_map'_pos \<rho>_pos)
  from 23 show \<open>(\<lambda>c. trace_tc (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))) summable_on UNIV\<close>
    apply (rewrite at \<open>trace_tc _\<close> of_real_Re[symmetric])
    by (auto intro!: nonnegative_complex_is_real summable_on_bounded_linear[where h=of_real]
        bounded_linear_of_real trace_tc_pos  infsum_nonneg_traceclass kraus_family_map'_pos \<rho>_pos)
  have 26: \<open>(\<Sum>\<^sub>\<infinity>c. Re (trace_tc (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)))) \<le> 1\<close>
    apply (subst infsum_bounded_linear[OF 16, symmetric, unfolded o_def])
    using 19 34 by auto
  from 26 show \<open>(\<Sum>\<^sub>\<infinity>c. trace_tc (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))) \<le> 1\<close>
    apply (rewrite at \<open>trace_tc _\<close> of_real_Re[symmetric])
    by (auto intro!: nonnegative_complex_is_real summable_on_bounded_linear[where h=of_real]
        bounded_linear_of_real trace_tc_pos  infsum_nonneg_traceclass kraus_family_map'_pos \<rho>_pos
        simp: infsum_of_real )
  from rel
  show \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)) = (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE>' d) (\<rho> d))\<close>
    by (auto intro!: kraus_family_map'_eqI infsum_cong simp: cq_map_rel_def)
qed

lift_definition cq_map_seq :: \<open>('cl1,'qu1,'cl2,'qu2) cq_map \<Rightarrow> ('cl2,'qu2,'cl3,'qu3) cq_map \<Rightarrow> ('cl1,'qu1,'cl3,'qu3) cq_map\<close>
  is \<open>\<lambda>\<EE> \<FF> c. kraus_family_map_outcome snd (kraus_family_comp_dependent \<FF> (\<EE> c))\<close>
proof -
  fix \<EE> \<EE>' :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'cl2) kraus_family\<close>
  fix \<FF> \<FF>' :: \<open>'cl2 \<Rightarrow> ('qu2 ell2, 'qu3 ell2, 'cl3) kraus_family\<close>
  assume asms: \<open>cq_map_rel \<EE> \<EE>'\<close>  \<open>cq_map_rel \<FF> \<FF>'\<close>
  have F1: \<open>kraus_family_norm (\<FF>' x) \<le> 1\<close> for x
    by (metis asms(2) kraus_equivalent'_imp_equivalent kraus_family_norm_welldefined cq_map_rel_def)
  have \<open>kraus_family_norm (kraus_family_comp_dependent \<FF> (\<EE> x)) \<le> 1 * kraus_family_norm (\<EE> x)\<close> for x
    apply (rule kraus_family_comp_dependent_norm)
    using asms(2) unfolding cq_map_rel_def by blast
  also have \<open>\<dots>x \<le> 1 * 1\<close> for x
    using asms(1) cq_map_rel_def by force
  finally have 1: \<open>kraus_family_norm (kraus_family_comp_dependent \<FF> (\<EE> x)) \<le> 1\<close> for x
    by simp
  have 2: \<open>kraus_equivalent' (kraus_family_map_outcome snd (kraus_family_comp_dependent \<FF> (\<EE> x)))
                 (kraus_family_map_outcome snd (kraus_family_comp_dependent \<FF>' (\<EE>' x)))\<close> for x
    using asms
    by (auto intro!: F1 bdd_aboveI kraus_equivalent'_map_cong kraus_family_comp_dependent_cong'
        simp: cq_map_rel_def)
  from 1 2
  show \<open>cq_map_rel (\<lambda>c. kraus_family_map_outcome snd (kraus_family_comp_dependent \<FF> (\<EE> c)))
        (\<lambda>c. kraus_family_map_outcome snd (kraus_family_comp_dependent \<FF>' (\<EE>' c)))\<close>
    by (simp add: cq_map_rel_def)
qed

lemma cq_map_eqI:
  assumes \<open>\<And>\<rho>. cq_map_apply s \<rho> = cq_map_apply t \<rho>\<close>
  shows \<open>s = t\<close>
proof -
  from assms[THEN Rep_cq_operator_inject[THEN iffD2]]
  have *: \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (rep_cq_map s d) (Rep_cq_operator \<rho> d))
      = (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (rep_cq_map t d) (Rep_cq_operator \<rho> d))\<close> for c \<rho>
    apply (simp add: cq_map_apply.rep_eq)
    by meson
  have \<open>kraus_family_map' {c} (rep_cq_map s d) \<rho> = kraus_family_map' {c} (rep_cq_map t d) \<rho>\<close>
    if \<open>\<rho> \<ge> 0\<close> and \<open>trace_tc \<rho> \<le> 1\<close> for c d \<rho>
    using *[of c \<open>fixed_cl_cq_operator d \<rho>\<close>]
    unfolding fixed_cl_cq_operator.rep_eq
    apply (subst (asm) infsum_single[where i=d])
     apply auto[1]
    apply (subst (asm) infsum_single[where i=d])
    using that by auto
  then have \<open>kraus_family_map' {c} (rep_cq_map s d) = kraus_family_map' {c} (rep_cq_map t d)\<close> for c d
    apply (rule eq_from_separatingI[OF separating_density_ops[where B=1], rotated -1])
        apply (auto intro!: kraus_family_map'_bounded_clinear bounded_clinear.clinear)
    using complex_of_real_mono norm_tc_pos by fastforce
  from fun_cong[OF this] have \<open>kraus_equivalent' (rep_cq_map s c) (rep_cq_map t c)\<close> for c
    by (rule kraus_equivalent'I)
  then show ?thesis
    apply (rule_tac Quotient3_rel_rep[OF Quotient3_cq_map, THEN iffD1])
    using Quotient3_rep_reflp[OF Quotient3_cq_map, of s]
    using Quotient3_rep_reflp[OF Quotient3_cq_map, of t]
    by (simp add: cq_map_rel_def)
qed

lemma cq_map_apply_id[simp]: \<open>cq_map_apply cq_map_id \<rho> = \<rho>\<close>
proof transfer'
  fix \<rho> :: \<open>'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class\<close>
  have inj: \<open>inj_on (\<lambda>(). x) X\<close> for x :: 'cl and X
    by (simp add: inj_onI)

  show \<open>(\<lambda>c. \<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome (\<lambda>(). d) kraus_family_id) (\<rho> d)) = \<rho>\<close>
  proof (rule ext)
    fix c
    have 1: \<open>Set.filter (\<lambda>(E, x). x = c) {(id_cblinfun, j)} = {}\<close> if \<open>j \<noteq> c\<close> for j :: 'cl
      using that by auto

    have \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome (\<lambda>(). d) kraus_family_id) (\<rho> d))
      = (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome_inj (\<lambda>(). d) kraus_family_id) (\<rho> d))\<close>
      by (auto intro!: infsum_cong kraus_family_map'_eqI kraus_equivalent'_map_outcome_inj[symmetric] inj)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>E\<in>Set.filter (\<lambda>(E, x). x = c) {(id_cblinfun, d)}. sandwich_tc (fst E) (\<rho> d))\<close>
      by (simp add: kraus_family_map'_def kraus_family_map.rep_eq kraus_family_filter.rep_eq
          kraus_family_map_outcome_inj.rep_eq kraus_family_id_def kraus_family_of_op.rep_eq Nitpick.case_unit_unfold)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>Set.filter (\<lambda>(E::'qu ell2 \<Rightarrow>\<^sub>C\<^sub>L 'qu ell2, x). x = c) {(id_cblinfun, c)}. \<rho> c)\<close>
      apply (subst infsum_single[where i=c])
      by (auto simp: 1)
    also have \<open>\<dots> = \<rho> c\<close>
      apply (subst infsum_single[where i=\<open>(id_cblinfun,c)\<close>])
      by auto
    finally show \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome (\<lambda>(). d) kraus_family_id) (\<rho> d)) = \<rho> c\<close>
      by -
  qed
qed

lemma cq_map_apply_seq: \<open>cq_map_apply (cq_map_seq s t) \<rho> = cq_map_apply t (cq_map_apply s \<rho>)\<close>
proof (transfer, intro ext)
  fix s :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'cl2) kraus_family\<close>
    and t :: \<open>'cl2 \<Rightarrow> ('qu2 ell2, 'qu3 ell2, 'cl3) kraus_family\<close>
    and \<rho> :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu1 ell2) trace_class\<close> and c :: 'cl3
  assume assms: \<open>(\<forall>c. 0 \<le> \<rho> c) \<and> (\<lambda>c. trace_tc (\<rho> c)) summable_on UNIV \<and> (\<Sum>\<^sub>\<infinity>c. trace_tc (\<rho> c)) \<le> 1\<close>
  assume \<open>cq_map_rel s s\<close>
  assume \<open>cq_map_rel t t\<close>
  then have bdd_t: \<open>bdd_above (range (kraus_family_norm \<circ> t))\<close>
    by (auto simp: cq_map_rel_def)
  have inj: \<open>inj_on fst (Set.filter (\<lambda>(E, x). x = f) X)\<close> for X f
    by (auto intro!: inj_onI)
  from bdd_t have bdd': \<open>bdd_above (range (kraus_family_norm \<circ> (\<lambda>e. kraus_family_filter (\<lambda>f. f = c) (t e))))\<close>
    apply (rule bdd_above_mono2)
    by (auto simp: kraus_family_norm_filter)
  have \<rho>_abs: \<open>\<rho> abs_summable_on UNIV\<close>
    by (smt (verit) assms complex_Re_le_cmod norm_tc_pos_Re summable_on_cong summable_on_iff_abs_summable_on_complex trace_tc_norm)

  have summ2: \<open>(\<lambda>d. kraus_family_map' {f} (s d) (\<rho> d)) summable_on UNIV\<close> for f
  proof (rule abs_summable_summable, rule abs_summable_on_comparison_test)
    from \<rho>_abs show \<open>\<rho> abs_summable_on UNIV\<close>
      by -
    fix d
    have \<open>norm (kraus_family_map' {f} (s d) (\<rho> d)) \<le> kraus_family_norm (kraus_family_filter (\<lambda>x. x = f) (s d)) * norm (\<rho> d)\<close>
      using assms by (auto intro!: kraus_family_map_bounded_pos simp add: kraus_family_map'_def)
    also have \<open>\<dots> \<le> 1 * norm (\<rho> d)\<close>
      apply (rule mult_right_mono)
      using \<open>cq_map_rel s s\<close>
        kraus_family_norm_filter[of \<open>\<lambda>x. x = f\<close> \<open>s d\<close>]
       apply (auto intro!: simp: cq_map_rel_def)
      by (smt (verit, del_insts))
    also have \<open>\<dots> \<le> norm (\<rho> d)\<close>
      by simp
    finally show \<open>norm (kraus_family_map' {f} (s d) (\<rho> d)) \<le> norm (\<rho> d)\<close>
      by -
  qed
  have summ3: \<open>(\<lambda>F. sandwich_tc F (\<rho> c)) summable_on {F. (F, f) \<in> Rep_kraus_family (s c)}\<close> for c f
  proof -
    have *: \<open>(\<lambda>x. fst x) ` Set.filter (\<lambda>Ff. snd Ff = f) (Rep_kraus_family (s c))
        = {F. (F, f) \<in> Rep_kraus_family (s c)}\<close>
      by (auto intro!: simp: image_iff Bex_def)
    from kraus_family_map_summable[of _ \<open>s c\<close>]
    have \<open>(\<lambda>Ff. sandwich_tc (fst Ff) (\<rho> c)) summable_on Rep_kraus_family (s c)\<close>
      by (simp add: case_prod_unfold)
    then have \<open>(\<lambda>Ff. sandwich_tc (fst Ff) (\<rho> c)) summable_on Set.filter (\<lambda>Ff. snd Ff = f) (Rep_kraus_family (s c))\<close>
      apply (rule summable_on_subset_banach)
      by auto
    then show ?thesis
      apply (subst (asm) summable_on_reindex[unfolded o_def, symmetric, where h=fst])
      by (auto intro!: inj_onI simp: * )
  qed
(*   have summ: \<open>(\<lambda>F. kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d))) summable_on
       {F. (F, f) \<in> Rep_kraus_family (s d)}\<close> for f d c
    by x *)
  have summ4: \<open>(\<lambda>y. kraus_family_map' {c} (t y) (kraus_family_map' {y} (s d) (\<rho> d))) summable_on UNIV\<close> for d
  proof -
    have 1: \<open>(\<lambda>f. kraus_family_map' {f} (s d) (\<rho> d)) abs_summable_on UNIV\<close>
    proof -
      have \<open>(\<lambda>X. kraus_family_map' X (s d) (\<rho> d)) summable_on range (\<lambda>f. {f})\<close>
        apply (rule kraus_family_map'_union_summable_on)
        by auto
      then have \<open>(\<lambda>f. kraus_family_map' {f} (s d) (\<rho> d)) summable_on UNIV\<close>
        apply (subst (asm) summable_on_reindex)
        by (simp_all add: o_def)
      then show ?thesis
        apply (rule summable_abs_summable_tc)
        using assms by (auto intro!: kraus_family_map'_pos simp: )
    qed
    have 2: \<open>norm (kraus_family_map' {c} (t f) (kraus_family_map' {f} (s d) (\<rho> d)))
         \<le> norm (kraus_family_map' {f} (s d) (\<rho> d))\<close> for f
    proof -
      have \<open>norm (kraus_family_map' {c} (t f) (kraus_family_map' {f} (s d) (\<rho> d)))
        \<le> kraus_family_norm (kraus_family_filter (\<lambda>x. x\<in>{c}) (t f)) * norm (kraus_family_map' {f} (s d) (\<rho> d))\<close>
        using assms
        by (auto intro!: kraus_family_map_bounded_pos
            simp: kraus_family_map'_def kraus_family_map_pos)
      also have \<open>\<dots> \<le> 1 * norm (kraus_family_map' {f} (s d) (\<rho> d))\<close>
        apply (rule mult_right_mono)
         apply (smt (verit, best) \<open>cq_map_rel t t\<close> kraus_family_norm_filter cq_map_rel_def)
        by simp
      finally show ?thesis
        by simp
    qed
    show ?thesis
      apply (rule abs_summable_summable)
      using 1 2 by (rule abs_summable_on_comparison_test)
  qed

  have \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome snd (kraus_family_comp_dependent t (s d))) (\<rho> d))
     = (\<Sum>\<^sub>\<infinity>d. kraus_family_map (kraus_family_filter (\<lambda>(e, f). f=c \<and> True) (kraus_family_comp_dependent t (s d))) (\<rho> d))\<close>
    by (simp add: kraus_family_map'_def kraus_family_filter_map_outcome case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. kraus_family_map (kraus_family_comp_dependent (\<lambda>e. kraus_family_filter (\<lambda>f. f = c) (t e)) (s d)) (\<rho> d))\<close>
    apply (subst kraus_family_filter_comp_dependent)
    using bdd_t by simp_all
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>(F, f)\<in>Rep_kraus_family (s d). kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d)))\<close>
    using bdd'
    by (simp add: kraus_family_comp_dependent_apply kraus_family_map'_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>(f, F)\<in>prod.swap ` Rep_kraus_family (s d). kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d)))\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>(f, F)\<in>(SIGMA f:UNIV. {F. (F, f) \<in> Rep_kraus_family (s d)}). kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d)))\<close>
    apply (rule infsum_cong)
    apply (rule arg_cong[where f=\<open>infsum _\<close>])
    by fastforce
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>f. \<Sum>\<^sub>\<infinity>F\<in>{F. (F,f) \<in> Rep_kraus_family (s d)}. kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d)))\<close>
    apply (rule infsum_cong)
    apply (subst infsum_Sigma_positive_tc)
    using assms by (auto intro!: summ3 kraus_family_map'_pos sandwich_tc_pos
        summable_on_bounded_linear[where h=\<open>kraus_family_map' _ _\<close>]
        bounded_clinear.bounded_linear kraus_family_map'_bounded_clinear)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>f. kraus_family_map' {c} (t f) (\<Sum>\<^sub>\<infinity>F\<in>{F. (F,f) \<in> Rep_kraus_family (s d)}. sandwich_tc F (\<rho> d)))\<close>
    apply (intro infsum_cong)
    apply (rule infsum_bounded_linear[unfolded o_def])
    by (auto intro!: bounded_clinear.bounded_linear kraus_family_map'_bounded_clinear summ3)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>f. kraus_family_map' {c} (t f) (kraus_family_map' {f} (s d) (\<rho> d)))\<close>
    apply (auto intro!: infsum_cong arg_cong[where f=\<open>kraus_family_map' _ _\<close>]
        simp: kraus_family_map'_def kraus_family_map.rep_eq kraus_family_filter.rep_eq)
    apply (subst infsum_reindex[OF inj, symmetric, unfolded o_def])
    by (auto intro!: arg_cong[where f=\<open>sandwich_tc _\<close>] arg_cong[where f=\<open>infsum _\<close>]
        simp: image_iff Bex_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>f. \<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (t f) (kraus_family_map' {f} (s d) (\<rho> d)))\<close>
    apply (rule infsum_swap_positive_tc)
    using assms
    by (auto intro!: summ4 summ2 summable_on_bounded_linear[where h=\<open>kraus_family_map' _ _\<close>]
        bounded_clinear.bounded_linear kraus_family_map'_bounded_clinear kraus_family_map'_pos simp: )
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>f. kraus_family_map' {c} (t f) (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {f} (s d) (\<rho> d)))\<close>
    apply (intro infsum_cong)
    apply (rule infsum_bounded_linear[unfolded o_def])
    by (auto intro!: bounded_clinear.bounded_linear kraus_family_map'_bounded_clinear summ2)
  finally  show \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome snd (kraus_family_comp_dependent t (s d))) (\<rho> d)) =
       (\<Sum>\<^sub>\<infinity>f. kraus_family_map' {c} (t f) (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {f} (s d) (\<rho> d)))\<close>
    by -
qed


lemma cq_map_seq_id_right[simp]: \<open>cq_map_seq s cq_map_id = s\<close>
  apply (rule cq_map_eqI)
  by (simp add: cq_map_apply_seq)

lemma cq_map_seq_id_left[simp]: \<open>cq_map_seq cq_map_id s = s\<close>
  apply (rule cq_map_eqI)
  by (simp add: cq_map_apply_seq)


lift_definition cq_map_if :: \<open>('cl1 \<Rightarrow> bool) \<Rightarrow> ('cl1,'qu1,'cl2,'qu2) cq_map \<Rightarrow> ('cl1,'qu1,'cl2,'qu2) cq_map \<Rightarrow> ('cl1,'qu1,'cl2,'qu2) cq_map\<close> is
  \<open>\<lambda>e p q c. if e c then p c else q c\<close>
  by (simp add: cq_map_rel_def)

lift_definition cq_map_quantum_op :: \<open>('cl \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'x) kraus_family) \<Rightarrow> ('cl,'qu1,'cl,'qu2) cq_map\<close> is
  \<open>\<lambda>(\<EE>::'cl \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'x) kraus_family) c. 
      kraus_family_map_outcome (\<lambda>_. c) (if kraus_family_norm (\<EE> c) \<le> 1 then \<EE> c else 0)\<close>
  by (simp add: cq_map_rel_def)

definition cq_map_of_op :: \<open>'qu1 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'qu2 ell2 \<Rightarrow> ('cl, 'qu1, 'cl, 'qu2) cq_map\<close> where
  \<open>cq_map_of_op U = cq_map_quantum_op (\<lambda>_. kraus_family_of_op U)\<close>


end
