theory CQ_Operators
  imports Kraus_Maps.Kraus_Maps Registers2.Missing_Bounded_Operators Registers2.Quantum_Registers
    Registers2.Registers_Unsorted
begin

unbundle kraus_map_syntax

(* type_synonym ('c,'q) cq_operator = \<open>(('c\<times>'q) ell2, ('c\<times>'q) ell2) trace_class\<close>
type_synonym ('c1,'q1,'c2,'q2) cq_map = \<open>('c1,'q1) cq_operator \<Rightarrow> ('c2,'q2) cq_operator\<close>
type_synonym ('c,'q) cq_map2 = \<open>('c,'q,'c,'q) cq_map\<close> *)

(* TODO move *)
lift_definition kf_apply_qregister :: \<open>('a,'b) qregister \<Rightarrow> ('a ell2, 'a ell2, 'x) kraus_family \<Rightarrow> ('b ell2, 'b ell2, 'x) kraus_family\<close> is
  \<open>\<lambda>(Q :: ('a,'b) qregister). image (\<lambda>(E,x). (apply_qregister Q E, x))\<close>
proof (rule CollectI, erule CollectE, rename_tac Q E)
  fix Q :: \<open>('a,'b) qregister\<close> and E :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2 \<times> 'x) set\<close>
  assume \<open>kraus_family E\<close>
  show \<open>kraus_family ((\<lambda>(E, y). (apply_qregister Q E, y)) ` E)\<close>
  proof -
    wlog [simp]: \<open>qregister Q\<close> goal \<open>kraus_family ((\<lambda>(E, y). (apply_qregister Q E, y)) ` E)\<close>
      using negation
      by (auto intro!: kraus_familyI_0 simp: non_qregister)
    from \<open>kraus_family E\<close> obtain B where B: \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>finite F\<close> and \<open>F \<subseteq> E\<close> for F
      by (auto simp: kraus_family_def bdd_above_def)
    have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> apply_qregister Q B\<close>
      if \<open>finite F\<close> and \<open>F \<subseteq> (\<lambda>(E, y). (apply_qregister Q E, y)) ` E\<close> for F
    proof -
      from that
      obtain G where FG: \<open>F = (\<lambda>(E, y). (apply_qregister Q E, y)) ` G\<close> and \<open>finite G\<close> and \<open>G \<subseteq> E\<close>
        by (meson finite_subset_image)
      have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) = (\<Sum>(E, x)\<in>(\<lambda>(E, y). (apply_qregister Q E, y)) ` G. E* o\<^sub>C\<^sub>L E)\<close>
        using FG by force
      also have \<open>\<dots> = (\<Sum>(E, x)\<in>G. apply_qregister Q (E* o\<^sub>C\<^sub>L E))\<close>
        apply (subst sum.reindex)
        by (auto intro!: inj_onI simp: case_prod_unfold qregister_compose apply_qregister_adj apply_qregister_inject')
      also have \<open>\<dots> = apply_qregister Q (\<Sum>(E, x)\<in>G. E* o\<^sub>C\<^sub>L E)\<close>
        apply (subst complex_vector.linear_sum[where f=\<open>apply_qregister Q\<close>]) 
        by (simp_all add: case_prod_beta)
      also have \<open>\<dots> \<le> apply_qregister Q B\<close>
        using \<open>qregister Q\<close> apply (rule apply_qregister_mono[THEN iffD2])
        using \<open>finite G\<close> and \<open>G \<subseteq> E\<close> by (rule B)
      finally show ?thesis
        by -
    qed
    then show ?thesis
      by (auto intro!: bdd_aboveI simp: kraus_family_def)
  qed
qed

lemma kf_apply_qregister_invalid_weak:
  assumes \<open>\<not> qregister Q\<close>
  shows \<open>kf_apply_qregister Q \<EE> =\<^sub>k\<^sub>r 0\<close>
  unfolding kf_eq_weak_def
  apply (transfer' fixing: Q)
  using assms
  by (auto intro!: ext infsum_0 simp add: non_qregister case_prod_beta)

lemma kf_apply_qregister_invalid:
  assumes \<open>\<not> qregister Q\<close>
  shows \<open>kf_apply_qregister Q \<EE> \<equiv>\<^sub>k\<^sub>r 0\<close>
  by (simp add: assms kf_apply_qregister_invalid_weak kf_eq_weak0_imp_kf_eq0)

lemma bij_iso_qregister:
  assumes \<open>iso_qregister Q\<close>
  shows \<open>bij (apply_qregister Q)\<close>
  using Laws_Quantum.iso_register_bij assms iso_qregister.rep_eq by blast

lemma apply_qregister_tc_plus:
  \<open>apply_qregister_tc Q (t + u) = apply_qregister_tc Q t + apply_qregister_tc Q u\<close>
    apply transfer'
    by (simp add: apply_qregister_plus)

lemma apply_qregister_tc_scale:
  \<open>apply_qregister_tc Q (c *\<^sub>C t) = c *\<^sub>C apply_qregister_tc Q t\<close>
    apply transfer'
    by (simp add: apply_qregister_plus apply_qregister_scaleC)

lemma bounded_clinear_apply_qregister_tc[bounded_clinear]:
  assumes \<open>iso_qregister Q\<close>
    \<comment> \<open>This assumption is actually not needed\<close>
  shows \<open>bounded_clinear (apply_qregister_tc Q)\<close>
  apply (rule bounded_clinearI[where K=1])
  by (simp_all add: assms apply_iso_qregister_tc_norm apply_qregister_tc_scale apply_qregister_tc_plus)

lemma clinear_apply_qregister_tc:
  shows \<open>clinear (apply_qregister_tc Q)\<close>
  apply (rule clinearI)
  by (simp_all add: apply_qregister_tc_scale apply_qregister_tc_plus)

lemma bij_iso_qregister_tc:
  assumes \<open>iso_qregister Q\<close>
  shows \<open>bij (apply_qregister_tc Q)\<close>
proof (rule bijI)
  have \<open>qregister Q\<close>
    using assms iso_qregister_def' by blast
  then show \<open>inj (apply_qregister_tc Q)\<close>
    by (smt (verit) apply_qregister_inject' apply_qregister_tc.rep_eq assms from_trace_class_inverse inj_onI
        iso_qregister_co_dim)
  show \<open>surj (apply_qregister_tc Q)\<close>
    apply (rule surjI[where f=\<open>apply_qregister_tc (qregister_inv Q)\<close>])
    by (smt (verit, ccfv_SIG) apply_qregister_inv_inverse apply_qregister_tc.rep_eq assms from_trace_class_inverse iso_qregister_co_dim
        iso_qregister_inv_iso)
qed


lemma separating_set_bounded_clinear_iso_qregister_tc_nested:
  fixes Q :: \<open>('a,'b) qregister\<close> and S :: \<open>('a ell2, 'a ell2) trace_class set\<close>
  assumes \<open>iso_qregister Q\<close>
  assumes \<open>separating_set (bounded_clinear :: (_\<Rightarrow>'c::complex_normed_vector) \<Rightarrow> _) S\<close>
  shows \<open>separating_set (bounded_clinear :: (_\<Rightarrow>'c::complex_normed_vector) \<Rightarrow> _) (apply_qregister_tc Q ` S)\<close>
proof (intro separating_setI)
  fix f g :: \<open>('b ell2, 'b ell2) trace_class \<Rightarrow> 'c\<close>
  assume \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close>
  assume fg_QS: \<open>f u = g u\<close> if \<open>u \<in> apply_qregister_tc Q ` S\<close> for u
  define f' g' where \<open>f' t = f (apply_qregister_tc Q t)\<close> and \<open>g' t = g (apply_qregister_tc Q t)\<close> for t
  have [iff]: \<open>bounded_clinear f'\<close>  \<open>bounded_clinear g'\<close>
    by (auto intro!: 
        comp_bounded_clinear[OF \<open>bounded_clinear f\<close>, unfolded o_def]
        comp_bounded_clinear[OF \<open>bounded_clinear g\<close>, unfolded o_def] 
        bounded_clinear_apply_qregister_tc assms
        simp: f'_def[abs_def] g'_def[abs_def])
  have \<open>f' t = g' t\<close> if \<open>t \<in> S\<close> for t
    by (simp add: f'_def fg_QS g'_def that)
  then have \<open>f' = g'\<close>
    apply (rule_tac eq_from_separatingI[OF assms(2)])
    by auto
  show \<open>f = g\<close>
  proof (rule ext)
    fix t :: \<open>('b ell2, 'b ell2) trace_class\<close>
    from assms have surj_Q: \<open>surj (apply_qregister_tc Q)\<close>
      by (meson bij_def bij_iso_qregister_tc)
    then obtain u where u: \<open>t = apply_qregister_tc Q u\<close>
      by fast
    with \<open>f' = g'\<close>
    have \<open>f' u = g' u\<close>
      by simp
    then show \<open>f t = g t\<close>
      by (simp add: f'_def g'_def u)
  qed
qed

lemma separating_set_bounded_clinear_apply_qregister_tensor_tc:
  assumes \<open>iso_qregister Q\<close>
  shows \<open>separating_set bounded_clinear ((\<lambda>(\<rho>, \<sigma>). apply_qregister_tc Q (tc_tensor \<rho> \<sigma>)) ` (UNIV \<times> UNIV))\<close>
  using separating_set_bounded_clinear_iso_qregister_tc_nested[OF assms(1) separating_set_bounded_clinear_tc_tensor]
  by (simp add: image_image case_prod_unfold)

lemma separating_set_bounded_clinear_apply_qregister_tensor_tc_nested:
  assumes \<open>iso_qregister Q\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) A\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) ((\<lambda>(\<rho>,\<sigma>). apply_qregister_tc Q (tc_tensor \<rho> \<sigma>)) ` (A \<times> B))\<close>
  using separating_set_bounded_clinear_iso_qregister_tc_nested[OF assms(1) separating_set_bounded_clinear_tc_tensor_nested,
      OF assms(2) assms(3)]
  by (simp add: image_image case_prod_unfold)

lemma kf_apply_qregister_apply_on_tensor:
  assumes \<open>qcomplements Q R\<close>
  shows \<open>kf_apply_qregister Q \<EE> *\<^sub>k\<^sub>r @X apply_qregister_tc \<lbrakk>Q, R\<rbrakk>\<^sub>q (tc_tensor t u)
      = apply_qregister_tc \<lbrakk>Q, R\<rbrakk>\<^sub>q (tc_tensor (\<EE> *\<^sub>k\<^sub>r @X t) u)\<close>
proof -
  have \<open>iso_qregister \<lbrakk>Q, R\<rbrakk>\<^sub>q\<close>
    using assms qcomplements_def' by blast
  then have \<open>qregister Q\<close>
    using distinct_qvarsL iso_qregister_def' by blast

  have blin: \<open>bounded_linear (\<lambda>x. apply_qregister_tc \<lbrakk>Q,R\<rbrakk>\<^sub>q (tc_tensor x u))\<close>
    apply (rule bounded_clinear.bounded_linear)
    by (intro bounded_linear_intros \<open>iso_qregister \<lbrakk>Q, R\<rbrakk>\<^sub>q\<close>)
  from kf_apply_summable[of _ \<open>kf_filter (\<lambda>x. x\<in>X) \<EE>\<close>]
  have sum: \<open>(\<lambda>(E, x). sandwich_tc E t) summable_on Set.filter (\<lambda>(E, y). y \<in> X) (Rep_kraus_family \<EE>)\<close>
    by (simp add: kf_filter.rep_eq)

  define tu QRtu where \<open>tu = tc_tensor t u\<close> and \<open>QRtu = apply_qregister_tc \<lbrakk>Q, R\<rbrakk>\<^sub>q tu\<close>
  have \<open>kf_apply_qregister Q \<EE> *\<^sub>k\<^sub>r @X QRtu
       = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Set.filter (\<lambda>(E, y). y \<in> X) ((\<lambda>(E, y). (apply_qregister Q E, y)) ` Rep_kraus_family \<EE>). sandwich_tc E QRtu)\<close>
    unfolding kf_apply_on_def
    apply (transfer' fixing: Q QRtu X)
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>(\<lambda>(E, y). (apply_qregister Q E, y)) ` Set.filter (\<lambda>(E, y). y \<in> X) (Rep_kraus_family \<EE>). sandwich_tc E QRtu)\<close>
    apply (rule arg_cong2[where f=infsum])
    by force+
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Set.filter (\<lambda>(E, y). y \<in> X) (Rep_kraus_family \<EE>). sandwich_tc (apply_qregister Q E) QRtu)\<close>
    apply (subst infsum_reindex)
    using \<open>qregister Q\<close>
    by (auto intro!: inj_onI simp: o_def case_prod_unfold apply_qregister_inject')
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Set.filter (\<lambda>(E, y). y \<in> X) (Rep_kraus_family \<EE>). apply_qregister_tc \<lbrakk>Q,R\<rbrakk>\<^sub>q (sandwich_tc (E \<otimes>\<^sub>o id_cblinfun) tu))\<close>
    apply (rule infsum_cong)
    apply (simp add: case_prod_unfold QRtu_def)
    by (metis apply_qregister_extend_pair_right apply_qregister_tc_sandwich assms iso_qregister_def' qcomplements_def')
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Set.filter (\<lambda>(E, y). y \<in> X) (Rep_kraus_family \<EE>). apply_qregister_tc \<lbrakk>Q,R\<rbrakk>\<^sub>q (tc_tensor (sandwich_tc E t) u))\<close>
    apply (rule infsum_cong)
    by (simp add: case_prod_unfold tu_def sandwich_tc_tensor)
  also have \<open>\<dots> = apply_qregister_tc \<lbrakk>Q,R\<rbrakk>\<^sub>q (tc_tensor (\<Sum>\<^sub>\<infinity>(E,x)\<in>Set.filter (\<lambda>(E, y). y \<in> X) (Rep_kraus_family \<EE>). (sandwich_tc E t)) u)\<close>
    apply (subst infsum_bounded_linear[where h=\<open>\<lambda>x. apply_qregister_tc \<lbrakk>Q,R\<rbrakk>\<^sub>q (tc_tensor x u)\<close>, symmetric])
    using  blin sum by (simp_all add: case_prod_unfold)
  also have \<open>\<dots> = apply_qregister_tc \<lbrakk>Q,R\<rbrakk>\<^sub>q (tc_tensor (\<EE> *\<^sub>k\<^sub>r @X t) u)\<close>
    unfolding kf_apply_on_def
    apply (transfer' fixing: Q QRtu x)
    by (simp add: case_prod_unfold)
  finally show ?thesis
    by (simp add: QRtu_def tu_def)
qed

lemma kf_apply_qregister_apply_tensor:
  assumes \<open>qcomplements Q R\<close>
  shows \<open>kf_apply_qregister Q \<EE> *\<^sub>k\<^sub>r apply_qregister_tc \<lbrakk>Q, R\<rbrakk>\<^sub>q (tc_tensor t u)
      = apply_qregister_tc \<lbrakk>Q, R\<rbrakk>\<^sub>q (tc_tensor (\<EE> *\<^sub>k\<^sub>r t) u)\<close>
  using kf_apply_qregister_apply_on_tensor[OF assms, of \<EE> UNIV]
  by simp

lemma kf_apply_qregister_cong:
  assumes \<open>\<EE> \<equiv>\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_apply_qregister Q \<EE> \<equiv>\<^sub>k\<^sub>r kf_apply_qregister Q \<FF>\<close>
proof -
  wlog \<open>qregister Q\<close>
    by (auto intro!: kf_eqI simp add: kf_apply_on_eq0I kf_apply_qregister_invalid_weak negation)
  from qcomplement_exists[OF this]
  have \<open>let 'g::type = qregister_decomposition_basis Q in kf_apply_qregister Q \<EE> \<equiv>\<^sub>k\<^sub>r kf_apply_qregister Q \<FF>\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>G::('g, 'c) qregister. qcomplements Q G\<close>
    then obtain G :: \<open>('g, 'c) qregister\<close> where \<open>qcomplements Q G\<close>
      by auto
    then have iso: \<open>iso_qregister \<lbrakk>Q,G\<rbrakk>\<^sub>q\<close>
      by (simp add: qcomplements_def')
    have \<open>kf_apply_qregister Q \<EE> *\<^sub>k\<^sub>r @{x} apply_qregister_tc \<lbrakk>Q, G\<rbrakk>\<^sub>q (tc_tensor t u)
        = kf_apply_qregister Q \<FF> *\<^sub>k\<^sub>r @{x} apply_qregister_tc \<lbrakk>Q, G\<rbrakk>\<^sub>q (tc_tensor t u)\<close> for x t u
      apply (simp add: kf_apply_qregister_apply_on_tensor \<open>qcomplements Q G\<close>)
      using assms kf_apply_on_eqI by fastforce
    then have \<open>kf_apply_qregister Q \<EE> *\<^sub>k\<^sub>r @{x} \<rho> = kf_apply_qregister Q \<FF> *\<^sub>k\<^sub>r @{x} \<rho>\<close> for x \<rho>
      apply (rule_tac eq_from_separatingI2x[OF separating_set_bounded_clinear_apply_qregister_tensor_tc, where x=\<rho>])
         apply (rule iso)
        apply (rule kf_apply_on_bounded_clinear)
       apply (rule kf_apply_on_bounded_clinear)
      by assumption
    then show \<open>kf_apply_qregister Q \<EE> \<equiv>\<^sub>k\<^sub>r kf_apply_qregister Q \<FF>\<close>
      by (rule kf_eqI)
  qed
  from this[cancel_with_type]
  show \<open>kf_apply_qregister Q \<EE> \<equiv>\<^sub>k\<^sub>r kf_apply_qregister Q \<FF>\<close>
    by -
qed

lemma kf_apply_qregister_cong_weak:
  assumes \<open>\<EE> =\<^sub>k\<^sub>r \<FF>\<close>
  shows \<open>kf_apply_qregister Q \<EE> =\<^sub>k\<^sub>r kf_apply_qregister Q \<FF>\<close>
proof -
  wlog \<open>qregister Q\<close>
    by (metis hypothesis kf_apply_qregister_invalid_weak kf_eq_weak_def)
  from qcomplement_exists[OF this]
  have \<open>let 'g::type = qregister_decomposition_basis Q in kf_apply_qregister Q \<EE> =\<^sub>k\<^sub>r kf_apply_qregister Q \<FF>\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>G::('g, 'd) qregister. qcomplements Q G\<close>
    then obtain G :: \<open>('g, 'd) qregister\<close> where \<open>qcomplements Q G\<close>
      by auto
    then have iso: \<open>iso_qregister \<lbrakk>Q,G\<rbrakk>\<^sub>q\<close>
      by (simp add: qcomplements_def')
    have \<open>kf_apply_qregister Q \<EE> *\<^sub>k\<^sub>r apply_qregister_tc \<lbrakk>Q, G\<rbrakk>\<^sub>q (tc_tensor t u)
        = kf_apply_qregister Q \<FF> *\<^sub>k\<^sub>r apply_qregister_tc \<lbrakk>Q, G\<rbrakk>\<^sub>q (tc_tensor t u)\<close> for t u
      apply (simp add: kf_apply_qregister_apply_tensor \<open>qcomplements Q G\<close>)
      using assms kf_eq_weak_def by force
    then have \<open>kf_apply_qregister Q \<EE> *\<^sub>k\<^sub>r \<rho> = kf_apply_qregister Q \<FF> *\<^sub>k\<^sub>r \<rho>\<close> for x \<rho>
      apply (rule_tac eq_from_separatingI2x[OF separating_set_bounded_clinear_apply_qregister_tensor_tc, where x=\<rho>])
         apply (rule iso)
        apply (rule kf_apply_bounded_clinear)
       apply (rule kf_apply_bounded_clinear)
      by assumption
    then show \<open>kf_apply_qregister Q \<EE> =\<^sub>k\<^sub>r kf_apply_qregister Q \<FF>\<close>
      by (rule kf_eq_weakI)
  qed
  from this[cancel_with_type]
  show \<open>kf_apply_qregister Q \<EE> =\<^sub>k\<^sub>r kf_apply_qregister Q \<FF>\<close>
    by -
qed


definition km_some_kraus_family :: \<open>(('a::chilbert_space, 'a) trace_class \<Rightarrow> ('b::chilbert_space, 'b) trace_class) \<Rightarrow> ('a, 'b, unit) kraus_family\<close> where
  \<open>km_some_kraus_family \<EE> = (SOME \<FF>. \<EE> = kf_apply \<FF>)\<close>

lemma kf_apply_km_some_kraus_family[simp]:
  assumes \<open>kraus_map \<EE>\<close>
  shows \<open>kf_apply (km_some_kraus_family \<EE>) = \<EE>\<close>
  unfolding km_some_kraus_family_def
  apply (rule someI2_ex)
  using assms kraus_map_def by auto

definition km_apply_qregister :: \<open>('a,'b) qregister \<Rightarrow> (('a ell2, 'a ell2) trace_class \<Rightarrow> ('a ell2, 'a ell2) trace_class) \<Rightarrow> (('b ell2, 'b ell2) trace_class \<Rightarrow> ('b ell2, 'b ell2) trace_class)\<close> where
  \<open>km_apply_qregister Q \<EE> = kf_apply (kf_apply_qregister Q (km_some_kraus_family \<EE> :: (_,_,unit) kraus_family))\<close>

lemma km_apply_qregister_kf_apply:
  assumes \<open>qregister Q\<close>
  shows \<open>km_apply_qregister Q (kf_apply \<EE>) = kf_apply (kf_apply_qregister Q \<EE>)\<close>
  by (auto intro!: ext kf_apply_eqI kf_apply_qregister_cong_weak simp: kf_eq_weak_def km_apply_qregister_def)

lemma km_apply_qregister_invalid: \<open>km_apply_qregister Q \<EE> = 0\<close> if \<open>\<not> qregister Q\<close>
  by (auto intro!: kf_apply_eq0I ext simp add: km_apply_qregister_def that kf_apply_qregister_invalid_weak)

lift_definition kf_annotate :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a, 'b, ('x \<times> 'a\<Rightarrow>\<^sub>C\<^sub>L'b)) kraus_family\<close> is
  \<open>\<lambda>\<EE> :: ('a\<Rightarrow>\<^sub>C\<^sub>L'b \<times> 'x) set. (\<lambda>(E,x). (E,(x,E))) ` \<EE>\<close>
proof (rule CollectI)
  fix \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x) set\<close>
  assume \<open>\<EE> \<in> Collect kraus_family\<close>
  then have \<open>(\<lambda>(E, x). Abs_cblinfun_wot (E* o\<^sub>C\<^sub>L E)) summable_on \<EE>\<close>
    by (simp add: kraus_family_iff_summable')
  then have \<open>(\<lambda>(E, x). Abs_cblinfun_wot (E* o\<^sub>C\<^sub>L E)) summable_on (\<lambda>(E, x). (E, x, E)) ` \<EE>\<close>
      apply (subst summable_on_reindex)
      by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  then show \<open>kraus_family ((\<lambda>(E, x). (E, x, E)) ` \<EE>)\<close>
    by (simp add: kraus_family_iff_summable')
qed

lemma kf_annotate_eq_weak: \<open>kf_annotate \<EE> =\<^sub>k\<^sub>r \<EE>\<close>
  apply (rule kf_eq_weakI)
  unfolding kf_apply.rep_eq kf_annotate.rep_eq
  apply (subst infsum_reindex)
  by (auto intro!: inj_onI simp: o_def case_prod_unfold)

lemma kf_filter_kf_apply_qregister:
  \<open>kf_filter P (kf_apply_qregister Q \<EE>) = kf_apply_qregister Q (kf_filter P \<EE>)\<close>
  apply (transfer' fixing: Q)
  by force

lemma kf_map_inj_kr_eq_weak:
  assumes \<open>inj_on f (kf_domain \<EE>)\<close>
  shows \<open>kf_map_inj f \<EE> =\<^sub>k\<^sub>r \<EE>\<close>
  by (simp add: assms kf_eq_weakI)


lemma kf_apply_qregister_pair_tensor_id_weak:
  assumes \<open>qcompatible Q R\<close>
  shows \<open>kf_apply_qregister \<lbrakk>Q,R\<rbrakk>\<^sub>q (kf_tensor \<EE> kf_id) =\<^sub>k\<^sub>r kf_apply_qregister Q \<EE>\<close>
    (is ?goal)
proof -
  define QR where \<open>QR = \<lbrakk>Q,R\<rbrakk>\<^sub>q\<close>
  with assms have \<open>qregister QR\<close>
    by blast
  have [simp]: \<open>apply_qregister QR (a \<otimes>\<^sub>o id_cblinfun) = apply_qregister Q a\<close> for a
    by (metis QR_def apply_qregister_extend_pair_right assms)
  have \<open>kf_apply_qregister QR (kf_tensor \<EE> kf_id) =\<^sub>k\<^sub>r kf_apply_qregister QR (kf_tensor_raw \<EE> kf_id)\<close>
    apply (rule kf_apply_qregister_cong_weak)
    by (simp add: kf_eq_weak_def kf_tensor_def)
  also have \<open>\<dots> = kf_map_inj (\<lambda>(x,E). (E, id_cblinfun, x, ())) (kf_apply_qregister Q (kf_annotate \<EE>))\<close>
    apply (rule Rep_kraus_family_inject[THEN iffD1])
    apply (simp add: kf_apply_qregister.rep_eq kf_tensor_raw.rep_eq kf_of_op.rep_eq
        image_image kf_map_inj.rep_eq case_prod_beta kf_annotate.rep_eq
        flip: kf_of_op_id )
    by force
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_apply_qregister Q (kf_annotate \<EE>)\<close>
    unfolding kf_eq_weak_def kf_apply_map_inj
    apply (rule ext)
    apply (subst kf_apply_map_inj)
    by (auto simp: inj_on_def case_prod_unfold)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_apply_qregister Q \<EE>\<close>
    apply (rule kf_apply_qregister_cong_weak)
    by (rule kf_annotate_eq_weak)
  finally show ?thesis
    by (simp add: QR_def)
qed

lemma kf_apply_qregister_pair_tensor_id:
  assumes \<open>qcompatible Q R\<close>
  shows \<open>kf_apply_qregister \<lbrakk>Q,R\<rbrakk>\<^sub>q (kf_tensor \<EE> kf_id) \<equiv>\<^sub>k\<^sub>r kf_map_inj (\<lambda>x. (x,())) (kf_apply_qregister Q \<EE>)\<close>
proof (rule kf_eqI_from_filter_eq_weak)
  fix xy :: \<open>'d \<times> unit\<close>
  define x y where \<open>x = fst xy\<close> and \<open>y = snd xy\<close> 
  then have xy: \<open>xy = (x,y)\<close>
    using surjective_pairing by blast
  have \<open>kf_filter ((=) xy) (kf_apply_qregister \<lbrakk>Q, R\<rbrakk>\<^sub>q (kf_tensor \<EE> kf_id)) =\<^sub>k\<^sub>r
        kf_apply_qregister \<lbrakk>Q, R\<rbrakk>\<^sub>q (kf_filter (\<lambda>(x',y'). (x=x') \<and> True) (kf_tensor \<EE> kf_id))\<close>
    apply (simp add: kf_filter_kf_apply_qregister xy)
    by (smt (verit, del_insts) kf_eqI_from_filter_eq_weak kf_eq_weak_def kf_filter_cong_weak kf_filter_kf_apply_qregister
        old.unit.exhaust prod.expand prod.sel(1) split_def)
  also have \<open>\<dots> = kf_apply_qregister \<lbrakk>Q, R\<rbrakk>\<^sub>q (kf_tensor (kf_filter ((=) x) \<EE>) kf_id)\<close>
    apply (subst kf_filter_tensor)
    by simp
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_apply_qregister Q (kf_filter ((=) x) \<EE>)\<close>
    by (simp add: assms kf_apply_qregister_pair_tensor_id_weak)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_map_inj (\<lambda>x. (x, ())) (kf_apply_qregister Q (kf_filter ((=) x) \<EE>))\<close>
    apply (rule kf_eq_weak_sym)
    apply (rule kf_map_inj_kr_eq_weak)
    by (auto intro!: inj_onI)
  also have \<open>\<dots> = kf_filter ((=) xy) (kf_map_inj (\<lambda>x. (x, ())) (kf_apply_qregister Q \<EE>))\<close>
    by (simp add: kf_filter_map_inj kf_filter_kf_apply_qregister xy)
  finally show \<open>kf_filter ((=) xy) (kf_apply_qregister \<lbrakk>Q, R\<rbrakk>\<^sub>q (kf_tensor \<EE> kf_id)) =\<^sub>k\<^sub>r
        kf_filter ((=) xy) (kf_map_inj (\<lambda>x. (x, ())) (kf_apply_qregister Q \<EE>))\<close>
    by -
qed

lemma iso_qregister_chain[iff]:
  assumes \<open>iso_qregister F\<close> and \<open>iso_qregister G\<close>
  shows \<open>iso_qregister (qregister_chain F G)\<close>
proof -
  have [iff]: \<open>qregister F\<close>
    using assms(1) iso_qregister_def' by blast
  have [iff]: \<open>qregister G\<close>
    using assms(2) iso_qregister_def' by blast
  have [iff]: \<open>qregister (qregister_inv F)\<close>
    using assms(1) iso_qregister_def' iso_qregister_inv_iso by blast
  have [iff]: \<open>qregister (qregister_inv G)\<close>
    using assms(2) iso_qregister_def' iso_qregister_inv_iso by blast
  have 1: \<open>qregister_chain (qregister_chain F G) (qregister_chain (qregister_inv G) (qregister_inv F)) = qregister_id\<close>
    apply (subst qregister_chain_assoc)
    apply (subst (2) qregister_chain_assoc[symmetric])
    using assms by (simp add: iso_qregister_chain_inv)
  have 2: \<open>qregister_chain (qregister_chain (qregister_inv G) (qregister_inv F)) (qregister_chain F G) = qregister_id\<close>
    using "1" qregister_left_right_inverse by blast

  show ?thesis
  using assms 1 2
  by (auto intro!: exI[of _ \<open>qregister_chain (qregister_inv G) (qregister_inv F)\<close>] simp add: iso_qregister_def')
qed



lemma qregister_chain_apply_tc:
  assumes \<open>iso_qregister F\<close> and \<open>iso_qregister G\<close>
  shows \<open>apply_qregister_tc (qregister_chain F G) = apply_qregister_tc F o apply_qregister_tc G\<close>
  apply (transfer' fixing: F G)
  using assms
  by (simp add: iso_qregister_co_dim)

lemma apply_qregister_tc_id[simp]: \<open>apply_qregister_tc qregister_id = id\<close>
  apply transfer'
  by (simp add: iso_qregister_co_dim iso_qregister_def')


lemma kf_apply_qregister_iso_qregister_explicit:
  assumes \<open>iso_qregister Q\<close>
  shows \<open>kf_apply_qregister Q \<EE> *\<^sub>k\<^sub>r \<rho> = apply_qregister_tc Q (\<EE> *\<^sub>k\<^sub>r apply_qregister_tc (qregister_inv Q) \<rho>)\<close>
proof -
  define q q1 where \<open>q = apply_qregister_tc Q\<close> and \<open>q1 = apply_qregister_tc (qregister_inv Q)\<close>
  have q1q: \<open>q1 (q t) = t\<close> for t
    unfolding q1_def q_def 
    apply (subst qregister_chain_apply_tc[symmetric, unfolded o_def, THEN fun_cong])
    using assms by (auto simp add: iso_qregister_inv_iso iso_qregister_inv_chain) 
  have qq1: \<open>q (q1 t) = t\<close> for t
    by (metis UNIV_I q1q assms bij_betw_iff_bijections bij_iso_qregister_tc q_def)

  have [iff]: \<open>bounded_linear q\<close>
    by (simp add: q_def assms bounded_clinear.bounded_linear bounded_clinear_apply_qregister_tc)
  have [iff]: \<open>bounded_linear q1\<close>
    by (simp add: assms bounded_clinear.bounded_linear bounded_clinear_apply_qregister_tc iso_qregister_inv_iso q1_def)

  have \<open>kf_apply_qregister Q \<EE> *\<^sub>k\<^sub>r \<rho> = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>(E, x). (apply_qregister Q E, x)) ` Rep_kraus_family \<EE>. sandwich_tc (fst E) \<rho>)\<close>
    by (simp add: kf_apply.rep_eq kf_apply_qregister.rep_eq)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. sandwich_tc (apply_qregister Q E) \<rho>)\<close>
    apply (subst infsum_reindex)
     apply (smt (verit) apply_qregister_inv_inverse assms case_prod_unfold inj_onI prod.collapse prod.inject) 
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. sandwich_tc (apply_qregister Q E) (q (q1 \<rho>)))\<close>
    by (simp add: qq1)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. q (sandwich_tc E (q1 \<rho>)))\<close>
    by (metis apply_qregister_tc_sandwich q_def)
  also have \<open>\<dots> = q (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. sandwich_tc E (q1 \<rho>))\<close>
    apply (subst infsum_bounded_linear_invertible[where h=q and h'=q1, symmetric])
    by (auto intro!: simp: case_prod_unfold o_def q1q)
  also have \<open>\<dots> = q (\<EE> *\<^sub>k\<^sub>r q1 \<rho>)\<close>
    by (metis (no_types, lifting) infsum_cong kf_apply.rep_eq split_def)
  finally show ?thesis
    by (simp add: q1_def q_def)
qed

definition cq_id :: \<open>('c,'a) qregister \<Rightarrow> (('a ell2, 'a ell2) trace_class \<Rightarrow> ('a ell2, 'a ell2) trace_class)\<close> where
  \<open>cq_id C = km_apply_qregister C (km_complete_measurement (range ket))\<close>

definition classical_on :: \<open>('c,'a) qregister \<Rightarrow> ('a ell2, 'a ell2) trace_class \<Rightarrow> bool\<close> where
  \<open>classical_on C \<rho> \<longleftrightarrow> cq_id C \<rho> = \<rho>\<close>

(* lemma \<open>classical_fst \<rho> \<longleftrightarrow> classical_on qFst \<rho>\<close>
  apply (simp add: classical_on_def classical_fst_def)
  by x *)

definition cq_operator_reconstruct :: \<open>('c\<times>'q, 'r) qregister \<Rightarrow> ('c \<Rightarrow> ('q ell2, 'q ell2) trace_class) \<Rightarrow> ('r ell2, 'r ell2) trace_class\<close> where
  \<open>cq_operator_reconstruct Q \<rho> = (\<Sum>\<^sub>\<infinity>c. apply_qregister_tc Q (tc_tensor (tc_butterfly (ket c) (ket c)) (\<rho> c)))\<close>

definition cq_operator_at :: \<open>('c\<times>'q, 'r) qregister \<Rightarrow> ('r ell2, 'r ell2) trace_class \<Rightarrow> 'c \<Rightarrow> ('q ell2, 'q ell2) trace_class\<close> where
  \<open>cq_operator_at Q \<rho> c = sandwich_tc (tensor_ell2_left (ket c)*) (apply_qregister_tc (qregister_inv Q) \<rho>)\<close>

lemma cq_operator_at_summable:
  fixes \<rho> :: \<open>(('c\<times>'q) ell2, ('c\<times>'q) ell2) trace_class\<close> and c :: 'c
  shows \<open>cq_operator_at Q \<rho> abs_summable_on UNIV\<close>
  using partial_trace_abs_summable'[of \<open>sandwich_tc swap_ell2 (apply_qregister_tc (qregister_inv Q) \<rho>)\<close>]
  by (simp add: cq_operator_at_def sandwich_tc_compose[symmetric, unfolded o_def, THEN fun_cong])

lemma cq_operator_at_bounded_clinear[bounded_clinear]:
  assumes \<open>iso_qregister Q\<close>
  shows \<open>bounded_clinear (\<lambda>\<rho>. cq_operator_at Q \<rho> c)\<close>
proof -
  have 1: \<open>cq_operator_at Q (\<rho> + y) c = cq_operator_at Q \<rho> c + cq_operator_at Q y c\<close> for \<rho> y :: \<open>('c ell2, 'c ell2) trace_class\<close>
    by (simp add: sandwich_tc_plus cq_operator_at_def apply_qregister_tc_plus)
  have 2: \<open>cq_operator_at Q (r *\<^sub>C \<rho>) c = r *\<^sub>C cq_operator_at Q \<rho> c\<close> for \<rho> :: \<open>('c ell2, 'c ell2) trace_class\<close> and r
    by (simp add: cq_operator_at_def sandwich_tc_scaleC_right apply_qregister_tc_scale)
  have 3: \<open>norm (cq_operator_at Q \<rho> c) \<le> norm \<rho> * 1\<close> for \<rho> :: \<open>('c ell2, 'c ell2) trace_class\<close>
    using norm_sandwich_tc[of \<open>tensor_ell2_left (ket c)*\<close> \<open>apply_qregister_tc (qregister_inv Q) \<rho>\<close>]
    by (simp add: cq_operator_at_def apply_iso_qregister_tc_norm assms iso_qregister_inv_iso)
  from 1 2 3
  show ?thesis
    by (rule bounded_clinearI)
qed


lemma cq_operator_reconstruct_inv:
  fixes \<rho> :: \<open>'c \<Rightarrow> ('q ell2, 'q ell2) trace_class\<close>
  assumes sum_\<rho>: \<open>\<rho> abs_summable_on UNIV\<close>
  assumes \<open>iso_qregister Q\<close>
  shows \<open>cq_operator_at Q (cq_operator_reconstruct Q \<rho>) = \<rho>\<close>
proof (rule ext)
  fix c :: 'c
  define q q1 where \<open>q = apply_qregister_tc Q\<close> and \<open>q1 = apply_qregister_tc (qregister_inv Q)\<close>
  have [simp]: \<open>q1 (q t) = t\<close> for t
    unfolding q1_def q_def 
    apply (subst qregister_chain_apply_tc[symmetric, unfolded o_def, THEN fun_cong])
    using assms by (auto simp add: iso_qregister_inv_iso iso_qregister_inv_chain) 
  have \<open>bounded_linear q\<close>
    by (simp add: q_def assms bounded_clinear.bounded_linear bounded_clinear_apply_qregister_tc)

  have *: \<open>cq_operator_at Q (q (tc_tensor (tc_butterfly (ket d) (ket d)) (\<rho> d))) c = of_bool (c=d) *\<^sub>C \<rho> d\<close> for d
    apply (rule from_trace_class_inject[THEN iffD1])
    by (simp add: cq_operator_at_def from_trace_class_sandwich_tc tc_tensor.rep_eq tc_butterfly.rep_eq sandwich_tensor_ell2_left
        flip: q1_def)
  have summable1: \<open>(\<lambda>c. tc_tensor (tc_butterfly (ket c) (ket c)) (\<rho> c)) summable_on UNIV\<close>
    by (simp add: abs_summable_summable assms norm_tc_butterfly norm_tc_tensor)
  then have summable2: \<open>(\<lambda>d. q (tc_tensor (tc_butterfly (ket d) (ket d)) (\<rho> d))) summable_on UNIV\<close>
    by (simp add: abs_summable_summable apply_iso_qregister_tc_norm assms(1,2) norm_tc_butterfly norm_tc_tensor q_def)
  have \<open>cq_operator_at Q (cq_operator_reconstruct Q \<rho>) c
     = cq_operator_at Q (\<Sum>\<^sub>\<infinity>c. q (tc_tensor (tc_butterfly (ket c) (ket c)) (\<rho> c))) c\<close>
    by (simp add: cq_operator_reconstruct_def q_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. cq_operator_at Q (q (tc_tensor (tc_butterfly (ket d) (ket d)) (\<rho> d))) c)\<close>
    apply (subst infsum_bounded_linear[where h=\<open>\<lambda>\<rho>. cq_operator_at Q \<rho> c\<close>])
      apply (simp add: bounded_clinear.bounded_linear cq_operator_at_bounded_clinear assms) 
     apply (rule summable2)
    by simp
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d::'c. of_bool (c = d) *\<^sub>C \<rho> d)\<close>
    by (simp add: * )
  also have \<open>\<dots> = \<rho> c\<close>
    apply (subst infsum_single[where i=c])
    by auto
  finally show \<open>cq_operator_at Q (cq_operator_reconstruct Q \<rho>) c = \<rho> c\<close>
    by -
qed

lemma cq_operator_reconstruct:
  fixes \<rho> :: \<open>('r ell2, 'r ell2) trace_class\<close>
    and C :: \<open>('c, 'r) qregister\<close>
    and Q :: \<open>('q, 'r) qregister\<close>
  assumes \<open>qcomplements C Q\<close>
  assumes cq: \<open>classical_on C \<rho>\<close>
  defines \<open>CQ \<equiv> \<lbrakk>C,Q\<rbrakk>\<^sub>q\<close>
  shows \<open>cq_operator_reconstruct CQ (cq_operator_at CQ \<rho>) = \<rho>\<close>
proof -
  have [iff]: \<open>iso_qregister CQ\<close>
    using assms(1,3) qcomplements_def' by blast
  then have [iff]: \<open>qregister CQ\<close>
    using iso_qregister_def' by blast
  define cq cq1 where \<open>cq = apply_qregister_tc CQ\<close> and \<open>cq1 = apply_qregister_tc (qregister_inv CQ)\<close>
  have [simp]: \<open>cq1 (cq t) = t\<close> for t
    unfolding cq1_def cq_def 
    apply (subst qregister_chain_apply_tc[symmetric, unfolded o_def, THEN fun_cong])
    by (auto simp add: iso_qregister_inv_iso iso_qregister_inv_chain) 
  have [iff]: \<open>bounded_linear cq\<close>
    by (simp add: cq_def bounded_clinear.bounded_linear bounded_clinear_apply_qregister_tc)
  have [iff]: \<open>bounded_linear cq1\<close>
    by (simp add: cq1_def bounded_clinear.bounded_linear bounded_clinear_apply_qregister_tc iso_qregister_inv_iso)
  define f :: \<open>('c \<times> 'q) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'q) ell2 \<Rightarrow> 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close>
    where \<open>f = inv (\<lambda>E. E \<otimes>\<^sub>o id_cblinfun)\<close>
  have [simp]: \<open>f (E \<otimes>\<^sub>o id_cblinfun) = E\<close> for E :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close>
    unfolding f_def
    apply (subst inv_f_f)
    by (auto intro!: inj_tensor_left)
  have \<open>cq_operator_reconstruct CQ (cq_operator_at CQ \<rho>)
        = (\<Sum>\<^sub>\<infinity>c. cq (tc_tensor (tc_butterfly (ket c) (ket c)) (sandwich_tc (tensor_ell2_left (ket c)*) (cq1 \<rho>))))\<close>
    by (simp add: cq_def cq1_def cq_operator_reconstruct_def cq_operator_at_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>c. cq (sandwich_tc (selfbutter (ket c) \<otimes>\<^sub>o id_cblinfun) (cq1 \<rho>)))\<close>
    (is \<open>(\<Sum>\<^sub>\<infinity>c. ?lhs c) = (\<Sum>\<^sub>\<infinity>c. ?rhs c)\<close>)
  proof (rule infsum_cong)
    fix c
    show \<open>?lhs c = ?rhs c\<close>
    proof -
      have *: \<open>sandwich_tc (selfbutter (ket c) \<otimes>\<^sub>o id_cblinfun) (tc_tensor x (tc_butterfly a b)) =
       tc_tensor (tc_butterfly (ket c) (ket c)) (sandwich_tc (tensor_ell2_left (ket c)*) (tc_tensor x (tc_butterfly a b)))\<close>
        for x :: \<open>('c ell2, 'c ell2) trace_class\<close> and a b :: \<open>'e ell2\<close>
        apply (rule from_trace_class_inject[THEN iffD1])
        apply (simp add: from_trace_class_sandwich_tc tc_tensor.rep_eq tc_butterfly.rep_eq sandwich_tensor_ell2_left)
        by (simp add: sandwich_apply tensor_op_adjoint comp_tensor_op butterfly_comp_cblinfun cinner_adj_left tensor_op_cbilinear.scaleC_left tensor_op_cbilinear.scaleC_right)
      have \<open>sandwich_tc (selfbutter (ket c) \<otimes>\<^sub>o id_cblinfun) = (\<lambda>\<rho>. tc_tensor (tc_butterfly (ket c) (ket c)) (sandwich_tc (tensor_ell2_left (ket c)*) \<rho>))\<close>
        apply (rule eq_from_separatingI2)
           apply (rule separating_set_bounded_clinear_tc_tensor_nested)
            apply (rule separating_set_UNIV)
           apply (rule separating_set_tc_butterfly)
        using bounded_clinear_sandwich_tc apply blast
        using bounded_clinear_compose bounded_clinear_sandwich_tc bounded_clinear_tc_tensor_right apply blast 
        using * by auto
      then show ?thesis
        by metis
    qed
  qed
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>range (\<lambda>x::'c. ((selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun), ket x)). cq (sandwich_tc (fst E) (cq1 \<rho>)))\<close>
    apply (subst infsum_reindex)
    by (simp_all add: inj_def o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((E, x), F, y)\<in>range (\<lambda>x. (selfbutter (ket x), ket x)) \<times> {(id_cblinfun, ())}. cq (sandwich_tc (E \<otimes>\<^sub>o F) (cq1 \<rho>)))\<close>
    apply (subst infsum_reindex_bij_betw[where A=\<open>range (\<lambda>x. (selfbutter (ket x), ket x)) \<times> {(id_cblinfun, ())}\<close>
          and g=\<open>\<lambda>((E,x),(F,y)). (E \<otimes>\<^sub>o F, x)\<close>, symmetric])
     apply (rule bij_betw_byWitness[where f'=\<open>\<lambda>(Eid,x). ((f Eid,x),(id_cblinfun,()))\<close>])
        apply auto[4]
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> = cq (\<Sum>\<^sub>\<infinity>((E, x), F, y)\<in>range (\<lambda>x. (selfbutter (ket x), ket x)) \<times> {(id_cblinfun, ())}. sandwich_tc (E \<otimes>\<^sub>o F) (cq1 \<rho>))\<close>
    apply (subst infsum_bounded_linear_invertible[where h=cq and h'=cq1, symmetric])
    by (auto simp: case_prod_unfold)
  also have \<open>\<dots> = cq (kf_tensor (kf_complete_measurement (range ket)) kf_id *\<^sub>k\<^sub>r (cq1 \<rho>))\<close>
    apply (simp only: kf_apply_tensor_as_infsum kf_id_def kf_of_op.rep_eq kf_complete_measurement.rep_eq)
    by (simp add: image_image)
  also have \<open>\<dots> = kf_apply_qregister CQ (kf_tensor (kf_complete_measurement (range ket)) kf_id) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_apply_qregister_iso_qregister_explicit cq_def cq1_def)
  also have \<open>\<dots> = kf_apply_qregister C (kf_complete_measurement (range ket)) *\<^sub>k\<^sub>r \<rho>\<close>
    using \<open>qregister CQ\<close> by (auto intro!: kf_apply_eqI kf_apply_qregister_pair_tensor_id_weak simp: CQ_def)
  also have \<open>\<dots> = km_apply_qregister C (km_complete_measurement (range ket)) \<rho>\<close>
    by (metis (no_types, lifting) ext CQ_def Missing_Bounded_Operators.is_ortho_set_ket \<open>iso_qregister CQ\<close> distinct_qvarsL
      iso_qregister_def' kf_complete_measurement_apply km_apply_qregister_kf_apply km_complete_measurement_def) 
  also have \<open>\<dots> = \<rho>\<close>
    using cq unfolding classical_on_def cq_id_def by blast
  finally show ?thesis
    by -
qed

definition is_cq_map :: \<open>('c, 'r) qregister \<Rightarrow> (('r ell2, 'r ell2) trace_class \<Rightarrow> ('r ell2, 'r ell2) trace_class) \<Rightarrow> bool\<close> where
  \<open>is_cq_map C \<EE> \<longleftrightarrow> kraus_map \<EE> \<and> cq_id C o \<EE> o cq_id C = \<EE>\<close>

lemma cq_id_invalid: \<open>cq_id C = 0\<close> if \<open>\<not> qregister C\<close>
  by (simp add: cq_id_def that km_apply_qregister_invalid)

lemma kf_comp_apply_qregister: \<open>kf_comp (kf_apply_qregister Q \<EE>) (kf_apply_qregister Q \<FF>) = kf_apply_qregister Q (kf_comp \<EE> \<FF>)\<close>
  by x

lemma km_apply_qregister_comp:
  assumes \<open>kraus_map \<EE>\<close> and \<open>kraus_map \<FF>\<close>
  shows \<open>km_apply_qregister Q \<EE> (km_apply_qregister Q \<FF> t) = km_apply_qregister Q (\<EE> o \<FF>) t\<close>
proof -
  have \<open>km_apply_qregister Q \<EE> (km_apply_qregister Q \<FF> t)
     = kf_comp (kf_apply_qregister Q (km_some_kraus_family \<EE>)) (kf_apply_qregister Q (km_some_kraus_family \<FF>)) *\<^sub>k\<^sub>r t\<close>
    by (simp add: km_apply_qregister_def kf_comp_apply)
  also have \<open>\<dots> = kf_apply_qregister Q (kf_comp (km_some_kraus_family \<EE>) (km_some_kraus_family \<FF>)) *\<^sub>k\<^sub>r t\<close>
    by (simp add: kf_comp_apply_qregister)
  also have \<open>\<dots> = kf_apply_qregister Q (km_some_kraus_family (\<EE> o \<FF>)) *\<^sub>k\<^sub>r t\<close>
    apply (rule kf_apply_eqI)
    apply (rule kf_apply_qregister_cong_weak)
    by (simp add: assms(1,2) kf_comp_apply kf_eq_weak_def kraus_map_comp)
  also have \<open>\<dots> = km_apply_qregister Q (\<EE> o \<FF>) t\<close>
    by (simp add: km_apply_qregister_def)
  finally show ?thesis
    by -
qed


lemma cq_id_idem[simp]: \<open>cq_id C (cq_id C t) = cq_id C t\<close>
proof -
  wlog \<open>qregister C\<close>
    by (simp add: cq_id_invalid negation)
  have \<open>cq_id C (cq_id C t) = km_apply_qregister C (km_complete_measurement (range ket) \<circ> km_complete_measurement (range ket)) t\<close>
    by (simp add: cq_id_def km_apply_qregister_comp kraus_map_complete_measurement)
  also have \<open>\<dots> = km_apply_qregister C (km_complete_measurement (range ket)) t\<close>
    by (simp add: comp_def)
  also have \<open>\<dots> = cq_id C t\<close>
    by (simp add: cq_id_def)
  finally show ?thesis
    by -
qed


lemma kraus_map_cq_id[iff]: \<open>kraus_map (cq_id C)\<close>
  apply (cases \<open>qregister C\<close>)
   apply (simp add: cq_id_def km_apply_qregister_def) 
  by (simp add: cq_id_invalid)

lemma is_cq_map_id[iff]: \<open>is_cq_map C (cq_id C)\<close>
  by (auto simp: is_cq_map_def)

lemma bounded_clinear_cq_id[bounded_clinear, iff]: \<open>bounded_clinear (cq_id C)\<close>
  by (simp add: kraus_map_bounded_clinear)

lemma is_cq_map_0[iff]: \<open>is_cq_map Q 0\<close>
  apply (auto intro!: ext simp add: is_cq_map_def o_def)
  by (metis bounded_clinear_CBlinfun_apply bounded_clinear_cq_id cblinfun.real.zero_right)

definition cq_prob :: \<open>('c,'r) qregister \<Rightarrow> ('r ell2, 'r ell2) trace_class \<Rightarrow> 'c \<Rightarrow> real\<close> where
  \<open>cq_prob C \<rho> c = norm (sandwich_tc (apply_qregister C (selfbutter (ket c))) \<rho>)\<close>


lemma km_norm_cq_id[simp]:
  assumes \<open>qregister C\<close>
  shows \<open>km_norm (cq_id C) = 1\<close>
  by x


definition kf_map_with_auxiliary_state ::
  \<open>('c ell2, 'c ell2) trace_class \<Rightarrow> (('a\<times>'c) ell2, ('b\<times>'d) ell2, 'x) kraus_family \<Rightarrow> ('a ell2, 'b ell2, 'x) kraus_family\<close> where
  \<open>kf_map_with_auxiliary_state \<rho> \<EE> = kf_map (\<lambda>((_,x),_). x) (kf_comp kf_partial_trace_right (kf_comp \<EE> (kf_tensor_right \<rho>)))\<close>

(* definition km_map_with_auxiliary_state ::
  \<open>('aux ell2, 'aux ell2) trace_class \<Rightarrow> (('a\<times>'aux, 'a\<times>'aux) trace_class \<Rightarrow> ('b\<times>'c, 'b\<times>'c) trace_class) \<Rightarrow> (('a, 'a) trace_class \<Rightarrow> ('b, 'b) trace_class)\<close> where *)

definition kf_local_register :: 
  \<open>'a QREGISTER \<Rightarrow> ('a ell2, 'a ell2) trace_class \<Rightarrow> ('a ell2, 'a ell2, 'x) kraus_family \<Rightarrow> ('a ell2, 'a ell2, 'x) kraus_family\<close> where
  \<open>kf_local_register Q \<rho> \<EE> = kf_map_with_auxiliary_state \<rho> (kf_map (\<lambda>((_,(x,_)),_). x)
        (kf_comp  (kf_of_op (swap_QREGISTER Q))
         (kf_comp (kf_tensor \<EE> kf_id)
                  (kf_of_op (swap_QREGISTER Q)))))\<close>

definition km_local_register :: 
  \<open>'a QREGISTER \<Rightarrow> ('a ell2, 'a ell2) trace_class \<Rightarrow> (('a ell2, 'a ell2) trace_class \<Rightarrow> ('a ell2, 'a ell2) trace_class) \<Rightarrow> (('a ell2, 'a ell2) trace_class \<Rightarrow> ('a ell2, 'a ell2) trace_class)\<close> where
  \<open>km_local_register Q \<rho> \<EE> = kf_apply (kf_local_register Q \<rho> (km_some_kraus_family \<EE>))\<close>
  

lemma is_cq_map_km_local_register_quantum:
  assumes \<open>Qqcompatible Q C\<close>
  assumes \<open>is_cq_map C \<EE>\<close>
  shows \<open>is_cq_map C (km_local_register Q \<rho> \<EE>)\<close>
  by x

lemma explicit_cblinfun_exists_0[simp]: \<open>explicit_cblinfun_exists (\<lambda>_ _. 0)\<close>
  by (auto intro!: explicit_cblinfun_exists_bounded[where B=0] simp: explicit_cblinfun_def)

lemma explicit_cblinfun_0[simp]: \<open>explicit_cblinfun (\<lambda>_ _. 0) = 0\<close>
  by (auto intro!: equal_ket Rep_ell2_inject[THEN iffD1] ext simp: Rep_ell2_explicit_cblinfun_ket zero_ell2.rep_eq)
(* 
lemma \<open>cblinfun_extension_exists (range ket) (\<lambda>ketm. 
          \<Sum>\<^sub>\<infinity>(x,y) | apply_cregister F [x\<mapsto>y] m \<noteq> None. (ket y \<bullet>\<^sub>C a (ket x)) *\<^sub>C ket (the (apply_cregister F [x\<mapsto>y] m)))\<close>
proof -
  wlog \<open>cregister F\<close>
    using negation
    apply (simp add: non_cregister non_cregister.rep_eq non_cregister_raw_def)
try0
sledgehammer [dont_slice]
by -
  show ?thesis
    apply (rule cblinfun_extension_existsI)
 *)

lemma cnj_of_bool[simp]: \<open>cnj (of_bool b) = of_bool b\<close>
  by simp


lemma has_sum_single: 
  fixes f :: \<open>_ \<Rightarrow> _::{comm_monoid_add,t2_space}\<close>
  assumes "\<And>j. j \<noteq> i \<Longrightarrow> j\<in>A \<Longrightarrow> f j = 0"
  assumes \<open>s = (if i\<in>A then f i else 0)\<close>
  shows "HAS_SUM f A s"
  apply (subst has_sum_cong_neutral[where T=\<open>A \<inter> {i}\<close> and g=f])
  using assms by auto


lemma qregister_of_cregister_alt_def_has_sum:
  assumes \<open>cregister F\<close>
  shows \<open>((\<lambda>(x,y). ket y \<bullet>\<^sub>C a (ket x)) has_sum
      of_bool (same_outside_cregister F n m) *\<^sub>C ket (Classical_Registers.getter F n) \<bullet>\<^sub>C a (ket (Classical_Registers.getter F m)))
          {(x,y). apply_cregister F [x\<mapsto>y] m = Some n}\<close>
proof (rule has_sum_single[where i=\<open>(getter F m, getter F n)\<close>])
  show \<open>j \<in> {(x, y). apply_cregister F [x \<mapsto> y] m = Some n} \<Longrightarrow> (case j of (x, y) \<Rightarrow> ket y \<bullet>\<^sub>C a (ket x)) = 0\<close>
    if \<open>j \<noteq> (Classical_Registers.getter F m, Classical_Registers.getter F n)\<close> for j
    apply (simp add: case_prod_unfold)
    using that
    by (metis (no_types, lifting) \<open>cregister F\<close> apply_cregister_getter_setter apply_cregister_of_0 array_rules(2) getter_setter_same option.case(2) option.simps(2)
        surjective_pairing )
  have *: \<open>apply_cregister F [Classical_Registers.getter F m \<mapsto> Classical_Registers.getter F n] m = Some n \<longleftrightarrow> same_outside_cregister F n m\<close>
    by (auto simp: same_outside_cregister_def \<open>cregister F\<close> apply_cregister_getter_setter)
  show \<open>of_bool (same_outside_cregister F n m) *\<^sub>C ket (Classical_Registers.getter F n) \<bullet>\<^sub>C a (ket (Classical_Registers.getter F m)) =
    (if (Classical_Registers.getter F m, Classical_Registers.getter F n) \<in> {(x, y). apply_cregister F [x \<mapsto> y] m = Some n}
     then case (Classical_Registers.getter F m, Classical_Registers.getter F n) of (x, y) \<Rightarrow> ket y \<bullet>\<^sub>C a (ket x) else 0)\<close>
    by (simp add: * )
qed


lemma qregister_of_cregister_alt_def_exists: \<open>explicit_cblinfun_exists (\<lambda>n m. 
          \<Sum>\<^sub>\<infinity>(x,y) | apply_cregister F [x\<mapsto>y] m = Some n. ket y \<bullet>\<^sub>C (a *\<^sub>V ket x))\<close>
proof -
  wlog \<open>cregister F\<close>
    using negation
    by (simp add: non_cregister non_cregister.rep_eq non_cregister_raw_def case_prod_unfold)
  have \<open>explicit_cblinfun_exists (\<lambda>n m. 
          \<Sum>\<^sub>\<infinity>(x,y) | apply_cregister F [x\<mapsto>y] m = Some n. ket y \<bullet>\<^sub>C (a *\<^sub>V ket x))
              = permute_and_tensor1_cblinfun_exists (getter F) (same_outside_cregister F) a\<close>
    unfolding permute_and_tensor1_cblinfun_exists_def
    apply (intro arg_cong[where f=explicit_cblinfun_exists] ext)
    unfolding infsumI[OF qregister_of_cregister_alt_def_has_sum[OF \<open>cregister F\<close>]]
    by (simp add: cinner_ket_left)
  moreover have \<open>permute_and_tensor1_cblinfun_exists (getter F) (same_outside_cregister F) a\<close>
    by (simp add: \<open>cregister F\<close> permute_and_tensor1_cblinfun_exists_register)
  ultimately show ?thesis
    by simp
qed

lemma qregister_of_cregister_alt_def:
  shows \<open>apply_qregister (qregister_of_cregister F) a = explicit_cblinfun (\<lambda>n m. 
          \<Sum>\<^sub>\<infinity>(x,y) | apply_cregister F [x\<mapsto>y] m = Some n. ket y \<bullet>\<^sub>C (a *\<^sub>V ket x))\<close>
proof -
  wlog [iff]: \<open>cregister F\<close>
    using negation
    by (simp add: non_cregister non_cregister.rep_eq non_cregister_raw_def)
  have \<open>apply_qregister (qregister_of_cregister F) a = permute_and_tensor1_cblinfun (Classical_Registers.getter F) (same_outside_cregister F) a\<close>
    by (simp add: apply_qregister_of_cregister)
  also have \<open>\<dots> = explicit_cblinfun (\<lambda>n m. of_bool (same_outside_cregister F n m) * Rep_ell2 (a *\<^sub>V ket (Classical_Registers.getter F m)) (Classical_Registers.getter F n))\<close>
    by (simp add: permute_and_tensor1_cblinfun_def)
  also have \<open>\<dots> = explicit_cblinfun (\<lambda>n m. \<Sum>\<^sub>\<infinity>(x,y) | apply_cregister F [x\<mapsto>y] m = Some n. ket y \<bullet>\<^sub>C (a *\<^sub>V ket x))\<close>
    apply (intro arg_cong[where f=explicit_cblinfun] ext)
    unfolding infsumI[OF qregister_of_cregister_alt_def_has_sum[OF \<open>cregister F\<close>], symmetric]
    using infsumI[OF qregister_of_cregister_alt_def_has_sum[OF \<open>cregister F\<close>], symmetric]
    by (simp add: cinner_ket_left)
  finally show ?thesis
    by -
qed

lemma classical_operator_None[simp]: \<open>classical_operator (\<lambda>_. None) = 0\<close>
  by (auto intro!: equal_ket simp: classical_operator_ket inj_map_def classical_operator_exists_inj)

lift_definition QREGISTER_of_CREGISTER :: \<open>'a CREGISTER \<Rightarrow> 'a QREGISTER\<close> is
  \<open>\<lambda>C :: ('a \<rightharpoonup> 'a) set. commutant (commutant (let ops = {classical_operator f | f. f \<in> C \<and> inj_map f} in ops \<union> adj ` ops))\<close>
proof (intro CollectI valid_qregister_range_def[THEN iffD2] von_neumann_algebra_def[THEN iffD2] conjI ballI)
  fix C :: \<open>('a \<rightharpoonup> 'a) set\<close> and a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assume \<open>C \<in> Collect valid_cregister_range\<close>
  then have \<open>valid_cregister_range C\<close>
    by simp
  define ops where \<open>ops = {classical_operator f | f. f \<in> C \<and> inj_map f}\<close>
  show \<open>commutant (commutant (commutant (commutant (let ops = ops in ops \<union> adj ` ops)))) = commutant (commutant (let ops = ops in ops \<union> adj ` ops))\<close>
    by simp
  fix a
  assume \<open>a \<in> commutant (commutant (let ops = ops in ops \<union> adj ` ops))\<close>
  then have \<open>a* \<in> adj ` \<dots>\<close>
    by blast
  also have \<open>\<dots> = commutant (commutant (adj ` ops \<union> ops))\<close>
    by (simp add: commutant_adj image_Un image_image)
  also have \<open>\<dots> = commutant (commutant (let ops = ops in ops \<union> adj ` ops))\<close>
    by (simp add: Un_commute)
  finally show \<open>a* \<in> commutant (commutant (let ops = ops in ops \<union> adj ` ops))\<close>
    by simp
qed

lemma QREGISTER_of_CREGISTER_bot[simp]: \<open>QREGISTER_of_CREGISTER \<bottom> = \<bottom>\<close>
proof transfer'
  define ops where \<open>ops = {classical_operator f | f::'a\<rightharpoonup>'a. f \<in> empty_cregister_range \<and> inj_map f}\<close>

  have \<open>ops \<subseteq> one_algebra\<close>
    apply (simp add: ops_def empty_cregister_range_def one_algebra_def)
    by force
  moreover then have \<open>adj ` ops \<subseteq> one_algebra\<close>
    by (metis (mono_tags, lifting) commutant_UNIV commutant_adj commutant_one_algebra image_mono image_subset_iff subset_UNIV von_neumann_algebra_adj_image
        von_neumann_algebra_def)
  ultimately have \<open>commutant (commutant (let ops = ops in ops \<union> adj ` ops)) \<subseteq> commutant (commutant one_algebra)\<close>
    by (auto intro!: commutant_antimono Un_least simp: Let_def)
  also have \<open>\<dots> = one_algebra\<close>
    by (simp add: commutant_UNIV commutant_one_algebra)
  finally have \<open>commutant (commutant (let ops = ops in ops \<union> adj ` ops)) \<subseteq> one_algebra\<close>
    by -
  then show \<open>commutant (commutant (let ops = ops in ops \<union> adj ` ops)) = one_algebra\<close>
    by (metis (no_types, lifting) \<open>adj ` ops \<subseteq> one_algebra\<close> \<open>ops \<subseteq> one_algebra\<close> commutant_UNIV commutant_empty commutant_one_algebra double_commutant_Un_right
        subset_Un_eq sup_bot.comm_neutral)
qed

lemma apply_cregister_inj_map_iff: 
  fixes X :: \<open>('a,'b) cregister\<close>
  assumes [iff]: \<open>cregister X\<close>
  shows \<open>inj_map (apply_cregister X f) \<longleftrightarrow> inj_map f\<close>
proof (intro iffI inj_map_def[THEN iffD2] allI impI conjI; rename_tac m n)
  fix a b :: 'a and m :: 'b
  define gX sX where \<open>gX = getter X\<close> and \<open>sX = setter X\<close>
  assume inj_Xf: \<open>inj_map (apply_cregister X f)\<close> and \<open>f a = f b \<and> f a \<noteq> None\<close>
  then obtain c where fa: \<open>f a = Some c\<close> and fb: \<open>f b = Some c\<close>
    by fastforce
  have gXsX[simp]: \<open>gX (sX a m) = a\<close> for a m
    using assms gX_def sX_def by auto
  have sXsX[simp]: \<open>sX a (sX b m) = sX a m\<close> for a b m
    by (simp add: sX_def)
  have Xfsam_Some: \<open>apply_cregister X f (sX a m) \<noteq> None\<close>
    by (simp add: inj_map_def apply_cregister_getter_setter[OF assms] fa
        flip: sX_def gX_def)
  have Xfsbm_Some:\<open>apply_cregister X f (sX b m) \<noteq> None\<close>
    by (simp add: inj_map_def apply_cregister_getter_setter[OF assms] fb
        flip: sX_def gX_def)
  have Xfsbm_Xfsam: \<open>apply_cregister X f (sX a m) = apply_cregister X f (sX b m)\<close>
    by (simp add: apply_cregister_getter_setter fa fb flip: gX_def sX_def)
  from Xfsbm_Xfsam Xfsam_Some Xfsbm_Some inj_Xf have \<open>sX a m = sX b m\<close>
    by (simp add: inj_map_def)  
  then have \<open>gX (sX a m) = gX (sX b m)\<close>
    by simp
  then show \<open>a = b\<close>
    by simp
next
  fix m n :: 'b
  define gX sX where \<open>gX = getter X\<close> and \<open>sX = setter X\<close>
  assume \<open>inj_map f\<close>
  assume \<open>apply_cregister X f m = apply_cregister X f n \<and> apply_cregister X f m \<noteq> None\<close>
  then obtain k where Xfm_k: \<open>apply_cregister X f m = Some k\<close> and Xfn_k: \<open>apply_cregister X f n = Some k\<close>
    by fastforce
  from Xfm_k obtain c where fgm_c: \<open>f (gX m) = Some c\<close>
    apply (simp add: apply_cregister_getter_setter flip: gX_def sX_def)
    by fastforce
  from Xfn_k obtain d where fgn_d: \<open>f (gX n) = Some d\<close>
    apply (simp add: apply_cregister_getter_setter flip: gX_def sX_def)
    by fastforce
  from Xfm_k have \<open>sX c m = k\<close>
    by (simp add: apply_cregister_getter_setter fgm_c flip: gX_def sX_def)
  moreover from Xfn_k have \<open>sX d n = k\<close>
    by (simp add: apply_cregister_getter_setter fgn_d flip: gX_def sX_def)
  ultimately have \<open>c = d\<close>
    by (metis assms getter_setter_same sX_def)
  with fgm_c fgn_d \<open>inj_map f\<close>
  show \<open>m = n\<close>
    by (metis \<open>sX c m = k\<close> \<open>sX d n = k\<close> gX_def inj_map_def option.simps(2) sX_def setter_getter_same setter_setter_same)
qed



lemma QREGISTER_of_qregister_of_cregister: \<open>QREGISTER_of (qregister_of_cregister X) = QREGISTER_of_CREGISTER (CREGISTER_of X)\<close>
proof -
  have 1: \<open>QREGISTER_of (qregister_of_cregister X) = QREGISTER_of_CREGISTER (CREGISTER_of X)\<close>
    if \<open>\<not> cregister X\<close>
    using that by (simp add: non_cregister)
  define ops where \<open>ops = {classical_operator f |f. f \<in> range (apply_cregister X) \<and> inj_map f}\<close>
  define ccops where \<open>ccops = commutant (commutant (ops \<union> adj ` ops))\<close>
  define apply_qX where \<open>apply_qX = apply_qregister (qregister_of_cregister X)\<close>
  define gX sX where \<open>gX = getter X\<close> and \<open>sX = setter X\<close>
  have 2: \<open>QREGISTER_of (qregister_of_cregister X) \<le> QREGISTER_of_CREGISTER (CREGISTER_of X)\<close>
    if [iff]: \<open>cregister X\<close>
  proof -
    have \<open>range apply_qX \<subseteq> ccops\<close>
    proof (intro image_subsetI)
(* TODO clean out unused lemmas *)
      fix x :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
      have \<open>csubspace ccops\<close>
        by (simp add: ccops_def)
      have \<open>closedin weak_star_topology ccops\<close>
        using ccops_def by auto
      have \<open>closedin cstrong_operator_topology ccops\<close>
        using ccops_def commutant_sot_closed by blast
      have \<open>apply_qX (butterfly (ket a) (ket b)) \<in> ops\<close> for a b
      proof (unfold ops_def, intro CollectI exI conjI)
        show \<open>apply_cregister X [b \<mapsto> a] \<in> range (apply_cregister X)\<close>
          by fast
        have \<open>inj_map [b\<mapsto>a]\<close>
          by (simp add: inj_map_def)
        then show inj: \<open>inj_map (apply_cregister X [b\<mapsto>a])\<close>
          by (simp add: apply_cregister_inj_map_iff \<open>cregister X\<close>)
        show \<open>apply_qX (butterfly (ket a) (ket b)) = classical_operator (apply_cregister X [b \<mapsto> a])\<close>
        proof (intro equal_ket cinner_ket_eqI, rename_tac m n)
          fix m n :: 'a
          have \<open>ket n \<bullet>\<^sub>C (apply_qX (butterfly (ket a) (ket b)) *\<^sub>V ket m)
                 = of_bool (same_outside_cregister X n m) *\<^sub>C ket (gX n) \<bullet>\<^sub>C (butterfly (ket a) (ket b) *\<^sub>V ket (gX m))\<close>
            unfolding qregister_of_cregister_alt_def apply_qX_def
            apply (subst Rep_ell2_explicit_cblinfun_ket[folded cinner_ket_left])
             apply (rule qregister_of_cregister_alt_def_exists)
            apply (subst qregister_of_cregister_alt_def_has_sum[THEN infsumI, OF \<open>cregister X\<close>])
            by (simp add: gX_def)
          also 
          have \<open>\<dots> = of_bool (same_outside_cregister X n m \<and> gX n = a \<and> gX m = b)\<close>
            by (auto simp: cinner_ket)
          also
          have \<open>\<dots> = of_bool (apply_cregister X [b \<mapsto> a] m = Some n)\<close>
            by x
          also
          have \<open>\<dots> = ket n \<bullet>\<^sub>C (classical_operator (apply_cregister X [b \<mapsto> a]) *\<^sub>V ket m)\<close>
            apply (cases \<open>apply_cregister X [b \<mapsto> a] m\<close>)
            using inj
            by (auto simp add: classical_operator_ket classical_operator_exists_inj apply_cregister_inj_map_iff
                cinner_ket)
          finally
          show \<open>ket n \<bullet>\<^sub>C (apply_qX (butterfly (ket a) (ket b)) *\<^sub>V ket m) = ket n \<bullet>\<^sub>C (classical_operator (apply_cregister X [b \<mapsto> a]) *\<^sub>V ket m)\<close>
            by -
      qed
      then have \<open>apply_qX (butterfly (ket a) (ket b)) \<in> ccops\<close> for a b
        by (simp add: ccops_def double_commutant_grows')


      show \<open>apply_qregister (qregister_of_cregister X) x \<in> ccops\<close>
        by x

    
    
    
    
    
    
    qed
    then show ?thesis
      by (simp add: less_eq_QREGISTER_def QREGISTER_of.rep_eq that QREGISTER_of_CREGISTER.rep_eq CREGISTER_of.rep_eq ccops_def
          flip: ops_def)
  qed
  have 3: \<open>QREGISTER_of_CREGISTER (CREGISTER_of X) \<le> QREGISTER_of (qregister_of_cregister X)\<close>
    if \<open>cregister X\<close>
  proof -
    have ops1: \<open>ops \<subseteq> range (apply_qregister (qregister_of_cregister X))\<close>
    proof (intro subsetI)
      fix x assume \<open>x \<in> ops\<close>
      then obtain f where x_def: \<open>x = classical_operator f\<close> and [iff]: \<open>inj_map f\<close> and \<open>f \<in> range (apply_cregister X)\<close>
        by (auto simp: ops_def)
      then obtain g where fg: \<open>f = apply_cregister X g\<close>
        by auto
      then have f_get_set: \<open>f m = (case g (gX m) of None \<Rightarrow> None | Some b \<Rightarrow> Some (sX b m))\<close> for m
        by (metis apply_cregister_getter_setter gX_def sX_def that)
      from fg \<open>inj_map f\<close> have [iff]: \<open>inj_map g\<close>
        by (simp add: fg apply_cregister_inj_map_iff \<open>cregister X\<close>)
      have aux1: \<open>same_outside_cregister X m n \<Longrightarrow> ket m \<bullet>\<^sub>C ket (sX a n) = ket (gX m) \<bullet>\<^sub>C ket a\<close> for a n m
        by (metis cinner_ket_same gX_def getter_setter_same orthogonal_ket sX_def same_outside_cregister_def that)
      have aux2: \<open>g (gX n) = Some a \<Longrightarrow> \<not> same_outside_cregister X (sX a n) n \<Longrightarrow> m = sX a n \<Longrightarrow> False\<close> for a n m
        by (simp add: sX_def same_outside_cregister_def that)

      define a where \<open>a = classical_operator g\<close>
      have *: \<open>ket m \<bullet>\<^sub>C (x *\<^sub>V ket n) =
           of_bool (same_outside_cregister X m n) *\<^sub>C ket (gX m) \<bullet>\<^sub>C (a *\<^sub>V ket (gX n))\<close> for m n
        apply (cases \<open>g (gX n)\<close>)
         apply (simp_all add: a_def x_def classical_operator_ket classical_operator_exists_inj f_get_set
            flip: sX_def gX_def)
        using aux1 aux2           
        by blast
      have \<open>x = explicit_cblinfun (\<lambda>n m. \<Sum>\<^sub>\<infinity>(x, y) | apply_cregister X [x \<mapsto> y] m = Some n. ket y \<bullet>\<^sub>C (a *\<^sub>V ket x))\<close>
        apply (intro equal_ket cinner_ket_eqI)
        apply (subst Rep_ell2_explicit_cblinfun_ket[folded cinner_ket_left])
         apply (rule qregister_of_cregister_alt_def_exists)
        apply (subst qregister_of_cregister_alt_def_has_sum[THEN infsumI, OF \<open>cregister X\<close>])
        using *
        by (simp flip: gX_def)
      also have \<open>\<dots> \<in> range (apply_qregister (qregister_of_cregister X))\<close>
        by (simp add: qregister_of_cregister_alt_def[abs_def])
      finally show \<open>x \<in> \<dots>\<close>
        by -
    qed
    then have ops2: \<open>adj ` ops \<subseteq> range (apply_qregister (qregister_of_cregister X))\<close>
      apply (subst von_neumann_algebra_adj_image[where X=\<open>range _\<close>, symmetric])
      using qregister_qregister_of_cregister that valid_qregister_range valid_qregister_range_def apply blast 
      by fast
    from ops1 ops2 have \<open>ops \<union> adj ` ops \<subseteq> range (apply_qregister (qregister_of_cregister X))\<close>
      by fast
    then have \<open>commutant (commutant (ops \<union> adj ` ops)) \<subseteq> range (apply_qregister (qregister_of_cregister X))\<close>
      apply (rule double_commutant_in_vn_algI[rotated])
      using qregister_qregister_of_cregister that valid_qregister_range valid_qregister_range_def by blast 
    then show ?thesis
      by (simp add: less_eq_QREGISTER_def QREGISTER_of.rep_eq that QREGISTER_of_CREGISTER.rep_eq CREGISTER_of.rep_eq 
        flip: ops_def)
  qed
  from 1 2 3 show ?thesis
    apply (cases \<open>cregister X\<close>)
    by (auto intro!: order.antisym simp: )
qed



lemma is_cq_map_km_local_register_classical:
  assumes \<open>is_cq_map C \<EE>\<close>
  assumes \<open>classical_on C \<rho>\<close>
  shows \<open>is_cq_map C (km_local_register (QREGISTER_chain C (QREGISTER_of_ X)) \<rho> \<EE>)\<close>
  by x

term qregister_of_cregister






definition cq_map_from_measurement :: \<open>(('c1\<times>'q1) ell2, 'q2 ell2, 'c2) kraus_family \<Rightarrow> (('c1\<times>'q1) ell2, ('c2\<times>'q2) ell2, unit) kraus_family\<close> where
  \<open>cq_map_from_measurement E = kf_flatten
      (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) E)\<close>

definition cq_map_from_pointwise :: \<open>('c1 \<Rightarrow> ('q1 ell2, 'q2 ell2, 'c2) kraus_family) \<Rightarrow> (('c1\<times>'q1) ell2, ('c2\<times>'q2) ell2, unit) kraus_family\<close> where
  \<open>cq_map_from_pointwise E = cq_map_from_measurement (kf_map snd (kf_comp_dependent E kf_partial_trace_left))\<close>

definition cq_map_to_pointwise :: \<open>(('c1\<times>'q1) ell2, ('c2\<times>'q2) ell2, unit) kraus_family \<Rightarrow> ('c1 \<Rightarrow> ('q1 ell2, 'q2 ell2, 'c2) kraus_family)\<close> where
  \<open>cq_map_to_pointwise E = undefined\<close>

definition cq_map_cases :: \<open>('c1 \<Rightarrow> ('c1,'q1,'c2,'q2) cq_map) \<Rightarrow> ('c1,'q1,'c2,'q2) cq_map\<close> where
  \<open>cq_map_cases E = kf_flatten (kf_comp_dependent (\<lambda>(c,()). E (inv ket c))
                       (kf_tensor (kf_complete_measurement (range ket)) kf_id))\<close>

definition cq_map_sample :: \<open>('cl1 \<Rightarrow> 'cl2 \<Rightarrow> real) \<Rightarrow> ('cl1, 'qu,'cl2, 'qu) cq_map\<close> where
  \<open>cq_map_sample d = cq_map_from_pointwise (\<lambda>c. kf_sample (d c))\<close>

definition cq_map_comp :: \<open>('c2,'q2,'c3,'q3) cq_map \<Rightarrow> ('c1,'q1,'c2,'q2) cq_map \<Rightarrow> ('c1,'q1,'c3,'q3) cq_map\<close> where
  \<open>cq_map_comp E F = kf_flatten (kf_comp E F)\<close>

definition cq_map_on_q :: \<open>('c \<Rightarrow> ('q1 ell2,'q2 ell2,'x) kraus_family) \<Rightarrow> ('c,'q1,'c,'q2) cq_map\<close> where
  \<open>cq_map_on_q E = cq_map_from_pointwise (\<lambda>c. kf_map (\<lambda>_. c) (E c))\<close>

definition cq_map_on_c :: \<open>('c1 \<Rightarrow> 'c2) \<Rightarrow> ('c1,'q,'c2,'q) cq_map\<close> where
  \<open>cq_map_on_c f = cq_map_from_pointwise (\<lambda>c. kf_map (\<lambda>_. f c) kf_id)\<close>

definition \<open>cq_map_of_op U = cq_map_on_q (\<lambda>c. kf_of_op (U c))\<close>

definition cq_map_tensor_id_right :: \<open>('cl1, 'qu1, 'cl2, 'qu2) cq_map \<Rightarrow> ('cl1, 'qu1\<times>'extra, 'cl2, 'qu2\<times>'extra) cq_map\<close> where
  \<open>cq_map_tensor_id_right \<EE> = cq_map_from_pointwise (\<lambda>c. 
      kf_map fst (kf_tensor (cq_map_to_pointwise \<EE> c) kf_id))\<close>

definition cq_map_id :: \<open>('c,'q) cq_map2\<close> where
  \<open>cq_map_id = cq_map_on_q (\<lambda>_. kf_id)\<close>

definition is_cq_map :: \<open>('c1,'q1,'c2,'q2) cq_map \<Rightarrow> bool\<close> where
  \<open>is_cq_map E \<longleftrightarrow> (cq_map_comp (cq_map_comp cq_map_id E) cq_map_id) E\<close>

definition cq_map_while :: \<open>('c \<Rightarrow> bool) \<Rightarrow> ('c,'q) cq_map2 \<Rightarrow> ('c,'q) cq_map2\<close> where
  \<open>cq_map_while = undefined\<close>

lemma cq_map_comp_cq_map_from_measurement:
  shows \<open>cq_map_comp (cq_map_from_measurement F) (cq_map_from_measurement E) 
      =\<^sub>k\<^sub>r cq_map_from_measurement (kf_map snd (kf_comp F (kf_comp_dependent 
                                            (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) E)))\<close> /
proof -
  have \<open>cq_map_comp (cq_map_from_measurement F) (cq_map_from_measurement E)
    = kf_flatten (kf_comp (kf_flatten (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) F))
       (kf_flatten (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) E)))\<close>
    by (simp add: cq_map_comp_def cq_map_from_measurement_def)
  also have \<open>kf_flatten
     (kf_comp (kf_flatten (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) F))
       (kf_flatten (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) E)))
=\<^sub>k\<^sub>r kf_comp (kf_flatten (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) F))
       (kf_flatten (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) E))\<close>
  by (simp add: kraus_equivalent_def)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_comp ( (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) F))
       (kf_flatten (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) E))\<close>
    by (simp add: kraus_equivalent_def kf_comp_apply)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_comp ( (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) F))
       ( (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) E))\<close>
    by (simp add: kraus_equivalent_def kf_comp_apply)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>((g, f), e). (g, f, ()))
     (kf_comp_dependent (\<lambda>(_, f). kf_of_op (tensor_ell2_left (ket f)))
       (kf_comp F (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) E)))\<close>
    apply (rule kraus_equivalent'_trans)
    unfolding kf_comp_def
     apply (rule kf_comp_dependent_assoc')
    by auto
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_comp_dependent (\<lambda>(_, f). kf_of_op (tensor_ell2_left (ket f)))
       (kf_comp F (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) E))\<close>
    by (simp add: kraus_equivalent_def)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kf_flatten (kf_comp_dependent (\<lambda>f. kf_of_op (tensor_ell2_left (ket f)))
       (kf_map snd (kf_comp F (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) E))))\<close>
    apply (rule kraus_equivalent_sym)
    apply (rule kraus_equivalent_trans)
     apply (rule kf_flatten_cong)
     apply (rule kraus_equivalent'_imp_equivalent)
     apply (rule kf_comp_dependent_map_outcome_right)
    by (simp add: kraus_equivalent_def case_prod_unfold)
  also have \<open>\<dots> = cq_map_from_measurement (kf_map snd (kf_comp F (kf_comp_dependent 
                                            (\<lambda>c. kf_of_op (tensor_ell2_left (ket c))) E)))\<close>
    by (simp add: cq_map_from_measurement_def)
  finally show ?thesis
    by -
qed

lemma cq_map_from_measurement_cong:
  assumes \<open>E \<equiv>\<^sub>k\<^sub>r F\<close>
  shows \<open>cq_map_from_measurement E =\<^sub>k\<^sub>r cq_map_from_measurement F\<close>
by -

lemma kf_map_equiv_left_iff[simp]: 
(* TODO right *)
  shows \<open>kf_map f E =\<^sub>k\<^sub>r F \<longleftrightarrow> E =\<^sub>k\<^sub>r F\<close>
  by (simp add: kraus_equivalent_def)

lemma cq_map_comp_cq_map_from_pointwise:
  fixes E :: \<open>'c1 \<Rightarrow> ('q1 ell2, 'q2 ell2, 'c2) kraus_family\<close>
    and F :: \<open>'c2 \<Rightarrow> ('q2 ell2, 'q3 ell2, 'c3) kraus_family\<close>///
  shows \<open>cq_map_comp (cq_map_from_pointwise F) (cq_map_from_pointwise E) 
      =\<^sub>k\<^sub>r cq_map_from_pointwise (\<lambda>c. kf_map snd (kf_comp_dependent (\<lambda>d. F d) (E c)))\<close>
proof -
  have \<open>cq_map_comp (cq_map_from_pointwise F) (cq_map_from_pointwise E) =\<^sub>k\<^sub>r 
      cq_map_from_measurement
           (kf_map snd
             (kf_comp (kf_map snd (kf_comp_dependent F (kraus_map_partial_trace')))
               (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c)))
                 (kf_map snd (kf_comp_dependent E (kraus_map_partial_trace'))))))\<close>
    unfolding cq_map_from_pointwise_def
    by (rule cq_map_comp_cq_map_from_measurement)
  also have \<open>\<dots> = xxx\<close>





]


  have \<open>kf_map snd (kf_comp (kf_map snd (kf_comp_dependent F (kraus_map_partial_trace')))
         (kf_comp_dependent (\<lambda>c. kf_of_op (tensor_ell2_left (ket c)))
           (kf_map snd (kf_comp_dependent E (kraus_map_partial_trace')))))
    \<equiv>\<^sub>k\<^sub>r
    kf_map snd (kf_comp_dependent (\<lambda>c. kf_map snd (kf_comp_dependent F (E c))) (kraus_map_partial_trace'))\<close>
  proof -


    show a for a
      by x
  qed

  then
  show ?thesis
    unfolding cq_map_from_pointwise_def
    apply (rule_tac kraus_equivalent_trans)
     apply (rule cq_map_comp_cq_map_from_measurement)
    apply (rule cq_map_from_measurement_cong)
    by simp
qed

lemma cq_map_from_pointwise_cong: ///
  assumes \<open>\<And>x. kraus_equivalent (E x) (F x)\<close>
  shows \<open>kraus_equivalent (cq_map_from_pointwise E) (cq_map_from_pointwise F)\<close>
by -


lemma is_cq_map_cq_map_from_measurement[iff]: 
  assumes \<open>kf_map snd (kf_comp E cq_map_id) \<equiv>\<^sub>k\<^sub>r E\<close>
  shows \<open>is_cq_map (cq_map_from_measurement E)\<close>
by -

lemma cq_map_comp_id_left[simp]: \<open>cq_map_comp cq_map_id E = E\<close> if \<open>is_cq_map E\<close>
by -

lemma cq_map_comp_id_right[simp]: \<open>cq_map_comp E cq_map_id = E\<close> if \<open>is_cq_map E\<close>
by -

lemma kf_comp_partial_trace'_cq_map_id: \<open>kf_comp (kraus_map_partial_trace') cq_map_id
    \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>x. ((),x)) (kraus_map_partial_trace')\<close> ///
by -



(* lemma is_cq_map_cq_map_from_pointwise[iff]: 
  fixes E :: \<open>('c1 \<Rightarrow> ('q1 ell2, 'q2 ell2, 'c2) kraus_family)\<close>
  shows \<open>is_cq_map (cq_map_from_pointwise E)\<close>
proof (unfold cq_map_from_pointwise_def, rule is_cq_map_cq_map_from_measurement)
  let ?id = \<open>cq_map_id :: (('c1 \<times> 'q1) ell2, ('c1 \<times> 'q1) ell2, unit) kraus_family\<close>
  let ?lhs = \<open>kf_map snd
     (kf_comp (kf_map snd (kf_comp_dependent E (kraus_map_partial_trace'))) ?id)\<close>
    and ?rhs = \<open>kf_map snd (kf_comp_dependent E (kraus_map_partial_trace'))\<close>
  wlog bdd: \<open>bdd_above (range (kf_norm \<circ> E))\<close> goal \<open>?lhs \<equiv>\<^sub>k\<^sub>r ?rhs\<close>
    using negation
    by (simp add: kf_comp_dependent_invalid case_prod_unfold)
  have bdd1: \<open>bdd_above (range (kf_norm \<circ> (\<lambda>g. kraus_map_partial_trace')))\<close>
    by simp
  have bdd2: \<open>bdd_above ((kf_norm \<circ> (\<lambda>(_, f). E f)) ` kraus_map_domain (kf_comp (kraus_map_partial_trace') ?id))\<close>
  proof -
    have \<open>?thesis = bdd_above ((kf_norm \<circ> E) ` ((\<lambda>(_, f). f) ` kraus_map_domain (kf_comp (kraus_map_partial_trace') ?id)))\<close>
      apply (rule arg_cong[where f=bdd_above])
      by force
    also have \<open>\<dots>\<close>
      using bdd apply (rule bdd_above_mono2)
      by auto
    finally show ?thesis
      by -
  qed
  have bdd3: \<open>bdd_above ((kf_norm \<circ> E) ` kraus_map_domain (kraus_map_partial_trace'))\<close>
    using bdd bdd_above_mono2 by force

  show  \<open>?lhs \<equiv>\<^sub>k\<^sub>r ?rhs\<close>
  proof (rule kraus_equivalent'I_from_equivalent)
    fix x :: 'c2
    define E_x where \<open>E_x e = kf_filter ((=) x) (E e)\<close> for e
    have aux1: \<open>(\<lambda>xa. x = snd xa) = (\<lambda>(e,f). x=f \<and> True)\<close>
      by auto
    have aux2: \<open>(\<lambda>xa. x = (case xa of (c, d) \<Rightarrow> d)) = (\<lambda>(e,f). x=f \<and> True)\<close>
      by auto
    from bdd
    have bdd4: \<open>bdd_above (range (kf_norm \<circ> E_x))\<close>
      apply (rule bdd_above_mono2)
      by (auto intro!: kf_norm_filter simp: E_x_def)
    have bdd5: \<open>bdd_above ((kf_norm \<circ> (\<lambda>(_, f). E_x f)) ` kraus_map_domain (kf_comp (kraus_map_partial_trace') ?id))\<close>
    proof -
      have \<open>?thesis = bdd_above ((kf_norm \<circ> E_x) ` ((\<lambda>(_, f). f) ` kraus_map_domain (kf_comp (kraus_map_partial_trace') ?id)))\<close>
        apply (rule arg_cong[where f=bdd_above])
        by force
      also have \<open>\<dots>\<close>
        using bdd4 apply (rule bdd_above_mono2)
        by auto
      finally show ?thesis
        by -
    qed

    have \<open>kf_filter ((=) x) ?lhs = kf_map snd
     (kf_comp (kf_map (\<lambda>(c, d). d)
         (kf_comp_dependent E_x (kraus_map_partial_trace'))) cq_map_id)\<close>
      by (simp only: kf_filter_true kf_filter_comp_dependent[OF bdd3] aux2 aux1
          kf_filter_map_outcome kf_filter_comp kf_filter_map_outcome E_x_def[abs_def])
    also have \<open>\<dots> =\<^sub>k\<^sub>r kf_comp (kf_comp_dependent E_x (kraus_map_partial_trace')) cq_map_id\<close>
      by (simp add: kraus_equivalent_def kf_comp_apply)
    also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>((g, f), e). (g, f, e))
       (kf_comp_dependent (\<lambda>(_, f). E_x f) (kf_comp (kraus_map_partial_trace') cq_map_id))\<close>
      using bdd1 bdd4 by (auto intro!: kf_comp_dependent_assoc' simp only: kf_comp_def)
    also have \<open>\<dots> =\<^sub>k\<^sub>r (kf_comp_dependent (\<lambda>(_, f). E_x f) (kf_comp (kraus_map_partial_trace') cq_map_id))\<close>
      by (simp add: kraus_equivalent_def)
    also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_comp_dependent (\<lambda>(_, f). E_x f) (kf_map (\<lambda>x. ((),x)) (kraus_map_partial_trace'))\<close>
      by (auto intro!: kf_comp_dependent_cong' bdd5 kf_comp_partial_trace'_cq_map_id)
    also have \<open>\<dots> =\<^sub>k\<^sub>r kf_map (\<lambda>(c, d). d) (kf_comp_dependent E_x (kraus_map_partial_trace'))\<close>
      (* TODO: missing lemma for: comp_def (map_outcome f E) (G) = \<dots> *)
      by -
    also have \<open>\<dots> = kf_filter ((=) x) (kf_map (\<lambda>(c, d). d) (kf_comp_dependent E (kraus_map_partial_trace')))\<close>
      by (simp only: kf_filter_true kf_filter_comp_dependent[OF bdd3] aux2 
          kf_filter_map_outcome E_x_def[abs_def])
    finally show \<open>kf_filter ((=) x) ?lhs =\<^sub>k\<^sub>r kf_filter ((=) x) ?rhs\<close>
      by -
  qed
qed *)

lemma kf_norm_cq_map_from_pointwise:
  assumes \<open>\<And>x. kf_norm (E x) \<le> B\<close>
  shows \<open>kf_norm (cq_map_from_pointwise E) \<le> B\<close>
  by -

lemma kf_norm_cq_map_to_pointwise:
  \<open>kf_norm (cq_map_to_pointwise E x) \<le> kf_norm E\<close>
  by -


end

