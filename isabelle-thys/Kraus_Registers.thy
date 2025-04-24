theory Kraus_Registers
  imports Kraus_Maps.Kraus_Maps Registers2.Registers_Unsorted
begin

unbundle kraus_map_syntax

lift_definition kf_apply_qregister :: \<open>('a,'b) qregister \<Rightarrow> ('a ell2, 'a ell2, 'x) kraus_family \<Rightarrow> ('b ell2, 'b ell2, 'x) kraus_family\<close> is
  \<open>\<lambda>(Q :: ('a,'b) qregister). if qregister Q then image (\<lambda>(E,x). (apply_qregister Q E, x)) else (\<lambda>_. {})\<close>
proof (rule CollectI, erule CollectE, rename_tac Q E)
  fix Q :: \<open>('a,'b) qregister\<close> and E :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2 \<times> 'x) set\<close>
  assume \<open>kraus_family E\<close>
  show \<open>kraus_family ((if qregister Q then image (\<lambda>(E,x). (apply_qregister Q E, x)) else (\<lambda>_. {})) E)\<close>
  proof -
    wlog [simp]: \<open>qregister Q\<close>
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

lemma kf_apply_qregister_non_qregister[simp]: \<open>kf_apply_qregister non_qregister \<EE> = 0\<close>
  apply transfer' by simp

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
  then have [iff]: \<open>qregister Q\<close>
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
    using negation by (auto intro!: kf_eqI simp add: kf_apply_on_eq0I non_qregister)
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
    using hypothesis kf_eq_weak_def non_qregister by force
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


definition km_apply_qregister :: \<open>('a,'b) qregister \<Rightarrow> (('a ell2, 'a ell2) trace_class \<Rightarrow> ('a ell2, 'a ell2) trace_class) \<Rightarrow> (('b ell2, 'b ell2) trace_class \<Rightarrow> ('b ell2, 'b ell2) trace_class)\<close> where
  \<open>km_apply_qregister Q \<EE> = kf_apply (kf_apply_qregister Q (km_some_kraus_family \<EE> :: (_,_,unit) kraus_family))\<close>

lemma km_apply_qregister_kf_apply:
  assumes \<open>qregister Q\<close>
  shows \<open>km_apply_qregister Q (kf_apply \<EE>) = kf_apply (kf_apply_qregister Q \<EE>)\<close>
  by (auto intro!: ext kf_apply_eqI kf_apply_qregister_cong_weak simp: kf_eq_weak_def km_apply_qregister_def)

lemma km_apply_qregister_invalid_Q[simp]: \<open>km_apply_qregister non_qregister \<EE> = 0\<close>
  by (auto intro!: kf_apply_eq0I ext simp add: km_apply_qregister_def)

(* TODO same for km_ *)
lemma kf_apply_qregister_0[simp]: \<open>kf_apply_qregister Q 0 = 0\<close>
  apply (transfer' fixing: Q)
  by simp

lemma km_apply_qregister_invalid_\<EE>: \<open>km_apply_qregister Q \<EE> = 0\<close> if \<open>\<not> kraus_map \<EE>\<close>
  using that
  by (auto intro!: simp add: km_apply_qregister_def km_some_kraus_family_invalid kf_apply_qregister_0)

lemma kf_filter_kf_apply_qregister:
  \<open>kf_filter P (kf_apply_qregister Q \<EE>) = kf_apply_qregister Q (kf_filter P \<EE>)\<close>
  apply (transfer' fixing: Q)
  by force

(* TODO move *)
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

(* TODO move *)
lemma kf_annotate_eq_weak: \<open>kf_annotate \<EE> =\<^sub>k\<^sub>r \<EE>\<close>
  apply (rule kf_eq_weakI)
  unfolding kf_apply.rep_eq kf_annotate.rep_eq
  apply (subst infsum_reindex)
  by (auto intro!: inj_onI simp: o_def case_prod_unfold)



lemma kf_apply_qregister_pair_tensor_id_weak:
  assumes \<open>qcompatible Q R\<close>
  shows \<open>kf_apply_qregister \<lbrakk>Q,R\<rbrakk>\<^sub>q (kf_tensor \<EE> kf_id) =\<^sub>k\<^sub>r kf_apply_qregister Q \<EE>\<close>
    (is ?goal)
proof -
  define QR where \<open>QR = \<lbrakk>Q,R\<rbrakk>\<^sub>q\<close>
  with assms have [iff]: \<open>qregister QR\<close>
    by blast
  then have [iff]: \<open>qregister Q\<close>
    using assms distinct_qvarsL by blast
    
  have [simp]: \<open>apply_qregister QR (a \<otimes>\<^sub>o id_cblinfun) = apply_qregister Q a\<close> for a
    by (metis QR_def apply_qregister_extend_pair_right assms)
  have \<open>kf_apply_qregister QR (kf_tensor \<EE> kf_id) =\<^sub>k\<^sub>r kf_apply_qregister QR (kf_tensor_raw \<EE> kf_id)\<close>
    apply (rule kf_apply_qregister_cong_weak)
    by (simp add: kf_eq_weak_def kf_tensor_def)
  also have \<open>\<dots> = kf_map_inj (\<lambda>(x,E). (E, id_cblinfun, x, ())) (kf_apply_qregister Q (kf_annotate \<EE>))\<close>
    apply (rule Rep_kraus_family_inject[THEN iffD1])
    apply (simp add: kf_apply_qregister.rep_eq kf_tensor_raw.rep_eq kf_of_op.rep_eq
        image_image kf_map_inj.rep_eq case_prod_beta kf_annotate.rep_eq
        flip: kf_of_op_id)
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

  have [iff]: \<open>qregister Q\<close>
    using assms iso_qregister_def' by blast
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

(* TODO same for km_ *)
lemma kf_apply_qregister_chain:
  shows \<open>kf_apply_qregister (qregister_chain Q R) \<EE> = kf_apply_qregister Q (kf_apply_qregister R \<EE>)\<close>
proof -
  wlog \<open>qregister Q \<and> qregister R\<close>
    using negation
    by (auto simp: non_qregister)
  then have [iff]: \<open>qregister Q\<close> \<open>qregister R\<close> \<open>qregister (qregister_chain Q R)\<close>
    by auto
  then
  show ?thesis
    apply (transfer' fixing: Q R)
    by (simp add: case_prod_unfold image_image)
qed

lemma kf_apply_qregister_transform_qregister_weak:
(* TODO: also kr_eq-form (by reduction to this) *)
  assumes \<open>unitary U\<close>
  shows \<open>kf_apply_qregister (transform_qregister U) \<EE> =\<^sub>k\<^sub>r kf_comp (kf_of_op U) (kf_comp \<EE> (kf_of_op (U*)))\<close>
  apply (rule kf_eq_weakI)
  by (simp add: kf_apply_qregister_iso_qregister_explicit apply_qregister_tc_transform_qregister
        iso_qregister_transform_qregister inv_transform_qregister assms kf_comp_apply kf_of_op_apply)

lemma kf_apply_qregister_qFst_weak:
(* TODO: also kr_eq-form (by reduction to this) *)
  shows \<open>kf_apply_qregister qFst \<EE> =\<^sub>k\<^sub>r kf_tensor \<EE> kf_id\<close>
proof -
  have \<open>kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q \<EE> *\<^sub>k\<^sub>r tc_tensor t u = kf_tensor \<EE> kf_id *\<^sub>k\<^sub>r tc_tensor t u\<close> 
    for t and u :: \<open>('b ell2, 'b ell2) trace_class\<close>
  proof -
    have \<open>kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q \<EE> *\<^sub>k\<^sub>r tc_tensor t u
       = kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q \<EE> *\<^sub>k\<^sub>r apply_qregister_tc \<lbrakk>#1,#2.\<rbrakk>\<^sub>q (tc_tensor t u)\<close>
      by simp
    also have \<open>\<dots> = apply_qregister_tc \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q (tc_tensor (\<EE> *\<^sub>k\<^sub>r t) u)\<close>
      apply (subst kf_apply_qregister_apply_tensor)
      by (simp_all add: QCOMPLEMENT_fst QREGISTER_of_qFst QREGISTER_of_qSnd Registers_Automation.qcomplements_tac_aux1)
    also have \<open>\<dots> = tc_tensor (\<EE> *\<^sub>k\<^sub>r t) u\<close>
      by simp
    also have \<open>\<dots> = kf_tensor \<EE> kf_id *\<^sub>k\<^sub>r tc_tensor t u\<close>
      by (simp add: kf_apply_tensor)
    finally show ?thesis
      by -
  qed
  then show ?thesis
    apply (rule_tac kf_eq_weak_from_separatingI)
     apply (rule separating_set_bounded_clinear_tc_tensor)
    by auto
qed

lemma kf_bound_apply_qregister:
  fixes Q :: \<open>('a,'b) qregister\<close>
  shows \<open>kf_bound (kf_apply_qregister Q \<EE>) = apply_qregister Q (kf_bound \<EE>)\<close>
proof -
  wlog [iff]: \<open>qregister Q\<close>
    using negation
    by (simp add: non_qregister)
  from qregister_decomposition[OF this]
  have \<open>let 'g::type = qregister_decomposition_basis Q in kf_bound (kf_apply_qregister Q \<EE>) = apply_qregister Q (kf_bound \<EE>)\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>U :: ('a \<times> 'g) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> Q = qregister_chain (transform_qregister U) \<lbrakk>#1\<rbrakk>\<^sub>q\<close>
    then obtain U :: \<open>('a \<times> 'g) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where
      [iff]: \<open>unitary U\<close> and QU: \<open>Q = qregister_chain (transform_qregister U) \<lbrakk>#1\<rbrakk>\<^sub>q\<close>
      by auto
    have \<open>kf_bound (kf_apply_qregister Q \<EE>) = kf_bound (kf_apply_qregister (transform_qregister U) (kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q \<EE>))\<close>
      by (simp add: QU kf_apply_qregister_chain)
    also have \<open>\<dots> = kf_bound (kf_comp (kf_of_op U) (kf_comp (kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q \<EE>) (kf_of_op (U*))))\<close>
      apply (rule kf_bound_cong)
      apply (rule kf_apply_qregister_transform_qregister_weak)
      by simp
    also have \<open>\<dots> = kf_bound (kf_comp (kf_of_op U) (kf_comp (kf_tensor \<EE> kf_id) (kf_of_op (U*))))\<close>
      apply (rule kf_bound_cong)
      apply (rule kf_comp_cong_weak)
       apply simp
      apply (rule kf_comp_cong_weak)
       apply (rule kf_apply_qregister_qFst_weak)
      by simp
    also have \<open>\<dots> = kf_bound (kf_comp (kf_tensor \<EE> kf_id) (kf_of_op (U*)))\<close>
      by (simp add: kf_bound_comp_iso)
    also have \<open>\<dots> = sandwich U *\<^sub>V kf_bound (kf_tensor \<EE> kf_id)\<close>
      by (simp add: kf_bound_comp_of_op)
    also have \<open>\<dots> = sandwich U *\<^sub>V (kf_bound \<EE> \<otimes>\<^sub>o id_cblinfun)\<close>
      by (simp add: kf_bound_tensor)
    also have \<open>\<dots> = apply_qregister Q (kf_bound \<EE>)\<close>
      by (simp add: QU apply_qregister_qFst transform_qregister.rep_eq)
    finally
    show \<open>kf_bound (kf_apply_qregister Q \<EE>) = apply_qregister Q (kf_bound \<EE>)\<close>
      by -
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

lemma km_bound_apply_qregister:
  fixes Q :: \<open>('a,'b) qregister\<close>
  assumes \<open>kraus_map \<EE>\<close>
  shows \<open>km_bound (km_apply_qregister Q \<EE>) = apply_qregister Q (km_bound \<EE>)\<close>
proof -
  wlog [iff]: \<open>qregister Q\<close>
    using negation by (simp add: non_qregister)
  obtain \<FF> :: \<open>('a ell2, 'a ell2, unit) kraus_family\<close> where \<EE>\<FF>: \<open>\<EE> = kf_apply \<FF>\<close>
    using assms kraus_map_def_raw by blast
  then show ?thesis
    by (simp add: kf_bound_apply_qregister km_apply_qregister_kf_apply km_bound_kf_bound)
qed


(* TODO same for km_ *)
lemma kf_norm_apply_qregister[simp]:
  assumes \<open>qregister Q\<close>
  shows \<open>kf_norm (kf_apply_qregister Q \<EE>) = kf_norm \<EE>\<close>
  by (simp add: assms apply_qregister_norm kf_norm_def kf_bound_apply_qregister)

lemma kf_domain_apply_qregister:
  assumes [iff]: \<open>qregister Q\<close>
  shows \<open>kf_domain (kf_apply_qregister Q \<EE>) = kf_domain \<EE>\<close>
proof (rule Set.set_eqI)
  fix x
  have \<open>x \<in> kf_domain (kf_apply_qregister Q \<EE>) \<longleftrightarrow> (\<exists>E. E \<noteq> 0 \<and> (E,x) \<in> Rep_kraus_family (kf_apply_qregister Q \<EE>))\<close>
    apply (transfer' fixing: )
    by (force simp: case_prod_unfold)
  also have \<open>\<dots> \<longleftrightarrow> (\<exists>E F. E \<noteq> 0 \<and> E = apply_qregister Q F \<and> (F,x) \<in> Rep_kraus_family \<EE>)\<close>
    by (force simp add: kf_apply_qregister.rep_eq)
  also have \<open>\<dots> \<longleftrightarrow> (\<exists>E F. F \<noteq> 0 \<and> E = apply_qregister Q F \<and> (F,x) \<in> Rep_kraus_family \<EE>)\<close>
    using apply_qregister_inject' by force
  also have \<open>\<dots> \<longleftrightarrow> (\<exists>F. F \<noteq> 0 \<and> (F,x) \<in> Rep_kraus_family \<EE>)\<close>
    by presburger
  also have \<open>\<dots> \<longleftrightarrow> x \<in> kf_domain \<EE>\<close>
    apply (transfer' fixing: x)
    by force
  finally show \<open>x \<in> kf_domain (kf_apply_qregister Q \<EE>) \<longleftrightarrow> x \<in> kf_domain \<EE>\<close>
    by -
qed



lemma kf_comp_dependent_raw_apply_qregister: 
  fixes Q :: \<open>('a,'b) qregister\<close>
  assumes [iff]: \<open>qregister Q\<close>
  shows \<open>kf_comp_dependent_raw (\<lambda>x. kf_apply_qregister Q (\<EE> x)) (kf_apply_qregister Q \<FF>)
      = kf_map_inj (\<lambda>(E,F,x,y). (apply_qregister Q E, apply_qregister Q F, x, y))
            (kf_apply_qregister Q (kf_comp_dependent_raw \<EE> \<FF>))\<close>
    (is \<open>?lhs = ?rhs\<close>)
proof (cases \<open>bdd_above ((\<lambda>x. kf_norm (\<EE> x)) ` kf_domain \<FF>)\<close>)
  case True
  then have bddQ: \<open>bdd_above ((\<lambda>x. kf_norm (kf_apply_qregister Q (\<EE> x))) ` kf_domain (kf_apply_qregister Q \<FF>))\<close>
    apply (rule bdd_above_mono2)
    by (auto simp: kf_norm_apply_qregister kf_domain_apply_qregister)

  show ?thesis
  proof (intro Rep_kraus_family_inject[THEN iffD1] Set.set_eqI)
    fix tuple :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'c \<times> 'd\<close>
    obtain QEF QE QF x y where tuple_def: \<open>tuple = (QEF,QF,QE,y,x)\<close>
      apply atomize_elim
      by (auto intro!: exI prod_eqI)
    have \<open>tuple \<in> Rep_kraus_family ?lhs \<longleftrightarrow>
         (QF,y) \<in> Rep_kraus_family (kf_apply_qregister Q \<FF>)
       \<and> (QE,x) \<in> Rep_kraus_family (kf_apply_qregister Q (\<EE> y))
       \<and> QEF = QE o\<^sub>C\<^sub>L QF\<close>
      by (force simp add: tuple_def kf_comp_dependent_raw.rep_eq bddQ True kf_domain_apply_qregister)
    also have \<open>\<dots> \<longleftrightarrow> (\<exists>F. (apply_qregister Q F = QF) \<and> (F,y) \<in> Rep_kraus_family \<FF>) \<and>
             (\<exists>E. (apply_qregister Q E = QE) \<and> (E,x) \<in> Rep_kraus_family (\<EE> y)) \<and>
             QEF = QE o\<^sub>C\<^sub>L QF\<close>
      by (auto simp: kf_apply_qregister.rep_eq)
    also have \<open>\<dots> \<longleftrightarrow> (\<exists>E F EF. QE = apply_qregister Q E \<and> QF = apply_qregister Q F \<and> QEF = apply_qregister Q EF
          \<and> EF = E o\<^sub>C\<^sub>L F \<and> (F,y) \<in> Rep_kraus_family \<FF> \<and> (E,x) \<in> Rep_kraus_family (\<EE> y))\<close>
      by (metis qregister_compose)
    also have \<open>\<dots> \<longleftrightarrow> (\<exists>E F EF. QE = apply_qregister Q E \<and> QF = apply_qregister Q F \<and> QEF = apply_qregister Q EF
          \<and> (EF, F, E, y, x) \<in> Rep_kraus_family (kf_comp_dependent_raw \<EE> \<FF>))\<close>
      using True
      by (force simp: kf_comp_dependent_raw.rep_eq)
    also have \<open>\<dots> \<longleftrightarrow> (\<exists>E F. QE = apply_qregister Q E \<and> QF = apply_qregister Q F 
          \<and> (QEF, F, E, y, x) \<in> Rep_kraus_family (kf_apply_qregister Q (kf_comp_dependent_raw \<EE> \<FF>)))\<close>
      by (force simp: kf_apply_qregister.rep_eq)
    also have \<open>\<dots> \<longleftrightarrow> tuple \<in> Rep_kraus_family ?rhs\<close>
      by (force simp: tuple_def kf_map_inj.rep_eq)
    finally show \<open>tuple \<in> Rep_kraus_family ?lhs \<longleftrightarrow> tuple \<in> Rep_kraus_family ?rhs\<close>
      by -
  qed
next
  case False
  then have nbddQ: \<open>\<not> bdd_above ((\<lambda>x. kf_norm (kf_apply_qregister Q (\<EE> x))) ` kf_domain (kf_apply_qregister Q \<FF>))\<close>
    by (metis (no_types, lifting) assms image_cong kf_domain_apply_qregister kf_norm_apply_qregister)
  show ?thesis
    apply (transfer' fixing: Q \<EE> \<FF>)
    using False nbddQ by auto
qed

lemma kf_element_weight_kf_apply_qregister:
  assumes \<open>qregister Q\<close>
  shows \<open>kf_element_weight (kf_apply_qregister Q \<EE>) (apply_qregister Q E)
      = kf_element_weight \<EE> E\<close>
proof -
  have inj: \<open>inj_on (\<lambda>(E, y). (apply_qregister Q E, y)) A\<close> for A
    by (smt (verit, ccfv_SIG) apply_qregister_inject' assms case_prod_unfold inj_onI prod.collapse prod.inject)
  have \<open>kf_element_weight (kf_apply_qregister Q \<EE>) (apply_qregister Q E)
    = (\<Sum>\<^sub>\<infinity>(F, x) | (F, x) \<in> (\<lambda>(E, y). (apply_qregister Q E, y)) ` Rep_kraus_family \<EE> \<and> (\<exists>r>0. apply_qregister Q E = r *\<^sub>R F).
       (norm F)\<^sup>2)\<close>
    by (simp add: kf_element_weight_def kf_similar_elements_def kf_apply_qregister.rep_eq assms)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F, x) \<in> (\<lambda>(E,y). (apply_qregister Q E, y)) ` {(F,x) \<in> Rep_kraus_family \<EE>. (\<exists>r>0. E = r *\<^sub>R F)}. (norm F)\<^sup>2)\<close>
    apply (rule arg_cong[where f=\<open>infsum _\<close>])
    apply (auto intro!: imageI simp: case_prod_unfold apply_qregister_scaleR )
    by (metis apply_qregister_inject' apply_qregister_scaleR assms)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,x) | (F, x) \<in> Rep_kraus_family \<EE> \<and> (\<exists>r>0. E = r *\<^sub>R F).
                      (norm (apply_qregister Q F))\<^sup>2)\<close>
    apply (subst infsum_reindex)
    apply (rule inj)
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,x) | (F, x) \<in> Rep_kraus_family \<EE> \<and> (\<exists>r>0. E = r *\<^sub>R F). (norm F)\<^sup>2)\<close>
    using apply_qregister_norm assms by fastforce
  also have \<open>\<dots> = kf_element_weight \<EE> E\<close>
    by (simp add: kf_element_weight_def kf_similar_elements_def)
  finally show ?thesis
    by -
qed

lemma kf_similar_elements_kf_apply_qregister_outside: 
  assumes \<open>E \<notin> range (apply_qregister Q)\<close>
  shows \<open>kf_similar_elements (kf_apply_qregister Q \<EE>) E = {}\<close>
  apply (simp add: kf_similar_elements_def kf_apply_qregister.rep_eq)
  by (smt (verit, best) apply_qregister_scaleR assms case_prod_unfold fst_conv imageE rangeI)

lemma kf_element_weight_kf_apply_qregister_outside:
  assumes \<open>E \<notin> range (apply_qregister Q)\<close>
  shows \<open>kf_element_weight (kf_apply_qregister Q \<EE>) E = 0\<close>
  by (auto intro!: simp: kf_element_weight_def kf_similar_elements_kf_apply_qregister_outside assms)

lemma kf_apply_qregister_kf_map:
  shows \<open>kf_apply_qregister Q (kf_map f \<EE>) = kf_map f (kf_apply_qregister Q \<EE>)\<close>
proof -
  wlog [iff]: \<open>qregister Q\<close>
    using negation
    by (simp add: non_qregister)
  show ?thesis
  proof (rule Rep_kraus_family_inject[THEN iffD1], rule Set.set_eqI)
    fix Ex :: \<open> 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2 \<times> 'b\<close>
    obtain E x where Ex_def: \<open>Ex = (E,x)\<close>
      by fastforce

    have \<open>Ex \<in> Rep_kraus_family (kf_apply_qregister Q (kf_map f \<EE>)) \<longleftrightarrow>
        (E,x) \<in> (\<lambda>(E, y). (apply_qregister Q E, y)) ` Rep_kraus_family (kf_map f \<EE>)\<close>
      by (simp add: kf_apply_qregister.rep_eq Ex_def)

    have \<open>Ex \<in> Rep_kraus_family (kf_map f (kf_apply_qregister Q \<EE>))
      \<longleftrightarrow> ((norm E)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>xa. f xa = x) (kf_apply_qregister Q \<EE>)) E \<and> E \<noteq> 0)\<close>
      by (simp add: kf_map.rep_eq Ex_def)
    also have \<open>\<dots> \<longleftrightarrow> (norm E)\<^sup>2 = kf_element_weight (kf_apply_qregister Q (kf_filter (\<lambda>xa. f xa = x) \<EE>)) E \<and> E \<noteq> 0\<close>
      by (simp add: kf_filter_kf_apply_qregister)
    also have \<open>\<dots> \<longleftrightarrow> E \<in> range (apply_qregister Q) \<and> 
     (norm E)\<^sup>2 = kf_element_weight (kf_apply_qregister Q (kf_filter (\<lambda>xa. f xa = x) \<EE>)) E \<and> E \<noteq> 0\<close>
      using kf_element_weight_kf_apply_qregister_outside  kf_element_weight_0_right apply simp
      by (smt (verit, ccfv_threshold) kf_element_weight_kf_apply_qregister_outside norm_eq_zero zero_eq_power2)
    also have \<open>\<dots> \<longleftrightarrow> (\<exists>F. E = apply_qregister Q F \<and> 
     (norm E)\<^sup>2 = kf_element_weight (kf_apply_qregister Q (kf_filter (\<lambda>xa. f xa = x) \<EE>)) E \<and> E \<noteq> 0)\<close>
      by auto
    also have \<open>\<dots> \<longleftrightarrow> (\<exists>F. E = apply_qregister Q F \<and> 
     (norm E)\<^sup>2 = kf_element_weight (kf_apply_qregister Q (kf_filter (\<lambda>xa. f xa = x) \<EE>)) (apply_qregister Q F) \<and> E \<noteq> 0)\<close>
      by auto
    also have \<open>\<dots> \<longleftrightarrow> (\<exists>F. E = apply_qregister Q F \<and> 
     (norm E)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>xa. f xa = x) \<EE>) F \<and> E \<noteq> 0)\<close>
      by (simp add: kf_element_weight_kf_apply_qregister)
    also have \<open>\<dots> \<longleftrightarrow> (\<exists>F. E = apply_qregister Q F \<and> 
     (norm F)\<^sup>2 = kf_element_weight (kf_filter (\<lambda>xa. f xa = x) \<EE>) F \<and> F \<noteq> 0)\<close>
      using apply_qregister_inject' apply_qregister_norm by fastforce
    also have \<open>\<dots> \<longleftrightarrow> (\<exists>F. E = apply_qregister Q F \<and> (F,x) \<in> Rep_kraus_family (kf_map f \<EE>))\<close>
      by (smt (verit, ccfv_threshold) Product_Type.Collect_case_prodD apply_qregister_inject' apply_qregister_norm apply_qregister_of_0
          \<open>qregister Q\<close> calculation case_prodI kf_element_weight_kf_apply_qregister kf_filter_kf_apply_qregister kf_map.rep_eq local.Ex_def
          mem_Collect_eq norm_AadjA prod.sel(1) snd_conv)
    also have \<open>\<dots> \<longleftrightarrow> (E,x) \<in> (\<lambda>(E, y). (apply_qregister Q E, y)) ` Rep_kraus_family (kf_map f \<EE>)\<close>
      by fast
    also have \<open>\<dots> \<longleftrightarrow> Ex \<in> Rep_kraus_family (kf_apply_qregister Q (kf_map f \<EE>))\<close>
      by (simp add: kf_apply_qregister.rep_eq Ex_def)
    finally show \<open>Ex \<in> Rep_kraus_family (kf_apply_qregister Q (kf_map f \<EE>)) \<longleftrightarrow> Ex \<in> Rep_kraus_family (kf_map f (kf_apply_qregister Q \<EE>))\<close>
      by simp
  qed
qed





lemma kf_comp_dependent_apply_qregister: 
  assumes \<open>qregister Q\<close>
  shows \<open>kf_comp_dependent (\<lambda>x. kf_apply_qregister Q (\<EE> x)) (kf_apply_qregister Q \<FF>) = kf_apply_qregister Q (kf_comp_dependent \<EE> \<FF>)\<close>
proof -
  have [simp]: \<open>inj_on (\<lambda>(E, F, x, y). (apply_qregister Q E, apply_qregister Q F, x, y)) X\<close> for X
    using inj_qregister[OF assms] by (auto simp add: inj_on_def)
  have [simp]: \<open>(\<lambda>x. snd (snd x)) = (\<lambda>(F, E, x). x)\<close>
    by auto
  show ?thesis
    by (simp add: kf_comp_dependent_def assms kf_comp_dependent_raw_apply_qregister
        kf_map_kf_map_inj_comp o_def id_def kf_apply_qregister_kf_map
        case_prod_beta)
qed

lemma kf_comp_apply_qregister:
  assumes \<open>qregister Q\<close>
  shows \<open>kf_comp (kf_apply_qregister Q \<EE>) (kf_apply_qregister Q \<FF>) = kf_apply_qregister Q (kf_comp \<EE> \<FF>)\<close>
  by (simp add: assms kf_comp_def kf_comp_dependent_apply_qregister)

lemma km_apply_qregister_comp:
  assumes \<open>kraus_map \<EE>\<close> and \<open>kraus_map \<FF>\<close>
  shows \<open>km_apply_qregister Q \<EE> (km_apply_qregister Q \<FF> t) = km_apply_qregister Q (\<EE> o \<FF>) t\<close>
proof -
  have \<open>km_apply_qregister Q \<EE> (km_apply_qregister Q \<FF> t)
     = kf_comp (kf_apply_qregister Q (km_some_kraus_family \<EE>)) (kf_apply_qregister Q (km_some_kraus_family \<FF>)) *\<^sub>k\<^sub>r t\<close>
    by (simp add: km_apply_qregister_def kf_comp_apply)
  also have \<open>\<dots> = kf_apply_qregister Q (kf_comp (km_some_kraus_family \<EE>) (km_some_kraus_family \<FF>)) *\<^sub>k\<^sub>r t\<close>
    apply (cases \<open>qregister Q\<close>)
    by (simp_all add: kf_comp_apply_qregister non_qregister)
  also have \<open>\<dots> = kf_apply_qregister Q (km_some_kraus_family (\<EE> o \<FF>)) *\<^sub>k\<^sub>r t\<close>
    apply (rule kf_apply_eqI)
    apply (rule kf_apply_qregister_cong_weak)
    by (simp add: assms(1,2) kf_comp_apply kf_eq_weak_def kraus_map_comp)
  also have \<open>\<dots> = km_apply_qregister Q (\<EE> o \<FF>) t\<close>
    by (simp add: km_apply_qregister_def)
  finally show ?thesis
    by -
qed


definition kf_map_with_auxiliary_state ::
  \<open>('c ell2, 'c ell2) trace_class \<Rightarrow> (('a\<times>'c) ell2, ('b\<times>'d) ell2, 'x) kraus_family \<Rightarrow> ('a ell2, 'b ell2, 'x) kraus_family\<close> where
  \<open>kf_map_with_auxiliary_state \<rho> \<EE> = kf_map (\<lambda>((_,x),_). x) (kf_comp kf_partial_trace_right (kf_comp \<EE> (kf_tensor_right \<rho>)))\<close>

definition km_map_with_auxiliary_state where
  \<open>km_map_with_auxiliary_state \<rho> \<EE> = partial_trace o \<EE> o (\<lambda>\<sigma>. tc_tensor \<sigma> \<rho>)\<close>

lemma km_norm_map_with_auxiliary_state:
  assumes \<open>kraus_map \<EE>\<close> and \<open>\<rho> \<ge> 0\<close>
  shows \<open>km_norm (km_map_with_auxiliary_state \<rho> \<EE>) \<le> km_norm \<EE> * norm \<rho>\<close>
  by (auto intro!: assms km_comp_norm_leq[THEN order.trans] kraus_map_comp kraus_map_tensor_right mult_right_mono
      simp add: km_map_with_auxiliary_state_def kf_norm_tensor_right assms)

definition kf_local_register :: 
  \<open>'a QREGISTER \<Rightarrow> ('a ell2, 'a ell2) trace_class \<Rightarrow> ('a ell2, 'a ell2, 'x) kraus_family \<Rightarrow> ('a ell2, 'a ell2, 'x) kraus_family\<close> where
  \<open>kf_local_register Q \<rho> \<EE> = kf_map_with_auxiliary_state \<rho> (kf_map (\<lambda>((_,(x,_)),_). x)
        (kf_comp  (kf_of_op (swap_QREGISTER Q))
         (kf_comp (kf_tensor \<EE> kf_id)
                  (kf_of_op (swap_QREGISTER Q)))))\<close>


definition km_local_register where
  \<open>km_local_register Q \<rho> \<EE> = km_map_with_auxiliary_state \<rho> (
        sandwich_tc (swap_QREGISTER Q) o km_tensor \<EE> id o sandwich_tc (swap_QREGISTER Q))\<close>

lemma km_norm_local_register:
  assumes \<open>kraus_map \<EE>\<close> and \<open>\<rho> \<ge> 0\<close>
  shows \<open>km_norm (km_local_register Q \<rho> \<EE>) \<le> km_norm \<EE> * norm \<rho>\<close>
  using norm_swap_QREGISTER_01[of Q]
  by (auto intro!: km_comp_norm_leq[THEN order.trans] km_tensor_kraus_map
      km_norm_map_with_auxiliary_state[THEN order.trans] 
      kraus_map_comp mult_right_mono
      simp add: km_local_register_def km_norm_tensor km_norm_tensor assms)

lemma km_map_with_auxiliary_state_km_tensor:
  assumes \<open>kraus_map \<EE>\<close>
  assumes \<open>km_trace_preserving \<FF>\<close>
  shows \<open>km_map_with_auxiliary_state \<rho> (km_tensor \<EE> \<FF>) \<sigma> = trace_tc \<rho> *\<^sub>C \<EE> \<sigma>\<close>
  using assms
  by (auto intro!: ext simp add: km_tensor_kraus_map_exists km_map_with_auxiliary_state_def partial_trace_tensor km_trace_preserving_iff)


lemma km_local_register_bot: \<open>km_local_register \<bottom> \<rho> \<EE> \<sigma> = trace_tc \<rho> *\<^sub>C \<EE> \<sigma>\<close> if \<open>kraus_map \<EE>\<close>
proof -
  have \<open>km_local_register \<bottom> \<rho> \<EE> \<sigma> = km_map_with_auxiliary_state \<rho> (km_tensor \<EE> id) \<sigma>\<close>
    by (auto intro!: ext simp add: km_local_register_def o_def that)
  also have \<open>\<dots> = trace_tc \<rho> *\<^sub>C \<EE> \<sigma>\<close>
    by (auto intro!: ext simp add: km_map_with_auxiliary_state_km_tensor that)
  finally show ?thesis
    by -
qed

lemma km_local_register_kf_apply:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>km_local_register Q \<rho> (kf_apply \<EE>) = kf_apply (kf_local_register Q \<rho> \<EE>)\<close>
  by (auto intro!: ext 
      simp add: assms km_local_register_def kf_local_register_def  id_def
      km_map_with_auxiliary_state_def kf_map_with_auxiliary_state_def partial_trace_is_kf_partial_trace
      kf_comp_apply kf_apply_tensor_right kf_of_op_apply kf_id_apply[abs_def] kf_partial_trace_right_apply_singleton
      simp flip: km_tensor_kf_tensor)

lemma kraus_map_km_local_register[intro!]:
  assumes \<open>\<rho> \<ge> 0\<close>
  assumes \<open>kraus_map \<EE>\<close>
  shows \<open>kraus_map (km_local_register Q \<rho> \<EE>)\<close>
  by (metis assms(1,2) kf_apply_km_some_kraus_family km_local_register_kf_apply kraus_mapI)


lemma kf_apply_qregister_comp_dependent_raw: 
  \<open>kf_comp_dependent_raw (\<lambda>x. kf_apply_qregister Q (\<EE> x)) (kf_apply_qregister Q \<FF>) 
  = kf_map_inj (\<lambda>(A,B,x,y). (apply_qregister Q A, apply_qregister Q B, x, y)) (kf_apply_qregister Q (kf_comp_dependent_raw \<EE> \<FF>))\<close>
proof -
  wlog [iff]: \<open>qregister Q\<close>
    using negation
    by (simp add: non_qregister)
  have [simp]: \<open>(SIGMA (F, y):Rep_kraus_family (kf_apply_qregister Q \<FF>). Rep_kraus_family (kf_apply_qregister Q (\<EE> y)))
    = (\<lambda>((F,y),(E,x)). ((apply_qregister Q F, y),(apply_qregister Q E, x))) ` (SIGMA (F, y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
    by (auto intro!: image_eqI simp: case_prod_unfold kf_apply_qregister.rep_eq)
  show ?thesis
    apply (transfer' fixing: Q \<EE> \<FF>)
    by (simp add: kf_domain_apply_qregister  image_image case_prod_beta qregister_compose)
qed


lemma kf_apply_qregister_comp_dependent: \<open>kf_apply_qregister Q (kf_comp_dependent \<EE> \<FF>) = kf_comp_dependent (\<lambda>x. kf_apply_qregister Q (\<EE> x)) (kf_apply_qregister Q \<FF>)\<close>
proof -
  wlog [iff]: \<open>qregister Q\<close>
    using negation
    by (simp add: non_qregister)
  have [iff]: \<open>inj_on (\<lambda>(A, B, x, y). (apply_qregister Q A, apply_qregister Q B, x, y)) X\<close> for X
    by (auto intro!: inj_onI simp: apply_qregister_inject')
  show ?thesis
    apply (simp add: kf_comp_dependent_def kf_apply_qregister_kf_map
        kf_apply_qregister_comp_dependent_raw kf_map_kf_map_inj_comp)
    by (simp add: o_def case_prod_unfold)
qed

lemma kf_apply_qregister: \<open>kf_apply_qregister Q (kf_comp \<EE> \<FF>) = kf_comp (kf_apply_qregister Q \<EE>) (kf_apply_qregister Q \<FF>)\<close>
  by (simp add: kf_comp_def kf_apply_qregister_comp_dependent)


lemma kf_operators_kf_apply_qregister:
  assumes \<open>qregister Q\<close>
  shows \<open>kf_operators (kf_apply_qregister Q \<EE>) = apply_qregister Q ` kf_operators \<EE>\<close>
  apply (transfer' fixing: Q)
  using assms by force

lemma kf_operators_kf_apply_qregister_invalid:
  assumes \<open>\<not> qregister Q\<close>
  shows \<open>kf_operators (kf_apply_qregister Q \<EE>) = {}\<close>
  apply (transfer' fixing: Q)
  using assms by force

lemma km_operators_in_km_apply_qregister_invalid_Q:
  assumes \<open>\<not> qregister Q\<close>
  shows \<open>km_operators_in (km_apply_qregister Q \<EE>) X\<close>
  by (metis assms empty_subsetI kf_operators_kf_apply_qregister_invalid km_apply_qregister_def km_operators_in_def)

lemma km_operators_in_km_apply_qregister:
  assumes \<open>km_operators_in \<EE> S\<close>
  shows \<open>km_operators_in (km_apply_qregister Q \<EE>) (apply_qregister Q ` S)\<close>
proof -
  wlog [iff]: \<open>qregister Q\<close>
    using negation
    by (simp add: km_operators_in_km_apply_qregister_invalid_Q)
  from assms
  obtain \<EE>' :: \<open>(_,_,unit) kraus_family\<close> where \<EE>_def: \<open>\<EE> = kf_apply \<EE>'\<close> and \<EE>'S: \<open>kf_operators \<EE>' \<subseteq> S\<close>
    by (metis km_operators_in_def)
  have \<open>apply_qregister Q ` kf_operators \<EE>' \<subseteq> apply_qregister Q ` S\<close>
    using \<EE>'S by blast
  then show ?thesis
    by (simp add: \<EE>_def km_apply_qregister_kf_apply km_operators_in_kf_apply_flattened kf_operators_kf_apply_qregister)
qed

lemma kf_apply_qregister_partial_trace:
  shows \<open>kf_comp (kf_apply_qregister Q \<EE>) kf_partial_trace_right \<equiv>\<^sub>k\<^sub>r kf_map prod.swap (kf_comp (kf_partial_trace_right) (kf_apply_qregister (qregister_chain qFst Q) \<EE>))\<close>
proof (rule kf_eqI)
  wlog [simp]: \<open>qregister Q\<close>
    goal \<open>\<And>x \<rho>. kf_comp (kf_apply_qregister Q \<EE>) kf_partial_trace_right *\<^sub>k\<^sub>r @{x} \<rho> = kf_map prod.swap (kf_comp kf_partial_trace_right (kf_apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q Q) \<EE>)) *\<^sub>k\<^sub>r @{x} \<rho>\<close>
    using hypothesis non_qregister by force
  fix \<rho> :: \<open>(('a \<times> 'b) ell2, ('a \<times> 'b) ell2) trace_class\<close> and x :: \<open>'b \<times> 'c\<close>
  obtain x1 x2 where x: \<open>x = (x1,x2)\<close>
    by fastforce
  have swap_x: \<open>prod.swap -` {x} = {(x2,x1)}\<close>
    by (auto simp: x)
  define \<EE>x and Q1 :: \<open>(_,_\<times>'b) qregister\<close> where \<open>\<EE>x = kf_filter (\<lambda>x. x = x2) \<EE>\<close> and \<open>Q1 = qregister_chain qFst Q\<close>
  have [iff]: \<open>qregister Q1\<close>
    by (simp add: Q1_def)
  have \<open>kf_comp (kf_apply_qregister Q \<EE>) kf_partial_trace_right *\<^sub>k\<^sub>r @{x} \<rho>
      = kf_apply_qregister Q \<EE> *\<^sub>k\<^sub>r @{x2} (kf_partial_trace_right *\<^sub>k\<^sub>r @{x1} \<rho>)\<close>
    by (simp add: kf_comp_apply_on_singleton x)
  also have \<open>\<dots> = kf_apply_qregister Q \<EE> *\<^sub>k\<^sub>r @{x2} (sandwich_tc (tensor_ell2_right (ket x1)*) \<rho>)\<close>
    by (simp add: kf_partial_trace_right_apply_singleton)
  also have \<open>\<dots> = kf_apply_qregister Q \<EE>x *\<^sub>k\<^sub>r (sandwich_tc (tensor_ell2_right (ket x1)*) \<rho>)\<close>
    by (simp add: kf_filter_kf_apply_qregister kf_apply_on_def \<EE>x_def)
  also have \<open>\<dots> = sandwich_tc (tensor_ell2_right (ket x1)*) (kf_apply_qregister Q1 \<EE>x *\<^sub>k\<^sub>r \<rho>)\<close>
  proof -
    define EEx where \<open>EEx = Rep_kraus_family \<EE>x\<close>
    have \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>(\<lambda>(E,x). (apply_qregister Q E, x)) ` EEx. sandwich_tc E (sandwich_tc (tensor_ell2_right (ket x1)*) \<rho>)) =
          sandwich_tc (tensor_ell2_right (ket x1)*) (\<Sum>\<^sub>\<infinity>(E,x)\<in>(\<lambda>(E,x). (apply_qregister Q1 E, x)) ` EEx. sandwich_tc E \<rho>)\<close>
      (is \<open>?lhs = ?rhs\<close>)
    proof -
      have inj1: \<open>inj_on (\<lambda>(E, y). (apply_qregister Q E, y)) X\<close> for X
        by (smt (verit, del_insts) \<open>qregister Q\<close> apply_qregister_inject' case_prod_unfold inj_onI prod.collapse prod.inject)
      have inj2: \<open>inj_on (\<lambda>(E, y). (apply_qregister Q1 E, y)) X\<close> for X
        by (smt (verit, ccfv_threshold) \<open>qregister Q\<close> apply_qregister_inject' inj_onI prod.collapse prod.inject qFst_register
            qregister_chain_is_qregister split_def Q1_def)
      have sum: \<open>(\<lambda>(E, x). sandwich_tc (apply_qregister Q1 E) \<rho>) summable_on EEx\<close>
        using kf_apply_summable[where \<EE>=\<open>kf_apply_qregister Q1 \<EE>x\<close> and \<rho>=\<rho>]
        apply (simp add: kf_apply_qregister.rep_eq summable_on_reindex inj2)
        by (simp add: o_def case_prod_unfold EEx_def)
      have \<open>?lhs = (\<Sum>\<^sub>\<infinity>(E,x)\<in>EEx. sandwich_tc (apply_qregister Q E) (sandwich_tc (tensor_ell2_right (ket x1)*) \<rho>))\<close>
        apply (subst infsum_reindex)
         apply (simp add: inj1)
        by (simp add: inj1 o_def case_prod_unfold)
      also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>EEx. sandwich_tc (tensor_ell2_right (ket x1)*) (sandwich_tc (apply_qregister Q1 E) \<rho>))\<close>
      proof (rule infsum_cong, unfold case_prod_beta)
        fix Ex assume \<open>Ex \<in> EEx\<close>
        define E x where \<open>E = fst Ex\<close> and \<open>x = snd Ex\<close>
        have \<open>sandwich_tc (apply_qregister Q E) (sandwich_tc (tensor_ell2_right (ket x1)*) \<rho>)
            = sandwich_tc (apply_qregister Q E o\<^sub>C\<^sub>L tensor_ell2_right (ket x1)*) \<rho>\<close>
          by (simp add: sandwich_tc_compose)
        also have \<open>\<dots> = sandwich_tc (tensor_ell2_right (ket x1)* o\<^sub>C\<^sub>L (apply_qregister Q E \<otimes>\<^sub>o id_cblinfun)) \<rho>\<close>
          apply (rule arg_cong2[where f=sandwich_tc, OF _ refl])
          apply (rule tensor_ell2_extensionality)
          by (simp add: cblinfun.scaleC_right tensor_op_ell2)
        also have \<open>\<dots> = sandwich_tc (tensor_ell2_right (ket x1)* o\<^sub>C\<^sub>L apply_qregister Q1 E) \<rho>\<close>
          by (simp add: Q1_def qregister_chain_apply apply_qregister_fst)
        also have \<open>\<dots>= sandwich_tc (tensor_ell2_right (ket x1)*) (sandwich_tc (apply_qregister Q1 E) \<rho>)\<close>
          by (simp add: sandwich_tc_compose)
        finally show \<open>sandwich_tc (apply_qregister Q E) (sandwich_tc (tensor_ell2_right (ket x1)*) \<rho>)
             = sandwich_tc (tensor_ell2_right (ket x1)*) (sandwich_tc (apply_qregister Q1 E) \<rho>)\<close>
          by -
      qed
      also have \<open>\<dots> = sandwich_tc (tensor_ell2_right (ket x1)*) (\<Sum>\<^sub>\<infinity>(E,x)\<in>EEx. sandwich_tc (apply_qregister Q1 E) \<rho>)\<close>
        apply (subst infsum_bounded_linear[where h=\<open>sandwich_tc _\<close>, symmetric])
        using sum by (simp_all add: bounded_clinear.bounded_linear bounded_clinear_sandwich_tc case_prod_unfold) 
      also have \<open>\<dots> = ?rhs\<close>
        apply (subst infsum_reindex)
         apply (simp add: inj2)
        by (simp add: o_def case_prod_unfold)
      finally show \<open>?lhs = ?rhs\<close>
        by -
    qed
    then show ?thesis
      by (simp add: kf_apply.rep_eq kf_apply_qregister.rep_eq case_prod_unfold
          flip: EEx_def)
  qed
  also have \<open>\<dots> = kf_partial_trace_right *\<^sub>k\<^sub>r @{x1} (kf_apply_qregister Q1 \<EE>x *\<^sub>k\<^sub>r \<rho>)\<close>
    by (simp add: kf_partial_trace_right_apply_singleton)
  also have \<open>\<dots> = kf_partial_trace_right *\<^sub>k\<^sub>r @{x1} (kf_apply_qregister Q1 \<EE> *\<^sub>k\<^sub>r @{x2} \<rho>)\<close>
    by (simp add: kf_filter_kf_apply_qregister kf_apply_on_def \<EE>x_def)
  also have \<open>\<dots> = kf_comp (kf_partial_trace_right) (kf_apply_qregister Q1 \<EE>) *\<^sub>k\<^sub>r @{(x2,x1)} \<rho>\<close>
    by (simp add: kf_comp_apply_on_singleton)
  also have \<open>\<dots> = kf_map prod.swap (kf_comp (kf_partial_trace_right) (kf_apply_qregister Q1 \<EE>)) *\<^sub>k\<^sub>r @{x} \<rho>\<close>
    by (simp add: kf_apply_on_map swap_x)
  finally show \<open>kf_comp (kf_apply_qregister Q \<EE>) kf_partial_trace_right *\<^sub>k\<^sub>r @{x} \<rho> = kf_map prod.swap (kf_comp kf_partial_trace_right (kf_apply_qregister Q1 \<EE>)) *\<^sub>k\<^sub>r @{x} \<rho>\<close>
    by -
qed

lemma km_apply_qregister_partial_trace:
  shows \<open>km_apply_qregister Q \<EE> (partial_trace \<rho>) = partial_trace (km_apply_qregister (qregister_chain qFst Q) \<EE> \<rho>)\<close>
proof -
  wlog km: \<open>kraus_map \<EE>\<close>
    using negation
    by (simp add: km_apply_qregister_invalid_\<EE>)
  wlog \<open>qregister Q\<close> keeping km
    using negation 
    by (simp add: km_apply_qregister_def kf_apply_qregister_non_qregister non_qregister)
  from km obtain \<FF> :: \<open>(_,_,unit) kraus_family\<close> where \<EE>_def: \<open>\<EE> = kf_apply \<FF>\<close>
    using kraus_map_def_raw by blast
  from kf_apply_qregister_partial_trace[of Q \<FF>, THEN kf_eq_imp_eq_weak, THEN kf_apply_eqI, of \<rho>]
  show ?thesis
    by (simp add: \<EE>_def km_apply_qregister_kf_apply \<open>qregister Q\<close> partial_trace_is_kf_partial_trace kf_comp_apply)
qed




unbundle no kraus_map_syntax

end