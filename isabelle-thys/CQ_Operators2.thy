theory CQ_Operators2
  imports Kraus_Maps
begin

definition \<open>measure_first =
  kraus_family_map_outcome (\<lambda>(out,_). inv ket out) (kraus_family_tensor (complete_measurement (range ket)) kraus_family_id)\<close>

lemma measure_first_idem[simp]: \<open>kraus_family_map measure_first (kraus_family_map measure_first \<rho>) = kraus_family_map measure_first \<rho>\<close>
  apply (rule fun_cong[where x=\<rho>])
  apply (rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
  by (auto intro!: bounded_linear_intros
      simp: measure_first_def kraus_family_map_tensor complete_measurement_idem)

definition \<open>is_cq_operator \<rho> \<longleftrightarrow> \<rho> = kraus_family_map measure_first \<rho>\<close>

lemma is_cq_operator_0[simp]: \<open>is_cq_operator 0\<close>
  by (simp add: is_cq_operator_def)

typedef ('c,'q) cq_operator = \<open>Collect (is_cq_operator :: (('c\<times>'q) ell2, ('c\<times>'q) ell2) trace_class \<Rightarrow> bool)\<close>
  by (auto intro!: exI[of _ 0])
setup_lifting type_definition_cq_operator

definition \<open>kraus_family_is_cq E \<longleftrightarrow> kraus_equivalent (kraus_family_comp measure_first (kraus_family_comp E measure_first)) E\<close>

lemma kraus_family_is_cq_0[simp]: \<open>kraus_family_is_cq 0\<close>
  by (auto intro!: ext simp: kraus_family_is_cq_def kraus_equivalent_def kraus_family_comp_apply)

typedef ('c1,'q1,'c2,'q2) cq_kraus_family = \<open>Collect (kraus_family_is_cq :: (('c1 \<times> 'q1) ell2, ('c2 \<times> 'q2) ell2, unit) kraus_family \<Rightarrow> bool)\<close>
  by (auto intro!: exI[of _ 0])
setup_lifting type_definition_cq_kraus_family

lemma kraus_family_is_cq_flatten[simp]: \<open>kraus_family_is_cq (kraus_family_flatten \<EE>) = kraus_family_is_cq \<EE>\<close>
  by (simp add: kraus_family_is_cq_def kraus_equivalent_def kraus_family_comp_apply)

lift_definition cq_kraus_family_id :: \<open>('c,'q,'c,'q) cq_kraus_family\<close>
  is \<open>kraus_family_flatten measure_first\<close>
  by (auto intro!: ext simp: kraus_family_is_cq_def kraus_equivalent_def kraus_family_comp_apply)

lemma kraus_family_is_cq_comp:
  assumes \<open>kraus_family_is_cq \<EE>\<close>
  assumes \<open>kraus_family_is_cq \<FF>\<close>
  shows \<open>kraus_family_is_cq (kraus_family_comp \<EE> \<FF>)\<close>
proof (unfold kraus_family_is_cq_def kraus_equivalent_def, rule ext)
  fix \<rho>
  let ?fst = \<open>kraus_family_map measure_first\<close>
    and ?\<EE> = \<open>kraus_family_map \<EE>\<close>
    and ?\<FF> = \<open>kraus_family_map \<FF>\<close>
  from assms have fst\<EE>fst: \<open>?fst (?\<EE> (?fst \<tau>)) = ?\<EE> \<tau>\<close> for \<tau>
    apply (simp add: kraus_family_is_cq_def kraus_equivalent_def kraus_family_comp_apply o_def)
    by metis
  from assms have fst\<FF>fst: \<open>?fst (?\<FF> (?fst \<tau>)) = ?\<FF> \<tau>\<close> for \<tau>
    apply (simp add: kraus_family_is_cq_def kraus_equivalent_def kraus_family_comp_apply o_def)
    by metis
  have \<open>kraus_family_map (kraus_family_comp measure_first (kraus_family_comp (kraus_family_comp \<EE> \<FF>) measure_first)) \<rho>
     = ?fst (?\<EE> (?\<FF> (?fst \<rho>)))\<close> (is \<open>?lhs = _\<close>)
    by (simp add: kraus_family_comp_apply)
  also have \<open>\<dots> = ?fst (?fst (?\<EE> (?fst (?\<FF> (?fst \<rho>)))))\<close>
    by (simp only: fst\<EE>fst)
  also have \<open>\<dots> = ?fst (?\<EE> (?fst (?\<FF> (?fst \<rho>))))\<close>
    by simp
  also have \<open>\<dots> = ?\<EE> (?\<FF> (?fst \<rho>))\<close>
    by (simp only: fst\<EE>fst)
  also have \<open>\<dots> = ?\<EE> (?fst (?\<FF> (?fst (?fst \<rho>))))\<close>
    by (simp only: fst\<FF>fst)
  also have \<open>\<dots> = ?\<EE> (?fst (?\<FF> (?fst \<rho>)))\<close>
    by simp
  also have \<open>\<dots> = ?\<EE> (?\<FF> \<rho>)\<close>
    by (simp only: fst\<FF>fst)
  also have \<open>\<dots> = kraus_family_map (kraus_family_comp \<EE> \<FF>) \<rho>\<close> (is \<open>_ = ?rhs\<close>)
    by (simp add: kraus_family_comp_apply)
  finally show \<open>?lhs = ?rhs\<close>
    by -
qed

lift_definition cq_kraus_family_comp :: \<open>('c2,'q2,'c3,'q3) cq_kraus_family \<Rightarrow> ('c1,'q1,'c2,'q2) cq_kraus_family \<Rightarrow> ('c1,'q1,'c3,'q3) cq_kraus_family\<close> is
  \<open>\<lambda>E F. kraus_family_flatten (kraus_family_comp E F)\<close>
  by (auto intro!: kraus_family_is_cq_comp)

lemma cauchy_summable_on:
  fixes f :: \<open>'a \<Rightarrow> 'b::{complete_space,comm_monoid_add}\<close>
  assumes \<open>\<And>e. e > 0 \<Longrightarrow> \<exists>F. finite F \<and> (\<forall>G H. finite G \<longrightarrow> finite H \<longrightarrow> G \<supseteq> F \<longrightarrow> H \<supseteq> F \<longrightarrow> dist (sum f G) (sum f H) \<le> e)\<close>
  shows \<open>f summable_on UNIV\<close>
proof -
  have \<open>\<exists>P. eventually P (filtermap (sum f) (finite_subsets_at_top UNIV)) \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)\<close>
    if \<open>0 < e\<close> for e
  proof -
    define d where \<open>d = e/2\<close>
    with that have \<open>d > 0\<close>
      by fastforce
    with assms[of d] obtain F where \<open>finite F\<close> and less_d: \<open>\<And>G H. finite G \<Longrightarrow> finite H \<Longrightarrow> G \<supseteq> F \<Longrightarrow> H \<supseteq> F \<Longrightarrow> dist (sum f G) (sum f H) \<le> d\<close>
      by blast
    define P where \<open>P s \<longleftrightarrow> (\<exists>G. finite G \<and> G \<supseteq> F \<and> s = sum f G)\<close> for s
    have \<open>\<forall>\<^sub>F x in finite_subsets_at_top UNIV. P (\<Sum>x\<in>x. f x)\<close>
      using \<open>finite F\<close> by (auto simp: eventually_finite_subsets_at_top P_def)
    then have \<open>eventually P (filtermap (sum f) (finite_subsets_at_top UNIV))\<close>
      by (simp add: eventually_filtermap)
    moreover have \<open>dist x y < e\<close> if \<open>P x\<close> and \<open>P y\<close> for x y
    proof -
      from that obtain G H where \<open>finite G\<close> \<open>finite H\<close> \<open>G \<supseteq> F\<close> \<open>H \<supseteq> F\<close> and \<open>x = sum f G\<close> and \<open>y = sum f H\<close>
        by (auto simp: P_def)
      with less_d have \<open>dist x y \<le> d\<close>
        by algebra
      with d_def \<open>e > 0\<close> show ?thesis
        by auto
    qed
    ultimately show ?thesis
      by blast
  qed
  then have \<open>cauchy_filter (filtermap (sum f) (finite_subsets_at_top UNIV))\<close>
    by (auto intro!: cauchy_filter_metricI)
  then have \<open>convergent_filter (filtermap (sum f) (finite_subsets_at_top UNIV))\<close>
    using cauchy_filter_convergent by blast
  then show ?thesis
    by (simp add: summable_on_def has_sum_def filterlim_def convergent_filter_iff)  
qed

(* 
lemma cauchy_abs_summable_on:
  fixes f :: \<open>'a \<Rightarrow> 'b::{complete_space,real_normed_vector}\<close>
  assumes \<open>\<And>e. e > 0 \<Longrightarrow> \<exists>F. finite F \<and> (\<forall>G. finite G \<longrightarrow> G \<supseteq> F \<longrightarrow> (\<Sum>x\<in>G. norm (f x)) \<le> e)\<close>
  shows \<open>f abs_summable_on UNIV\<close>
proof (rule cauchy_summable_on)
  fix e :: real assume \<open>e > 0\<close>
  with assms obtain F where \<open>finite F\<close> and \<open>\<And>G. finite G \<Longrightarrow> G \<supseteq> F \<Longrightarrow> (\<Sum>x\<in>G. norm (f x)) \<le> e\<close>
    by meson
  have \<open>dist (\<Sum>x\<in>G. norm (f x)) (\<Sum>x\<in>H. norm (f x)) < e\<close> if \<open>finite G\<close> \<open>finite H\<close> \<open>G \<supseteq> F\<close> \<open>H \<supseteq> F\<close> for G H
  proof -
    have \<open>dist (\<Sum>x\<in>G. norm (f x)) (\<Sum>x\<in>H. norm (f x)) =\<close>
 *)

(* TODO move *)
lemma tc_butterfly_scaleC_summable:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>f abs_summable_on A\<close>
  shows \<open>(\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) summable_on A\<close>
proof -
  define M where \<open>M = (\<Sum>\<^sub>\<infinity>x\<in>A. norm (f x))\<close>
  have \<open>(\<Sum>x\<in>F. cmod (f x) * norm (tc_butterfly (ket x) (ket x))) \<le> M\<close> if \<open>finite F\<close> and \<open>F \<subseteq> A\<close> for F
  proof -
    have \<open>(\<Sum>x\<in>F. norm (f x) * norm (tc_butterfly (ket x) (ket x))) = (\<Sum>x\<in>F. norm (f x))\<close>
      by (simp add: norm_tc_butterfly)
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. norm (f x))\<close>
      using assms finite_sum_le_infsum norm_ge_zero that(1) that(2) by blast
    also have \<open>\<dots> = M\<close>
      by (simp add: M_def)
    finally show ?thesis
      by -
  qed
  then have \<open>(\<lambda>x. norm (f x *\<^sub>C tc_butterfly (ket x) (ket x))) abs_summable_on A\<close>
    apply (intro nonneg_bdd_above_summable_on bdd_aboveI)
    by auto
  then show ?thesis
    by (auto intro: abs_summable_summable)
qed

lift_definition tc_apply :: \<open>('a::chilbert_space,'b::chilbert_space) trace_class \<Rightarrow> 'a \<Rightarrow> 'b\<close> is cblinfun_apply.

lemma bounded_cbilinear_tc_apply: \<open>bounded_cbilinear tc_apply\<close>
  apply (rule bounded_cbilinear.intro; transfer)
      apply (auto intro!: simp: )
  apply (auto intro!: exI[of _ 1] cblinfun.add_left cblinfun.add_right cblinfun.scaleC_right)
  by (smt (verit, del_insts) Unsorted_HSTP.norm_leq_trace_norm mult_hom.hom_zero mult_less_cancel_right norm_cblinfun norm_not_less_zero not_square_less_zero ordered_field_class.sign_simps(5) ordered_field_class.sign_simps(50) rel_simps(70) vector_space_over_itself.scale_eq_0_iff vector_space_over_itself.scale_left_commute vector_space_over_itself.vector_space_assms(3))

(* TODO move *)
lemma tc_butterfly_scaleC_has_sum:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>f abs_summable_on UNIV\<close>
  shows \<open>((\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) has_sum diagonal_operator_tc f) UNIV\<close>
proof -
  define D where \<open>D = (\<Sum>\<^sub>\<infinity>x. f x *\<^sub>C tc_butterfly (ket x) (ket x))\<close>
  have bdd_f: \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
    by (metis assms summable_on_bdd_above_real)

  have \<open>ket y \<bullet>\<^sub>C from_trace_class D (ket z) = ket y \<bullet>\<^sub>C from_trace_class (diagonal_operator_tc f) (ket z)\<close> for y z
  proof -
    have blin_tc_apply: \<open>bounded_linear (\<lambda>a. tc_apply a (ket z))\<close>
      by (intro bounded_clinear.bounded_linear bounded_cbilinear.bounded_clinear_left bounded_cbilinear_tc_apply)
    have summ: \<open>(\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) summable_on UNIV\<close>
      by (intro tc_butterfly_scaleC_summable assms)

    have \<open>((\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) has_sum D) UNIV\<close>
      by (simp add: D_def summ)
    with blin_tc_apply have \<open>((\<lambda>x. tc_apply (f x *\<^sub>C tc_butterfly (ket x) (ket x)) (ket z)) has_sum tc_apply D (ket z)) UNIV\<close>
      by (rule Infinite_Sum.has_sum_bounded_linear)
    then have \<open>((\<lambda>x. ket y \<bullet>\<^sub>C tc_apply (f x *\<^sub>C tc_butterfly (ket x) (ket x)) (ket z)) has_sum ket y \<bullet>\<^sub>C tc_apply D (ket z)) UNIV\<close>
      by (smt (verit, best) has_sum_cong has_sum_imp_summable has_sum_infsum infsumI infsum_cinner_left summable_on_cinner_left)
    then have \<open>((\<lambda>x. of_bool (x=y) * of_bool (y=z) * f y) has_sum ket y \<bullet>\<^sub>C tc_apply D (ket z)) UNIV\<close>
      apply (rule has_sum_cong[THEN iffD2, rotated])
      by (auto intro!: simp: tc_apply.rep_eq scaleC_trace_class.rep_eq tc_butterfly.rep_eq)
    then have \<open>((\<lambda>x. of_bool (y=z) * f y) has_sum ket y \<bullet>\<^sub>C tc_apply D (ket z)) {y}\<close>
      apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
      by auto
    then have \<open>ket y \<bullet>\<^sub>C tc_apply D (ket z) = of_bool (y=z) * f y\<close>
      by simp
    also have \<open>\<dots> = ket y \<bullet>\<^sub>C from_trace_class (diagonal_operator_tc f) (ket z)\<close>
      by (simp add: diagonal_operator_tc.rep_eq assms diagonal_operator_ket bdd_f)
    finally show ?thesis
      by (simp add: tc_apply.rep_eq)
  qed
  then have \<open>from_trace_class D = from_trace_class (diagonal_operator_tc f)\<close>
    by (auto intro!: equal_ket cinner_ket_eqI)
  then have \<open>D = diagonal_operator_tc f\<close>
    by (simp add: from_trace_class_inject)
  with tc_butterfly_scaleC_summable[OF assms]
  show ?thesis
    using D_def by force
qed

lift_definition cq_diagonal_operator :: \<open>('c \<Rightarrow> complex) \<Rightarrow> ('q ell2, 'q ell2) trace_class \<Rightarrow> ('c,'q) cq_operator\<close> is
  \<open>\<lambda>f \<rho>\<^sub>q. tc_tensor (diagonal_operator_tc f) \<rho>\<^sub>q\<close>
  by (auto intro!: simp: is_cq_operator_def measure_first_def kraus_family_map_tensor)
(* proof -
  fix f :: \<open>'c \<Rightarrow> complex\<close> and \<rho>\<^sub>q :: \<open>('q ell2, 'q ell2) trace_class\<close>
  show \<open>tc_tensor (diagonal_operator_tc f) \<rho>\<^sub>q \<in> Collect is_cq_operator\<close>
    apply (auto intro!: simp: is_cq_operator_def measure_first_def kraus_family_map_tensor ) *)

lift_definition cq_kraus_map_cases :: \<open>('c1 \<Rightarrow> ('c1,'q1,'c2,'q2) cq_kraus_family) \<Rightarrow> ('c1,'q1,'c2,'q2) cq_kraus_family\<close> is
  \<open>\<lambda>\<EE> :: 'c1 \<Rightarrow> (('c1\<times>'q1) ell2, ('c2\<times>'q2) ell2, unit) kraus_family. 
    kraus_family_flatten (kraus_family_comp_dependent \<EE> measure_first)\<close>
proof (rule CollectI)
  fix \<EE> :: \<open>'c1 \<Rightarrow> (('c1\<times>'q1) ell2, ('c2\<times>'q2) ell2, unit) kraus_family\<close>
  assume \<open>\<EE> x \<in> Collect kraus_family_is_cq\<close> for x
  write kraus_equivalent (infix "~~" 80)
  write kraus_family_comp (infixl "oo" 85)
  have \<open>measure_first oo (kraus_family_flatten (kraus_family_comp_dependent \<EE> measure_first) oo measure_first)
      ~~ measure_first oo (kraus_family_comp_dependent \<EE> measure_first oo measure_first)\<close>
    by (intro kraus_family_comp_cong kraus_equivalent_reflI kraus_equivalent_kraus_family_map_outcome_left)
  also have \<open>\<dots> ~~ measure_first oo kraus_family_comp_dependent \<EE> measure_first oo measure_first\<close>
try0
sledgehammer [dont_slice]
by -


apply (simp add: )
  show \<open>kraus_family_is_cq (kraus_family_flatten (kraus_family_comp_dependent \<EE> measure_first))\<close>
    unfolding kraus_family_is_cq_def
apply (auto intro!: simp: )

end