theory Programs
  imports QRHL_Core Expressions Wlog.Wlog
begin

(* TODO move *)
lemma norm_cblinfun_mono:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>norm A \<le> norm B\<close>
proof -
  have \<open>B \<ge> 0\<close>
    using assms by force
  have sqrtA: \<open>(sqrt_op A)* o\<^sub>C\<^sub>L sqrt_op A = A\<close>
    by (simp add: \<open>A \<ge> 0\<close> flip: positive_hermitianI)
  have sqrtB: \<open>(sqrt_op B)* o\<^sub>C\<^sub>L sqrt_op B = B\<close>
    by (simp add: \<open>B \<ge> 0\<close> flip: positive_hermitianI)
  have \<open>norm (sqrt_op A \<psi>) \<le> norm (sqrt_op B \<psi>)\<close> for \<psi>
    apply (auto intro!: cnorm_le[THEN iffD2]
        simp: sqrtA sqrtB
        simp flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
    using assms less_eq_cblinfun_def by auto
  then have \<open>norm (sqrt_op A) \<le> norm (sqrt_op B)\<close>
    by (meson dual_order.trans norm_cblinfun norm_cblinfun_bound norm_ge_zero)
  moreover have \<open>norm A = (norm (sqrt_op A))\<^sup>2\<close>
    by (metis norm_AadjA sqrtA)
  moreover have \<open>norm B = (norm (sqrt_op B))\<^sup>2\<close>
    by (metis norm_AadjA sqrtB)
  ultimately show \<open>norm A \<le> norm B\<close>
    by force
qed

lemma sandwich_mono: \<open>sandwich A B \<le> sandwich A C\<close> if \<open>B \<le> C\<close>
  by (metis cblinfun.real.diff_right diff_ge_0_iff_ge sandwich_pos that)

lemma abs_op_id_on_pos: \<open>a \<ge> 0 \<Longrightarrow> abs_op a = a\<close>
  using abs_opI by force

lemma cmod_mono: \<open>0 \<le> a \<Longrightarrow> a \<le> b \<Longrightarrow> cmod a \<le> cmod b\<close>
  by (simp add: cmod_Re less_eq_complex_def)

lemma trace_norm_bounded:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close> and \<open>trace_class B\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>trace_class A\<close>
proof -
  have \<open>(\<lambda>x. x \<bullet>\<^sub>C (B *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
    by (metis assms(2) is_onb_some_chilbert_basis summable_on_iff_abs_summable_on_complex trace_exists)
  then have \<open>(\<lambda>x. x \<bullet>\<^sub>C (A *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
    apply (rule abs_summable_on_comparison_test)
    using \<open>A \<ge> 0\<close> \<open>A \<le> B\<close>
    by (auto intro!: cmod_mono cinner_pos_if_pos simp: abs_op_id_on_pos less_eq_cblinfun_def)
  then show ?thesis
    by (auto intro!: trace_classI[OF is_onb_some_chilbert_basis] simp: abs_op_id_on_pos \<open>A \<ge> 0\<close>)
qed

lemma trace_norm_cblinfun_mono:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close> and \<open>trace_class B\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>trace_norm A \<le> trace_norm B\<close>
proof -
  from assms have \<open>trace_class A\<close>
    by (rule trace_norm_bounded)
  from \<open>A \<le> B\<close> and \<open>A \<ge> 0\<close>
  have \<open>B \<ge> 0\<close>
    by simp
  have \<open>cmod (x \<bullet>\<^sub>C (abs_op A *\<^sub>V x)) \<le> cmod (x \<bullet>\<^sub>C (abs_op B *\<^sub>V x))\<close> for x
    using \<open>A \<le> B\<close>
    unfolding less_eq_cblinfun_def
    using \<open>A \<ge> 0\<close> \<open>B \<ge> 0\<close> 
    by (auto intro!: cmod_mono cinner_pos_if_pos simp: abs_op_id_on_pos)
  then show \<open>trace_norm A \<le> trace_norm B\<close>
    using \<open>trace_class A\<close> \<open>trace_class B\<close>
    by (auto intro!: infsum_mono 
        simp add: trace_norm_def trace_class_iff_summable[OF is_onb_some_chilbert_basis])
qed

(* TODO move *)
instantiation trace_class :: (chilbert_space, chilbert_space) order begin
lift_definition less_eq_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> bool\<close> is
  less_eq.
lift_definition less_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> bool\<close> is
  less.
instance
  apply intro_classes
     apply (auto simp add: less_eq_trace_class.rep_eq less_trace_class.rep_eq)
  by (simp add: from_trace_class_inject)
end


lemma norm_cblinfun_mono_trace_class:
  fixes A B :: \<open>('a::chilbert_space, 'a) trace_class\<close>
  assumes \<open>A \<ge> 0\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>norm A \<le> norm B\<close>
  using assms
  apply transfer
  apply (rule trace_norm_cblinfun_mono)
  by auto

type_synonym ('a,'b) kraus_family = \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> nat\<close>

definition \<open>kraus_family \<EE> \<longleftrightarrow> (\<exists>B. \<forall>F. finite F \<longrightarrow> norm (\<Sum>E\<in>F. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> B)\<close>
  for \<EE> :: \<open>(_::chilbert_space, _::chilbert_space) kraus_family\<close>
definition \<open>kraus_family_norm \<EE> = (SUP F\<in>Collect finite. norm (\<Sum>E\<in>F. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)))\<close>

definition \<open>kraus_family_map \<EE> \<rho> = (\<Sum>\<^sub>\<infinity>E. of_nat (\<EE> E) *\<^sub>C Abs_trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E*))\<close>

definition \<open>kraus_equivalent \<EE> \<FF> \<longleftrightarrow> kraus_family \<EE> \<and> kraus_family \<FF> \<and> kraus_family_map \<EE> = kraus_family_map \<FF>\<close>

lemma kraus_family_zero[simp]: \<open>kraus_family (\<lambda>_. 0)\<close>
  by (auto simp: kraus_family_def)

quotient_type (overloaded) ('a,'b) kraus_map = \<open>('a::chilbert_space, 'b::chilbert_space) kraus_family\<close> / partial: kraus_equivalent
  by (auto intro!: part_equivpI exI[of _ \<open>\<lambda>_. 0\<close>] sympI transpI simp: kraus_equivalent_def)

definition \<open>kraus_family_comp \<EE> \<FF> G = (if G=0 then 0 else \<Sum>(E,F)|(\<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F = G). \<EE> E * \<FF> F)\<close> 
\<comment> \<open>The lemma \<open>kraus_family_comp_finite\<close> below shows that we range over a finite set in the sum.\<close>
  for \<EE> \<FF> :: \<open>(_::chilbert_space, _::chilbert_space) kraus_family\<close>

definition kraus_family_of_op :: \<open>_ \<Rightarrow> (_::chilbert_space,_::chilbert_space) kraus_family\<close> where
  \<open>kraus_family_of_op E F = of_bool (E=F)\<close>

lemma kraus_family_kraus_family_of_op[simp]: \<open>kraus_family (kraus_family_of_op E)\<close>
proof -
  have \<open>(\<Sum>F\<in>M. kraus_family_of_op E F *\<^sub>C (F* o\<^sub>C\<^sub>L F)) = (if E\<in>M then E* o\<^sub>C\<^sub>L E else 0)\<close> if \<open>finite M\<close> for M
    apply (subst sum_single[where i=E])
    using that by (auto simp: kraus_family_of_op_def)
  then show ?thesis
    by (auto simp add: kraus_family_def)
qed

lemma kraus_family_of_op_norm[simp]:
  \<open>kraus_family_norm (kraus_family_of_op E) = (norm E)\<^sup>2\<close>
proof -
  have \<open>kraus_family_norm (kraus_family_of_op E) = 
      (\<Squnion>M\<in>Collect finite. norm (\<Sum>F\<in>M. of_bool (E=F) *\<^sub>C (F* o\<^sub>C\<^sub>L F)))\<close>
    by (simp add: kraus_family_norm_def kraus_family_of_op_def)
  also have \<open>\<dots> = (\<Squnion>M\<in>Collect finite. if E\<in>M then norm (E* o\<^sub>C\<^sub>L E) else 0)\<close>
  proof (rule SUP_cong, simp)
    fix M :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close> assume \<open>M \<in> Collect finite\<close>
    then have [simp]: \<open>finite M\<close> by simp
    show \<open>norm (\<Sum>F\<in>M. of_bool (E = F) *\<^sub>C (F* o\<^sub>C\<^sub>L F)) = (if E \<in> M then norm (E* o\<^sub>C\<^sub>L E) else 0)\<close>
      apply (subst sum_single[where i=E])
      by auto
  qed
  also have \<open>\<dots> = norm (E* o\<^sub>C\<^sub>L E)\<close>
    apply (rule cSup_eq_maximum)
    by auto
  also have \<open>\<dots> = (norm E)\<^sup>2\<close>
    by simp
  finally show ?thesis
    by -
qed

lift_definition kraus_map_of_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> ('a,'b) kraus_map\<close>
  is kraus_family_of_op
  by (simp add: kraus_equivalent_def)

lemma kraus_family_map_bounded:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>norm (kraus_family_map \<EE> \<rho>) \<le> kraus_family_norm \<EE> * norm \<rho>\<close>
  sorry

lemma kraus_family_norm_geq0:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_norm \<EE> \<ge> 0\<close>
  unfolding kraus_family_norm_def
  apply (rule cSUP_upper2[where x=\<open>{}\<close>])
  using assms
  by (simp_all add: bdd_above_def kraus_family_def)

(* Strengthening of Nat.of_nat_0_le_iff: wider type. *)
lemma of_nat_0_le_iff: \<open>of_nat x \<ge> (0::_::{ordered_ab_semigroup_add,zero_less_one})\<close>
  apply (induction x)
   apply auto
  by (metis add_mono semiring_norm(50) zero_less_one_class.zero_le_one)

lemma trace_class_sandwich: \<open>trace_class b \<Longrightarrow> trace_class (sandwich a b)\<close>
  by (simp add: sandwich_apply trace_class_comp_right trace_class_comp_left)

lemma trace_norm_butterfly: \<open>trace_norm (butterfly a a) = (norm a)^2\<close>
  sorry

lemma from_trace_class_sum:
  shows \<open>from_trace_class (\<Sum>x\<in>M. f x) = (\<Sum>x\<in>M. from_trace_class (f x))\<close>
  apply (induction M rule:infinite_finite_induct)
  by (simp_all add: plus_trace_class.rep_eq)

lemma not_not_singleton_zero: 
  \<open>x = 0\<close> if \<open>\<not> class.not_singleton TYPE('a)\<close> for x :: \<open>'a::zero\<close>
  using that unfolding class.not_singleton_def by auto

lemma not_not_singleton_cblinfun_zero: 
  \<open>x = 0\<close> if \<open>\<not> class.not_singleton TYPE('a)\<close> for x :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  apply (rule cblinfun_eqI)
  apply (subst not_not_singleton_zero[OF that])
  by simp

(* lemma not_not_singleton_cblinfun_zero_simp:
  \<open>x = 0\<close> if \<open>NO_MATCH 0 x\<close> \<open>\<not> class.not_singleton TYPE('a)\<close> for x :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  using that not_not_singleton_cblinfun_zero by simp *)

lemma cblinfun_norm_approx_witness':
  fixes A :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. norm (A *\<^sub>V \<psi>) / norm \<psi> \<ge> norm A - \<epsilon>\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  obtain \<psi> where \<open>norm (A *\<^sub>V \<psi>) \<ge> norm A - \<epsilon>\<close> and \<open>norm \<psi> = 1\<close>
    apply atomize_elim
    using complex_normed_vector_axioms True assms
    by (rule cblinfun_norm_approx_witness[internalize_sort' 'a])
  then have \<open>norm (A *\<^sub>V \<psi>) / norm \<psi> \<ge> norm A - \<epsilon>\<close>
    by simp
  then show ?thesis 
    by auto
next
  case False
  show ?thesis
    apply (subst not_not_singleton_cblinfun_zero[OF False])
     apply simp
    apply (subst not_not_singleton_cblinfun_zero[OF False])
    using \<open>\<epsilon> > 0\<close> by simp
qed

lemma any_norm_exists:
  assumes \<open>n \<ge> 0\<close>
  shows \<open>\<exists>\<psi>::'a::{real_normed_vector,not_singleton}. norm \<psi> = n\<close>
proof -
  obtain \<psi> :: 'a where \<open>\<psi> \<noteq> 0\<close>
    using not_singleton_card
    by force
  then have \<open>norm (n *\<^sub>R sgn \<psi>) = n\<close>
    using assms by (auto simp: sgn_div_norm abs_mult)
  then show ?thesis
    by blast
qed

lemma cblinfun_norm_approx_witness_cinner:
  fixes A :: \<open>'a::{not_singleton,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close> and \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>) \<ge> norm A - \<epsilon> \<and> norm \<psi> = 1\<close>
proof (cases \<open>A = 0\<close>)
  case False
  define B where \<open>B = sqrt_op A\<close>
  define \<delta> where \<open>\<delta> = min (\<epsilon> / (2 * norm B)) (norm B)\<close>
  then have \<open>\<delta> > 0\<close>
    by (smt (verit, ccfv_threshold) B_def False Positive_Operators.sqrt_op_square assms(1) assms(2) linordered_field_class.divide_pos_pos norm_AAadj norm_eq_zero positive_hermitianI power_zero_numeral sqrt_op_pos zero_less_norm_iff)
  have \<delta>: \<open>2 * (\<delta> * norm B) - \<delta> * \<delta> \<le> \<epsilon>\<close>
  proof -
    have \<open>\<delta> \<le> \<epsilon> / (2 * norm B)\<close>
      by (simp add: \<delta>_def)
  then show ?thesis
    using assms(2) \<open>0 < \<delta>\<close>
    by (smt (verit, best) Extra_Ordered_Fields.sign_simps(19) add_diff_cancel_left' diff_diff_eq2 less_eq_real_def linorder_not_less mult_le_cancel_left_pos nice_ordered_field_class.pos_le_divide_eq)
  qed
  from cblinfun_norm_approx_witness[OF \<open>\<delta> > 0\<close>]
  obtain \<psi> where bound: \<open>norm B - \<delta> \<le> norm (B *\<^sub>V \<psi>)\<close> and \<open>norm \<psi> = 1\<close>
    by auto
  have \<open>complex_of_real (norm A - \<epsilon>) = (norm B)\<^sup>2 - \<epsilon>\<close>
    by (metis B_def Positive_Operators.sqrt_op_square assms(1) norm_AAadj positive_hermitianI sqrt_op_pos)
  also have \<open>\<dots> \<le> (norm B - \<delta>)^2\<close>
    apply (rule complex_of_real_mono)
    using \<delta> by (simp add: power2_eq_square left_diff_distrib right_diff_distrib)
  also have \<open>\<dots> \<le> (norm (B *\<^sub>V \<psi>))^2\<close>
    apply (rule complex_of_real_mono)
    apply (rule power_mono)
    apply (rule bound)
    by (auto simp: \<delta>_def)
  also have \<open>\<dots> = B \<psi> \<bullet>\<^sub>C B \<psi>\<close>
    by (simp add: cdot_square_norm)
  also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C A \<psi>\<close>
    by (metis B_def Positive_Operators.sqrt_op_square assms(1) cblinfun_apply_cblinfun_compose cinner_adj_right positive_hermitianI sqrt_op_pos)
  finally show ?thesis
    using \<open>norm \<psi> = 1\<close> by auto
next
  case True
  with \<open>\<epsilon> > 0\<close> show ?thesis
    by (auto intro!: any_norm_exists)
qed

lemma cblinfun_norm_approx_witness_cinner':
  fixes A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close> and \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>) / (norm \<psi>)^2 \<ge> norm A - \<epsilon>\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  obtain \<psi> where \<open>\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>) \<ge> norm A - \<epsilon>\<close> and \<open>norm \<psi> = 1\<close>
    apply atomize_elim
    using chilbert_space_axioms True assms
    by (rule cblinfun_norm_approx_witness_cinner[internalize_sort' 'a])
  then have \<open>\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>) / (norm \<psi>)^2 \<ge> norm A - \<epsilon>\<close>
    by simp
  then show ?thesis 
    by auto
next
  case False
  show ?thesis
    apply (subst not_not_singleton_cblinfun_zero[OF False])
     apply simp
    apply (subst not_not_singleton_cblinfun_zero[OF False])
    using \<open>\<epsilon> > 0\<close> by simp
qed

lemma bdd_above_mono2:
  assumes \<open>bdd_above (g ` B)\<close>
  assumes \<open>A \<subseteq> B\<close>
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows \<open>bdd_above (f ` A)\<close>
  by (smt (verit, del_insts) Set.basic_monos(7) assms(1) assms(2) assms(3) basic_trans_rules(23) bdd_above.I2 bdd_above.unfold imageI)

lemma has_sum_mono_neutral_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  have \<open>((\<lambda>x. Re (f x)) has_sum Re a) A\<close>
    using assms(1) has_sum_Re has_sum_cong by blast
  moreover have \<open>((\<lambda>x. Re (g x)) has_sum Re b) B\<close>
    using assms(2) has_sum_Re has_sum_cong by blast
  ultimately have Re: \<open>Re a \<le> Re b\<close>
    apply (rule has_sum_mono_neutral)
    using assms(3-5) by (simp_all add: less_eq_complex_def)
  have \<open>((\<lambda>x. Im (f x)) has_sum Im a) A\<close>
    using assms(1) has_sum_Im has_sum_cong by blast
  then have \<open>((\<lambda>x. Im (f x)) has_sum Im a) (A \<inter> B)\<close>
    apply (rule has_sum_cong_neutral[THEN iffD1, rotated -1])
    using assms(3-5) by (auto simp add: less_eq_complex_def)
  moreover have \<open>((\<lambda>x. Im (g x)) has_sum Im b) B\<close>
    using assms(2) has_sum_Im has_sum_cong by blast
  then have \<open>((\<lambda>x. Im (f x)) has_sum Im b) (A \<inter> B)\<close>
    apply (rule has_sum_cong_neutral[THEN iffD1, rotated -1])
    using assms(3-5) by (auto simp add: less_eq_complex_def)
  ultimately have Im: \<open>Im a = Im b\<close>
    by (rule has_sum_unique)
  from Re Im show ?thesis
    using less_eq_complexI by blast
qed

lemma has_sum_mono_neutral_wot:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes \<open>has_sum_in cweak_operator_topology f A a\<close> and "has_sum_in cweak_operator_topology g B b"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  have \<psi>_eq: \<open>\<psi> \<bullet>\<^sub>C a \<psi> \<le> \<psi> \<bullet>\<^sub>C b \<psi>\<close> for \<psi>
  proof -
    from assms(1)
    have sumA: \<open>((\<lambda>x. \<psi> \<bullet>\<^sub>C f x \<psi>) has_sum \<psi> \<bullet>\<^sub>C a \<psi>) A\<close>
      by (simp add: has_sum_in_def has_sum_def limitin_cweak_operator_topology
          cblinfun.sum_left cinner_sum_right)
    from assms(2)
    have sumB: \<open>((\<lambda>x. \<psi> \<bullet>\<^sub>C g x \<psi>) has_sum \<psi> \<bullet>\<^sub>C b \<psi>) B\<close>
      by (simp add: has_sum_in_def has_sum_def limitin_cweak_operator_topology
          cblinfun.sum_left cinner_sum_right)
    from sumA sumB
    show ?thesis
      apply (rule has_sum_mono_neutral_complex)
      using assms(3-5)
      by (auto simp: less_eq_cblinfun_def)
  qed
  then show \<open>a \<le> b\<close>
    by (simp add: less_eq_cblinfun_def)
qed

lemma sot_weaker_than_norm_limitin: \<open>limitin cstrong_operator_topology a A F\<close> if \<open>(a \<longlongrightarrow> A) F\<close>
proof -
  from that have \<open>((\<lambda>x. a x *\<^sub>V \<psi>) \<longlongrightarrow> A \<psi>) F\<close> for \<psi>
    by (auto intro!: cblinfun.tendsto)
  then show ?thesis
    by (simp add: limitin_cstrong_operator_topology)
qed

(* lemma wot_weaker_than_traceclass_limitin: \<open>limitin cweak_operator_topology (\<lambda>x. from_trace_class (a x)) (from_trace_class A) F\<close> 
  if \<open>(a \<longlongrightarrow> A) F\<close>
proof -
  from that have \<open>((\<lambda>x. a x *\<^sub>V \<psi>) \<longlongrightarrow> A \<psi>) F\<close> for \<psi>
    by (auto intro!: cblinfun.tendsto) *)


lemma has_sum_mono_neutral_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  from assms(1)
  have \<open>has_sum_in cweak_operator_topology (\<lambda>x. from_trace_class (f x)) A (from_trace_class a)\<close>
    sorry
  moreover
  from assms(2)
  have \<open>has_sum_in cweak_operator_topology (\<lambda>x. from_trace_class (g x)) B (from_trace_class b)\<close>
    sorry
  ultimately have \<open>from_trace_class a \<le> from_trace_class b\<close>
    apply (rule has_sum_mono_neutral_wot)
    using assms by (auto simp: less_eq_trace_class.rep_eq)
  then show ?thesis
    by (auto simp: less_eq_trace_class.rep_eq)
qed

lemma has_sum_mono_neutral_cblinfun:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  from assms(1)
  have \<open>has_sum_in cweak_operator_topology f A a\<close> 
    by (auto intro!: wot_weaker_than_sot_limitin sot_weaker_than_norm_limitin 
        simp: has_sum_def has_sum_in_def)
  moreover
  from assms(2) have "has_sum_in cweak_operator_topology g B b"
    by (auto intro!: wot_weaker_than_sot_limitin sot_weaker_than_norm_limitin 
        simp: has_sum_def has_sum_in_def)
  ultimately show ?thesis
    apply (rule has_sum_mono_neutral_wot)
    using assms by auto
qed



lemma has_sum_mono_cblinfun:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes "(f has_sum x) A" and "(g has_sum y) A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "x \<le> y"
  using assms has_sum_mono_neutral_cblinfun by force

lemma has_sum_mono_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "(f has_sum x) A" and "(g has_sum y) A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "x \<le> y"
  using assms has_sum_mono_neutral_traceclass by force

lemma infsum_mono_cblinfun:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes "f summable_on A" and "g summable_on A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "infsum f A \<le> infsum g A"
  by (meson assms has_sum_infsum has_sum_mono_cblinfun)

lemma infsum_mono_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "f summable_on A" and "g summable_on A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "infsum f A \<le> infsum g A"
  by (meson assms has_sum_infsum has_sum_mono_traceclass)

lemma infsum_mono_neutral_cblinfun:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes "f summable_on A" and "g summable_on B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "infsum f A \<le> infsum g B"
  by (smt (verit, del_insts) assms(1) assms(2) assms(3) assms(4) assms(5) has_sum_infsum has_sum_mono_neutral_cblinfun)

lemma infsum_mono_neutral_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "f summable_on A" and "g summable_on B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "infsum f A \<le> infsum g B"
  using assms(1) assms(2) assms(3) assms(4) assms(5) has_sum_mono_neutral_traceclass summable_iff_has_sum_infsum by blast

instance complex :: ordered_complex_vector
  apply intro_classes
  by (auto simp: less_eq_complex_def mult_left_mono mult_right_mono)

instance cblinfun :: (chilbert_space, chilbert_space) ordered_complex_vector
  by intro_classes

instance trace_class :: (chilbert_space, chilbert_space) ordered_complex_vector
  apply (intro_classes; transfer)
  by (auto intro!: scaleC_left_mono scaleC_right_mono)

lemma Abs_trace_class_geq0I: \<open>0 \<le> Abs_trace_class t\<close> if \<open>trace_class t\<close> and \<open>t \<ge> 0\<close>
  sorry

lemma kraus_family_map_abs_summable:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>(\<lambda>E. of_nat (\<EE> E) *\<^sub>C Abs_trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E*)) abs_summable_on UNIV\<close>
(*
proof -
  wlog \<rho>_pos: \<open>\<rho> \<ge> 0\<close> generalizing \<rho>
  proof -
    have aux: \<open>trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )\<close> 
      for \<rho> :: \<open>('a, 'a) trace_class\<close> and E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      by (simp add: trace_class_comp_left trace_class_comp_right)
    obtain \<rho>1 \<rho>2 \<rho>3 \<rho>4 a1 a2 a3 a4 where \<rho>_decomp: \<open>\<rho> = a1 *\<^sub>C \<rho>1 + a2 *\<^sub>C \<rho>2 + a3 *\<^sub>C \<rho>3 + a4 *\<^sub>C \<rho>4\<close>
      and pos: \<open>\<rho>1 \<ge> 0\<close> \<open>\<rho>2 \<ge> 0\<close> \<open>\<rho>3 \<ge> 0\<close> \<open>\<rho>4 \<ge> 0\<close>
      by -
    have \<open>norm (of_nat (\<EE> x) *\<^sub>C Abs_trace_class (x o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L x* )) 
      \<le> norm (a1 *\<^sub>C of_nat (\<EE> x) *\<^sub>C Abs_trace_class (x o\<^sub>C\<^sub>L from_trace_class \<rho>1 o\<^sub>C\<^sub>L x* ))
      + norm (a2 *\<^sub>C of_nat (\<EE> x) *\<^sub>C Abs_trace_class (x o\<^sub>C\<^sub>L from_trace_class \<rho>2 o\<^sub>C\<^sub>L x* ))
      + norm (a3 *\<^sub>C of_nat (\<EE> x) *\<^sub>C Abs_trace_class (x o\<^sub>C\<^sub>L from_trace_class \<rho>3 o\<^sub>C\<^sub>L x* ))
      + norm (a4 *\<^sub>C of_nat (\<EE> x) *\<^sub>C Abs_trace_class (x o\<^sub>C\<^sub>L from_trace_class \<rho>4 o\<^sub>C\<^sub>L x* ))\<close> 
      (is \<open>_ \<le> ?S x\<close>) for x
      apply (auto intro!: mult_left_mono
          simp add: norm_trace_class.abs_eq eq_onp_def trace_class_plus trace_class_scaleC
          aux trace_class_adj \<rho>_decomp plus_trace_class.rep_eq scaleC_trace_class.rep_eq
          cblinfun_compose_add_right cblinfun_compose_add_left
          scaleC_left_commute[of _ \<open>of_nat (\<EE> x)\<close>]
          simp flip: ring_distribs
          simp del: scaleC_scaleC)
      by (smt (verit) local.aux trace_class_plus trace_class_scaleC trace_norm_scaleC trace_norm_triangle)
    then have *: \<open>norm (of_nat (\<EE> x) *\<^sub>C Abs_trace_class (x o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L x* )) 
      \<le> norm (?S x)\<close> for x
      by force
    show ?thesis
      apply (rule abs_summable_on_comparison_test[OF _ *])
      by (intro abs_summable_on_add abs_summable_norm abs_summable_on_scaleC_right hypothesis pos)
  qed
  have aux: \<open>trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )\<close> 
    for \<rho> :: \<open>('a, 'a) trace_class\<close> and E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    by (simp add: trace_class_comp_left trace_class_comp_right)
  define n\<rho> where \<open>n\<rho> = norm \<rho>\<close>
  have *: \<open>norm (of_nat (\<EE> E) *\<^sub>C Abs_trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* ))
      \<le> norm (norm \<rho> *\<^sub>C of_nat (\<EE> E) *\<^sub>C norm (E* o\<^sub>C\<^sub>L E))\<close> for E
  proof -
    have \<open>norm (Abs_trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )) =
          trace_norm (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )\<close>
      by (simp add: norm_trace_class.abs_eq eq_onp_def aux)
    also have \<open>\<dots> = trace (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )\<close>
      by (metis \<rho>_pos abs_op_def from_trace_class_0 less_eq_trace_class.rep_eq sandwich_apply sandwich_pos sqrt_op_unique trace_abs_op)
    also have \<open>\<dots> = trace (from_trace_class \<rho> o\<^sub>C\<^sub>L (E* o\<^sub>C\<^sub>L E))\<close>
      by (simp add: Misc.lift_cblinfun_comp(2) circularity_of_trace trace_class_comp_left)
    also have \<open>\<dots> \<le> trace_norm (from_trace_class \<rho>) * norm (E* o\<^sub>C\<^sub>L E)\<close>
      by (metis Extra_Ordered_Fields.sign_simps(5) calculation circularity_of_trace cmod_trace_times complex_of_real_cmod complex_of_real_mono complex_of_real_nn_iff norm_ge_zero trace_class_from_trace_class)
    also have \<open>\<dots> = norm \<rho> * norm (E* o\<^sub>C\<^sub>L E)\<close>
      by (simp add: norm_trace_class.rep_eq)
    finally show ?thesis
  sledgehammer
  by X (smt (verit, del_insts) Extra_Ordered_Fields.sign_simps(5) Extra_Ordered_Fields.sign_simps(6)
 \<open>complex_of_real (trace_norm (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )) = trace (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )\<close> 
\<open>norm (Abs_trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )) = trace_norm (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )\<close>
 \<open>trace (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* ) = trace (from_trace_class \<rho> o\<^sub>C\<^sub>L (E* o\<^sub>C\<^sub>L E))\<close> 
cmod_trace_times' mult_left_mono norm_AadjA norm_ge_zero 
norm_mult norm_of_nat norm_of_real norm_trace_class.rep_eq of_real_power trace_class_from_trace_class)
  try0
  by -
qed
  from assms obtain B where B: \<open>norm (\<Sum>E\<in>S. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> B\<close> if \<open>finite S\<close> for S
    by (auto simp: kraus_family_def)

  show ?thesis
    apply (rule abs_summable_on_comparison_test[OF _ *])
    apply (rule abs_summable_on_scaleC_right)
(* TODO: Impossible goal here. E* o E only bounded in Loewner order, not in norm *)
    apply (rule nonneg_bdd_above_summable_on, simp)
    apply (rule bdd_aboveI[where M=B])
    using B' apply safe
  by -



  show \<open>\<rho> \<ge> 0\<close>
  sorry
*)
  sorry

lemma kraus_family_map_summable:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>(\<lambda>E. of_nat (\<EE> E) *\<^sub>C Abs_trace_class (sandwich E *\<^sub>V from_trace_class \<rho>)) summable_on UNIV\<close>
  apply (rule abs_summable_summable)
  unfolding sandwich_apply
  using assms by (rule kraus_family_map_abs_summable)

lemma kraus_family_map_bounded_tight:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_norm \<EE> = (\<Squnion>\<rho>. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close>
proof (rule antisym)
  from assms
  have bounded: \<open>norm (kraus_family_map \<EE> \<rho>) / norm \<rho> \<le> kraus_family_norm \<EE>\<close> for \<rho>
    apply (cases \<open>\<rho> = 0\<close>)
    by (simp_all add: kraus_family_norm_geq0 kraus_family_map_bounded linordered_field_class.pos_divide_le_eq)

  have aux1: \<open>0 \<le> (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C
            Abs_trace_class (E o\<^sub>C\<^sub>L from_trace_class (Abs_trace_class (selfbutter \<psi>)) o\<^sub>C\<^sub>L E*))\<close> for \<psi> M
    by (auto intro!: norm_cblinfun_mono sum_nonneg sum_mono
        scaleC_nonneg_nonneg of_nat_0_le_iff Abs_trace_class_geq0I trace_class_sandwich sandwich_pos
        simp: Abs_trace_class_inverse
        simp flip: sandwich_apply)

  show \<open>(\<Squnion>\<rho>. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>) \<le> kraus_family_norm \<EE>\<close>
    apply (rule cSUP_least)
    using bounded by auto
  show \<open>kraus_family_norm \<EE> \<le> (\<Squnion>\<rho>. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close>
    unfolding kraus_family_norm_def
  proof (rule cSUP_least)
    show \<open>Collect finite \<noteq> {}\<close>
      by auto
    fix M :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
    assume \<open>M \<in> Collect finite\<close>
    then have [simp]: \<open>finite M\<close> by simp
    have \<open>norm (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) - \<epsilon> \<le> (\<Squnion>\<rho>. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close> 
      (is \<open>?lhs \<le> ?rhs\<close>) if \<open>\<epsilon> > 0\<close> for \<epsilon>
    proof (cases \<open>\<forall>\<psi>::'a. \<psi> = 0\<close>)
      case True
      then have *: \<open>(A::'a\<Rightarrow>\<^sub>C\<^sub>L'a) = 0\<close> for A
        apply (rule_tac cblinfun_eqI)
        by auto
      show ?thesis
        apply (rule cSUP_upper2[where x=0])
        apply (rule bdd_aboveI[where M=\<open>kraus_family_norm \<EE>\<close>])
        using bounded \<open>\<epsilon> > 0\<close> by (auto simp: *[of \<open>sum _ _\<close>])
    next
      case False
      then have [simp]: \<open>class.not_singleton TYPE('a)\<close>
        apply intro_classes by blast
      obtain \<psi> where \<open>?lhs \<le> \<psi> \<bullet>\<^sub>C ((\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) *\<^sub>V \<psi>)\<close> and \<open>norm \<psi> = 1\<close>
        apply atomize_elim
        apply (rule cblinfun_norm_approx_witness_cinner[internalize_sort' 'a])
        using \<open>\<epsilon> > 0\<close>
        by (auto intro!: chilbert_space_axioms sum_nonneg scaleC_nonneg_nonneg of_nat_0_le_iff positive_cblinfun_squareI[OF refl])
      then have \<open>?lhs \<le> \<psi> \<bullet>\<^sub>C ((\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) *\<^sub>V \<psi>)\<close> (* Just restating *)
        by simp
      also have \<open>\<dots> = trace ((\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) o\<^sub>C\<^sub>L selfbutter \<psi>)\<close>
        by (simp flip: trace_butterfly_comp')
      also have \<open>\<dots> = (\<Sum>E\<in>M. complex_of_nat (\<EE> E) * trace (E* o\<^sub>C\<^sub>L (E o\<^sub>C\<^sub>L selfbutter \<psi>)))\<close>
        by (simp add: trace_class_scaleC trace_class_comp_right cblinfun_compose_sum_left
            cblinfun_compose_assoc
            flip: trace_scaleC trace_sum)
      also have \<open>\<dots> = (\<Sum>E\<in>M. complex_of_nat (\<EE> E) * trace (sandwich E (selfbutter \<psi>)))\<close>
        by (simp add: trace_class_comp_right sandwich_apply flip: circularity_of_trace)
      also have \<open>\<dots> = trace (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (sandwich E (selfbutter \<psi>)))\<close>
        by (simp add: trace_class_scaleC trace_class_comp_right cblinfun_compose_assoc trace_class_sandwich
            flip: trace_scaleC trace_sum)
      also have \<open>\<dots> = trace_norm (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (sandwich E (selfbutter \<psi>)))\<close>
        by (simp_all add: sandwich_pos of_nat_0_le_iff scaleC_nonneg_nonneg sum_nonneg abs_op_id_on_pos
            flip: trace_abs_op)
      also have \<open>\<dots> \<le> norm (\<Sum>E\<in>M.
             complex_of_nat (\<EE> E) *\<^sub>C Abs_trace_class (E o\<^sub>C\<^sub>L from_trace_class (Abs_trace_class (selfbutter \<psi>)) o\<^sub>C\<^sub>L E*))\<close>
        by (simp add: norm_trace_class.rep_eq from_trace_class_sum scaleC_trace_class.rep_eq
             Abs_trace_class_inverse trace_class_sandwich
             flip: sandwich_apply)
    
(*       (* Experiment *)
      have \<open>norm (\<Sum>E\<in>M.
             complex_of_nat (\<EE> E) *\<^sub>C Abs_trace_class (E o\<^sub>C\<^sub>L from_trace_class (Abs_trace_class (selfbutter \<psi>)) o\<^sub>C\<^sub>L E* ))
\<le> 
norm (\<Sum>E\<in>UNIV.
               complex_of_nat (\<EE> E) *\<^sub>C
               Abs_trace_class (E o\<^sub>C\<^sub>L from_trace_class (Abs_trace_class (selfbutter \<psi>)) o\<^sub>C\<^sub>L E* ))
\<close>
        apply (rule norm_cblinfun_mono_trace_class)
 *)

      also have \<open>\<dots> \<le> norm (kraus_family_map \<EE> (Abs_trace_class (selfbutter \<psi>)))\<close>
        apply (rule complex_of_real_mono)
        unfolding kraus_family_map_def
        using aux1 apply (rule norm_cblinfun_mono_trace_class)
        apply (subst infsum_finite[symmetric], simp)
        apply (rule infsum_mono_neutral_traceclass)
            apply (auto intro!: aux1 scaleC_nonneg_nonneg of_nat_0_le_iff
            Abs_trace_class_geq0I trace_class_sandwich sandwich_pos
            kraus_family_map_summable \<open>kraus_family \<EE>\<close>
            simp: summable_on_finite
            simp flip: sandwich_apply Abs_trace_class_inverse)
        using kraus_family_map_summable
        by (simp add: Abs_trace_class_inverse)
      also have \<open>\<dots> = norm (kraus_family_map \<EE> (Abs_trace_class (selfbutter \<psi>))) / norm (Abs_trace_class (selfbutter \<psi>))\<close>
        by (simp add: norm_trace_class.abs_eq eq_onp_def trace_norm_butterfly \<open>norm \<psi> = 1\<close>)
      also have \<open>\<dots> \<le> ?rhs\<close>
        apply (rule complex_of_real_mono)
        apply (rule cSup_upper)
        apply simp
        apply (rule bdd_aboveI[where M=\<open>kraus_family_norm \<EE>\<close>])
        using bounded by auto
      finally show ?thesis
        using complex_of_real_mono_iff by blast
    qed
    then show \<open>norm (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> (\<Squnion>\<rho>. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close>
      by (smt (verit, ccfv_SIG) nice_ordered_field_class.field_le_epsilon)
  qed
qed


lemma
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>((\<lambda>F. norm (\<Sum>E\<in>F. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E))) \<longlongrightarrow> kraus_family_norm \<EE>) (finite_subsets_at_top UNIV)\<close>
  sorry

lemma kraus_family_norm_welldefined:
  assumes \<open>kraus_equivalent \<EE> \<FF>\<close>
  shows \<open>kraus_family_norm \<EE> = kraus_family_norm \<FF>\<close>
  using assms unfolding kraus_equivalent_def
  by (smt (z3) SUP_cong kraus_family_map_bounded_tight)

lift_definition kraus_map_norm :: \<open>('a::chilbert_space, 'b::chilbert_space) kraus_map \<Rightarrow> real\<close> is
  kraus_family_norm
  by (rule kraus_family_norm_welldefined)

lemma kraus_map_of_op_norm[simp]:
  \<open>kraus_map_norm (kraus_map_of_op E) = (norm E)\<^sup>2\<close>
  apply (transfer fixing: E)
  by simp

lemma less_eq_scaled_id_norm: 
  assumes \<open>norm A \<le> c\<close> and \<open>A = A*\<close>
  shows \<open>A \<le> complex_of_real c *\<^sub>C id_cblinfun\<close>
proof -
  have \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<le> complex_of_real c\<close> if \<open>norm x = 1\<close> for x
  proof -
    have \<open>norm (x \<bullet>\<^sub>C (A *\<^sub>V x)) \<le> norm (A *\<^sub>V x)\<close>
      by (metis complex_inner_class.Cauchy_Schwarz_ineq2 mult_cancel_right1 that)
    also have \<open>\<dots> \<le> norm A\<close>
      by (metis more_arith_simps(6) norm_cblinfun that)
    also have \<open>\<dots> \<le> c\<close>
      by (rule assms)
    finally have \<open>norm (x \<bullet>\<^sub>C (A *\<^sub>V x)) \<le> c\<close>
      by -
    moreover have \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<in> \<real>\<close>
      by (metis assms(2) cinner_hermitian_real)
    ultimately show ?thesis
      by (metis cnorm_le_square complex_of_real_cmod complex_of_real_mono complex_of_real_nn_iff dual_order.trans reals_zero_comparable)
  qed
  then show ?thesis
    by (smt (verit) cblinfun.scaleC_left cblinfun_id_cblinfun_apply cblinfun_leI cinner_scaleC_right cnorm_eq_1 mult_cancel_left2)
qed

lemma kraus_family_comp_finite:
  assumes \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close> and \<open>G \<noteq> 0\<close>
  shows \<open>finite {(E, F). \<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F = G}\<close>
proof (rule ccontr)
  assume infinite: \<open>infinite {(E, F). \<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F = G}\<close>
  from assms obtain BE where BE: \<open>norm (\<Sum>E\<in>S. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> if \<open>finite S\<close> for S
    by (auto simp: kraus_family_def)
  then have \<open>BE \<ge> 0\<close>
    by force
  from assms obtain BF where BF: \<open>norm (\<Sum>F\<in>S. \<FF> F *\<^sub>C (F* o\<^sub>C\<^sub>L F)) \<le> BF\<close> if \<open>finite S\<close> for S
    by (auto simp: kraus_family_def)
  from infinite obtain S where [simp]: \<open>finite S\<close> and S_subset: \<open>S \<subseteq> {(E, F). \<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F = G}\<close>
    and S_size: \<open>card S > BE * BF / norm (G* o\<^sub>C\<^sub>L G)\<close>
    by (smt (verit, best) infinite_arbitrarily_large reals_Archimedean2)
  define SE SF where \<open>SE = fst ` S\<close> and \<open>SF = snd ` S\<close>
  have \<open>BE * BF < card S * norm (G* o\<^sub>C\<^sub>L G)\<close>
    by (meson S_size assms(3) linordered_field_class.pos_divide_less_eq op_square_nondegenerate zero_less_norm_iff)
  also have \<open>\<dots> = norm (\<Sum>(F,E)\<in>prod.swap ` S. G* o\<^sub>C\<^sub>L G)\<close>
    by (simp add: case_prod_beta sum_constant_scale card_image)
  also have \<open>\<dots> \<le> norm (\<Sum>(F,E)\<in>prod.swap ` S. of_nat (\<EE> E * \<FF> F) *\<^sub>C (G* o\<^sub>C\<^sub>L G))\<close>
  proof -
    have \<open>G* o\<^sub>C\<^sub>L G \<le> (of_nat (\<EE> E) * of_nat (\<FF> F)) *\<^sub>C (G* o\<^sub>C\<^sub>L G)\<close> if \<open>(E, F) \<in> S\<close> for E F
    proof -
      from that have geq1: \<open>\<EE> E \<ge> 1\<close> \<open>\<FF> F \<ge> 1\<close>
        using S_subset by auto
      have \<open>G* o\<^sub>C\<^sub>L G = 1 *\<^sub>C (G* o\<^sub>C\<^sub>L G)\<close>
        by simp
      also have \<open>\<dots> \<le> (of_nat (\<EE> E) * of_nat (\<FF> F)) *\<^sub>C (G* o\<^sub>C\<^sub>L G)\<close>
        apply (intro scaleC_right_mono)
        using geq1 apply (simp_all add: less_eq_complex_def positive_cblinfun_squareI[OF refl]
            real_of_nat_ge_one_iff
            del: One_nat_def flip: of_nat_mult)
        by (metis mult_le_mono nat_mult_1 )
      finally show ?thesis
        by -
    qed
    then show ?thesis
      by (auto intro!: norm_cblinfun_mono sum_nonneg positive_cblinfun_squareI[OF refl] sum_mono)
  qed
  also have \<open>\<dots> = norm (\<Sum>(F,E)\<in>prod.swap ` S. of_nat (\<EE> E * \<FF> F) *\<^sub>C ((E o\<^sub>C\<^sub>L F)* o\<^sub>C\<^sub>L (E o\<^sub>C\<^sub>L F)))\<close>
    apply (rule arg_cong[where f=norm])
    apply (rule sum.cong, rule refl)
    using S_subset by auto
  also have \<open>\<dots> \<le> norm (\<Sum>(F,E)\<in>SF \<times> SE. of_nat (\<EE> E * \<FF> F) *\<^sub>C ((E o\<^sub>C\<^sub>L F)* o\<^sub>C\<^sub>L (E o\<^sub>C\<^sub>L F)))\<close>
    apply (auto intro!: norm_cblinfun_mono sum_nonneg scaleC_nonneg_nonneg mult_nonneg_nonneg
        of_nat_0_le_iff positive_cblinfun_squareI[OF refl] sum_mono2
        simp: SE_def[abs_def] SF_def[abs_def]
        simp del: adj_cblinfun_compose)
    by force+
  also have \<open>\<dots> = norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C sandwich (F*)
                             (\<Sum>E\<in>SE. of_nat (\<EE> E) *\<^sub>C ((E* o\<^sub>C\<^sub>L E))))\<close>
    by (simp add: sum.cartesian_product scaleC_sum_right 
        sandwich_apply Extra_Ordered_Fields.sign_simps(5)
        cblinfun_compose_assoc cblinfun_compose_sum_right cblinfun_compose_sum_left)
  also have \<open>\<dots> \<le> norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C sandwich (F*) (BE *\<^sub>C id_cblinfun))\<close>
    by (auto intro!: norm_cblinfun_mono sum_nonneg scaleC_nonneg_nonneg of_nat_0_le_iff
        sum_mono sandwich_pos positive_cblinfun_squareI[OF refl] scaleC_left_mono
        sandwich_mono less_eq_scaled_id_norm BE  finite_imageI
        simp: SE_def[abs_def] SF_def[abs_def] sum_adj)
  also have \<open>\<dots> = BE * norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C F* o\<^sub>C\<^sub>L F)\<close>
    by (simp flip: scaleC_scaleC scaleC_sum_right 
        add: sandwich_apply \<open>BE \<ge> 0\<close> scaleC_left_commute)
  also have \<open>\<dots> \<le> BE * BF\<close>
    by (auto intro!: mult_left_mono \<open>BE \<ge> 0\<close> BF finite_imageI simp: SF_def[abs_def])
  finally show False
    by simp
qed

lemma kraus_family_kraus_family_comp: 
  assumes \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family (kraus_family_comp \<EE> \<FF>)\<close>
proof -
  from assms obtain BE where BE: \<open>norm (\<Sum>E\<in>S. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> if \<open>finite S\<close> for S
    by (auto simp: kraus_family_def)
  then have \<open>BE \<ge> 0\<close>
    by force
  from assms obtain BF where BF: \<open>norm (\<Sum>F\<in>S. \<FF> F *\<^sub>C (F* o\<^sub>C\<^sub>L F)) \<le> BF\<close> if \<open>finite S\<close> for S
    by (auto simp: kraus_family_def)
  have \<open>norm (\<Sum>G\<in>S. kraus_family_comp \<EE> \<FF> G *\<^sub>C (G* o\<^sub>C\<^sub>L G)) \<le> BE * BF\<close> if \<open>finite S\<close> for S
  proof -
    define EF_G EF_S where \<open>EF_G G = {(E, F). \<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F = G}\<close>
      and \<open>EF_S = {(E, F). \<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F \<in> S-{0}}\<close> for G
    define SE SF where \<open>SE = fst ` EF_S\<close> and \<open>SF = snd ` EF_S\<close>
    have finite_EF: \<open>finite (EF_G G)\<close> if \<open>G \<noteq> 0\<close> for G :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      by (unfold EF_G_def, intro kraus_family_comp_finite assms that)
    then have finite_EFS: \<open>finite EF_S\<close>
      apply (subst asm_rl[of \<open>EF_S = (\<Union>G\<in>S-{0}. EF_G G)\<close>])
       apply (auto simp: EF_S_def EF_G_def)[1]
      by (auto intro!: finite_UN_I \<open>finite S\<close> finite_EF finite_Diff)
    have \<open>norm (\<Sum>G\<in>S. kraus_family_comp \<EE> \<FF> G *\<^sub>C (G* o\<^sub>C\<^sub>L G))
      = norm (\<Sum>G\<in>S-{0}. kraus_family_comp \<EE> \<FF> G *\<^sub>C (G* o\<^sub>C\<^sub>L G))\<close>
      by (auto intro!: arg_cong[where f=norm] sum.mono_neutral_right \<open>finite S\<close>)
    also have \<open>\<dots> = norm (\<Sum>G\<in>S-{0}. (\<Sum>(E, F)\<in>EF_G G. of_nat (\<EE> E * \<FF> F) *\<^sub>C (G* o\<^sub>C\<^sub>L G)))\<close>
      by (simp add: kraus_family_comp_def case_prod_beta scaleC_sum_left EF_G_def)
    also have \<open>\<dots> = norm (\<Sum>(G,E,F)\<in>(SIGMA G:S-{0}. EF_G G). of_nat (\<EE> E * \<FF> F) *\<^sub>C (G* o\<^sub>C\<^sub>L G))\<close>
      apply (subst sum.Sigma)
      using that finite_EF by auto
    also have \<open>\<dots> = norm (\<Sum>(G,E,F)\<in>(\<lambda>(F,E). (E o\<^sub>C\<^sub>L F, E, F)) ` prod.swap ` EF_S. 
                                             of_nat (\<EE> E * \<FF> F) *\<^sub>C (G* o\<^sub>C\<^sub>L G))\<close>
      apply (rule arg_cong[where f=norm])
      apply (rule sum.cong)
      by (auto simp: EF_S_def EF_G_def)
    also have \<open>\<dots> = norm (\<Sum>(F,E)\<in>prod.swap ` EF_S. 
                  of_nat (\<EE> E * \<FF> F) *\<^sub>C ((E o\<^sub>C\<^sub>L F)* o\<^sub>C\<^sub>L (E o\<^sub>C\<^sub>L F)))\<close>
      apply (subst sum.reindex)
      by (auto intro!: inj_onI simp: case_prod_beta)
    also have \<open>\<dots> \<le> norm (\<Sum>(F,E)\<in>SF \<times> SE. 
                  of_nat (\<EE> E * \<FF> F) *\<^sub>C ((E o\<^sub>C\<^sub>L F)* o\<^sub>C\<^sub>L (E o\<^sub>C\<^sub>L F)))\<close>
      apply (auto intro!: norm_cblinfun_mono sum_nonneg scaleC_nonneg_nonneg mult_nonneg_nonneg
          of_nat_0_le_iff positive_cblinfun_squareI[OF refl] sum_mono2 finite_cartesian_product
          finite_EFS finite_imageI
          simp: SE_def[abs_def] SF_def[abs_def]
          simp del: adj_cblinfun_compose)
      by force+
    also have \<open>\<dots> = norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C sandwich (F*)
                             (\<Sum>E\<in>SE. of_nat (\<EE> E) *\<^sub>C ((E* o\<^sub>C\<^sub>L E))))\<close>
      by (simp add: case_prod_beta sum.cartesian_product scaleC_sum_right scaleC_scaleC
          sandwich_apply Extra_Ordered_Fields.sign_simps(5)
          cblinfun_compose_assoc cblinfun_compose_sum_right cblinfun_compose_sum_left)
    also have \<open>\<dots> \<le> norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C sandwich (F*) (BE *\<^sub>C id_cblinfun))\<close>
      by (auto intro!: norm_cblinfun_mono sum_nonneg scaleC_nonneg_nonneg of_nat_0_le_iff
          sum_mono sandwich_pos positive_cblinfun_squareI[OF refl] scaleC_left_mono
          sandwich_mono less_eq_scaled_id_norm BE finite_EFS finite_imageI
          simp: SE_def[abs_def] SF_def[abs_def] sum_adj)
    also have \<open>\<dots> = BE * norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C F* o\<^sub>C\<^sub>L F)\<close>
      by (simp flip: scaleC_scaleC scaleC_sum_right 
          add: sandwich_apply \<open>BE \<ge> 0\<close> scaleC_left_commute)
    also have \<open>\<dots> \<le> BE * BF\<close>
      by (auto intro!: mult_left_mono \<open>BE \<ge> 0\<close> BF finite_imageI finite_EFS
          simp: SF_def[abs_def])
    finally show ?thesis
      by -
  qed
  then show ?thesis
    by (auto simp: kraus_family_def)
qed

lemma abs_summable_on_add:
  fixes f g :: \<open>_ \<Rightarrow> 'e ell2\<close> (* TODO more general *)
  assumes \<open>f abs_summable_on A\<close> and \<open>g abs_summable_on A\<close>
  shows \<open>(\<lambda>x. f x + g x) abs_summable_on A\<close>
proof -
  from assms have \<open>(\<lambda>x. norm (f x) + norm (g x)) summable_on A\<close>
    using summable_on_add by blast
  then show ?thesis
    apply (rule Infinite_Sum.abs_summable_on_comparison_test')
    using norm_triangle_ineq by blast
qed

lemma abs_summable_norm:
  assumes \<open>f abs_summable_on A\<close>
  shows \<open>(\<lambda>x. norm (f x)) abs_summable_on A\<close>
  using assms by simp

lemma abs_summable_on_scaleC_left [intro]:
  fixes c :: \<open>'a :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>C c) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_left assms simp: norm_scaleC)

lemma abs_summable_on_scaleC_right [intro]:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A"
  shows   "(\<lambda>x. c *\<^sub>C f x) abs_summable_on A"
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (auto intro!: summable_on_cmult_right assms simp: norm_scaleC)


lemma kraus_family_comp_apply:
  assumes \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) = kraus_family_map \<EE> \<circ> kraus_family_map \<FF>\<close>
  sorry

lift_definition kraus_map_comp :: \<open>('a::chilbert_space,'b::chilbert_space) kraus_map
                                \<Rightarrow> ('c::chilbert_space,'a) kraus_map \<Rightarrow> ('c,'b) kraus_map\<close>
  is kraus_family_comp
  by (auto intro!: kraus_family_kraus_family_comp
      simp add: kraus_equivalent_def kraus_family_comp_apply)


(* TODO replace original *) thm norm_leq_trace_norm
lemma norm_leq_trace_norm: \<open>norm t \<le> trace_norm t\<close> if \<open>trace_class t\<close> 
  for t :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> (* TODO get rid of "not_singleton" *)
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    apply (rule norm_leq_trace_norm[internalize_sort' 'a, where t=t])
    using that chilbert_space_axioms True by auto
next
  case False
  then have x0: \<open>x = 0\<close> for x :: 'a
    by (simp add: class.not_singleton_def)
  have \<open>t = 0\<close>
    apply (rule cblinfun_eqI)
    apply (subst x0)
    by simp
  then show ?thesis 
    by simp
qed

(* TODO move to Trace_Class *)
lift_definition tc_compose :: \<open>('b::chilbert_space, 'c::chilbert_space) trace_class 
                               \<Rightarrow> ('a::chilbert_space, 'b) trace_class \<Rightarrow> ('a,'c) trace_class\<close> is
    cblinfun_compose
  by (simp add: trace_class_comp_left)

lemma norm_tc_compose:
  \<open>norm (tc_compose a b) \<le> norm a * norm b\<close>
proof transfer
  fix a :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and b :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'c\<close>
  assume \<open>a \<in> Collect trace_class\<close> and tc_b: \<open>b \<in> Collect trace_class\<close>
  then have \<open>trace_norm (a o\<^sub>C\<^sub>L b) \<le> trace_norm a * norm b\<close>
    by (simp add: trace_norm_comp_left)
  also have \<open>\<dots> \<le> trace_norm a * trace_norm b\<close>
    using tc_b by (auto intro!: mult_left_mono norm_leq_trace_norm)
  finally show \<open>trace_norm (a o\<^sub>C\<^sub>L b) \<le> trace_norm a * trace_norm b\<close>
    by -
qed

typedef ('a,'b) cq_operator = \<open>{f :: 'a \<Rightarrow> ('b ell2, 'b ell2) trace_class. f abs_summable_on UNIV}\<close>
  morphisms cq_operator_at Abs_cq_operator
  apply (rule exI[of _ \<open>\<lambda>_. 0\<close>])
  by auto
setup_lifting type_definition_cq_operator

(* TODO move *)
lemma abs_summable_product':
  fixes x :: "'a \<Rightarrow> 'b::{real_normed_algebra}"
  assumes "(\<lambda>i. x i) abs_summable_on A"
    and "(\<lambda>i. y i) abs_summable_on A"
  shows "(\<lambda>i. x i * y i) abs_summable_on A"
proof -
  from assms have \<open>(\<lambda>(i,j). x i * y j) abs_summable_on A \<times> A\<close>
    by (rule abs_summable_times)
  then have \<open>(\<lambda>(i,j). x i * y j) abs_summable_on (\<lambda>a. (a,a)) ` A\<close>
    apply (rule summable_on_subset_banach)
    by auto
  then show ?thesis
    apply (subst (asm) summable_on_reindex)
    by (auto intro: inj_onI simp: o_def)
qed

(* TODO move *)
lemma abs_summable_add:
  fixes f g :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes \<open>f abs_summable_on A\<close>
  assumes \<open>g abs_summable_on A\<close>
  shows \<open>(\<lambda>x. f x + g x) abs_summable_on A\<close>
  apply (rule abs_summable_on_comparison_test[where g=\<open>\<lambda>x. norm (f x) + norm (g x)\<close>])
  using assms by (auto intro!: summable_on_add simp add: norm_triangle_ineq)

(* TODO move *)
lemma abs_summable_minus:
  fixes f g :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes \<open>f abs_summable_on A\<close>
  assumes \<open>g abs_summable_on A\<close>
  shows \<open>(\<lambda>x. f x - g x) abs_summable_on A\<close>
  using abs_summable_add[where f=f and g=\<open>\<lambda>x. - g x\<close>]
  using assms by auto

instantiation cq_operator :: (type,type) complex_algebra begin
lift_definition zero_cq_operator :: \<open>('a,'b) cq_operator\<close> is \<open>\<lambda>_. 0\<close>
  by auto
lift_definition plus_cq_operator :: \<open>('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator\<close> is
  \<open>\<lambda>a b x. a x + b x\<close>
  by (rule abs_summable_add)
lift_definition minus_cq_operator :: \<open>('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator\<close> is
  \<open>\<lambda>a b x. a x - b x\<close>
  by (rule abs_summable_minus)
lift_definition uminus_cq_operator :: \<open>('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator\<close> is
  \<open>\<lambda>a x. - a x\<close>
  by simp
lift_definition scaleC_cq_operator :: \<open>complex \<Rightarrow> ('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator\<close> is
  \<open>\<lambda>c a x. c *\<^sub>C a x\<close>
  by (simp add: summable_on_cmult_right)
lift_definition scaleR_cq_operator :: \<open>real \<Rightarrow> ('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator\<close> is
  \<open>\<lambda>c a x. c *\<^sub>R a x\<close>
  using summable_on_cmult_right by auto
lift_definition times_cq_operator :: \<open>('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator\<close> is
  \<open>\<lambda>a b x. tc_compose (a x) (b x)\<close>
proof -
  fix a b :: \<open>'a \<Rightarrow> ('b ell2, 'b ell2) trace_class\<close>
  assume asum: \<open>a abs_summable_on UNIV\<close>
  assume bsum: \<open>b abs_summable_on UNIV\<close>
  have \<open>(\<lambda>x. norm (norm (a x)) * norm (norm (b x))) abs_summable_on UNIV\<close>
    apply (rule abs_summable_product')
    using asum bsum by auto
  then have \<open>(\<lambda>x. tc_compose (a x) (b x)) abs_summable_on UNIV\<close>
    apply (rule abs_summable_on_comparison_test)
    by (simp add: norm_tc_compose)
  then show \<open>(\<lambda>x. tc_compose (a x) (b x)) abs_summable_on UNIV\<close>
    by simp
qed
instance
proof intro_classes
  fix a b c :: \<open>('a, 'b) cq_operator\<close>
  show \<open>((*\<^sub>R) r :: ('a, 'b) cq_operator \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> for r :: real
    apply (rule ext)
    apply transfer
    by (simp add: scaleR_scaleC)
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer
    by auto
  show \<open>a + b = b + a\<close>
    apply transfer
    by auto
  show \<open>0 + a = a\<close>
    apply transfer
    by auto
  show \<open>- a + a = 0\<close>
    apply transfer
    by auto
  show \<open>a - b = a + - b\<close>
    apply transfer
    by auto
  show \<open>s *\<^sub>C (a + b) = s *\<^sub>C a + s *\<^sub>C b\<close> for s :: complex
    apply transfer
    by (simp add: complex_vector.vector_space_assms(1))
  show \<open>(s + t) *\<^sub>C a = s *\<^sub>C a + t *\<^sub>C a\<close> for s t :: complex
    apply transfer
    by (simp add: complex_vector.vector_space_assms(2))
  show \<open>s *\<^sub>C t *\<^sub>C a = (s * t) *\<^sub>C a\<close> for s t :: complex
    apply transfer
    by auto
  show \<open>1 *\<^sub>C a = a\<close>
    apply transfer
    by auto
  show \<open>a * b * c = a * (b * c)\<close>
    apply transfer
    apply transfer
    by (simp add: cblinfun_compose_assoc)
  show \<open>(a + b) * c = a * c + b * c\<close>
    apply transfer
    apply transfer
    using cblinfun_compose_add_left by blast
  show \<open>a * (b + c) = a * b + a * c\<close>
    apply transfer
    apply transfer
    by (meson cblinfun_compose_add_right)
  show \<open>s *\<^sub>C a * b = s *\<^sub>C (a * b)\<close> for s :: complex
    apply transfer
    apply transfer
    by simp
  show \<open>a * s *\<^sub>C b = s *\<^sub>C (a * b)\<close> for s :: complex
    apply transfer
    apply transfer
    by simp
qed
end

instantiation cq_operator :: (type,type) complex_normed_vector begin
lift_definition norm_cq_operator :: \<open>('a, 'b) cq_operator \<Rightarrow> real\<close> is
  \<open>\<lambda>a. \<Sum>\<^sub>\<infinity>x. norm (a x)\<close>.
definition \<open>sgn_cq_operator a = a /\<^sub>R norm a\<close> for a :: \<open>('a, 'b) cq_operator\<close>
definition \<open>dist_cq_operator a b = norm (a - b)\<close> for a b :: \<open>('a, 'b) cq_operator\<close>
definition [code del]: "uniformity_cq_operator = (INF e\<in>{0<..}. principal {(x::('a,'b) cq_operator, y). dist x y < e})"
definition [code del]: "open_cq_operator U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e\<in>{0<..}. principal {(x, y). dist x y < e}. x' = x \<longrightarrow> y \<in> U)"
  for U :: "('a,'b) cq_operator set"
instance
proof intro_classes
  fix a b c :: \<open>('a, 'b) cq_operator\<close>
  show \<open>dist a b = norm (a - b)\<close>
    by (simp add: dist_cq_operator_def)
  show \<open>sgn a = a /\<^sub>R norm a\<close>
    by (simp add: sgn_cq_operator_def)
  show \<open>uniformity = (INF e\<in>{0<..}. principal {(x::('a,'b) cq_operator, y). dist x y < e})\<close>
    using uniformity_cq_operator_def by force
  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)\<close>
    for U :: "('a,'b) cq_operator set"
    by (simp add: open_cq_operator_def uniformity_cq_operator_def)
  show \<open>norm a = 0 \<longleftrightarrow> a = 0\<close>
  proof (transfer, rule iffI)
    fix a :: \<open>'a \<Rightarrow> ('b ell2, 'b ell2) trace_class\<close>
    assume summable: \<open>(\<lambda>x. a x) abs_summable_on UNIV\<close>
    assume \<open>(\<Sum>\<^sub>\<infinity>x. norm (a x)) = 0\<close>
    then have \<open>norm (a x) = 0\<close> for x
      using summable nonneg_infsum_le_0D by force
    then show \<open>a = (\<lambda>_. 0)\<close>
      using norm_eq_zero by blast
  next
    fix a :: \<open>'a \<Rightarrow> ('b ell2, 'b ell2) trace_class\<close>
    assume \<open>a = (\<lambda>_. 0)\<close>
    then show \<open>(\<Sum>\<^sub>\<infinity>x. norm (a x)) = 0\<close>
      by simp
  qed
  show \<open>norm (a + b) \<le> norm a + norm b\<close>
  proof transfer
    fix a b :: \<open>'a \<Rightarrow> ('b ell2, 'b ell2) trace_class\<close>
    assume asummable: \<open>(\<lambda>x. a x) abs_summable_on UNIV\<close>
    assume bsummable: \<open>(\<lambda>x. b x) abs_summable_on UNIV\<close>
    have \<open>(\<Sum>\<^sub>\<infinity>x. norm (a x + b x)) \<le> (\<Sum>\<^sub>\<infinity>x. norm (a x) + norm (b x))\<close>
      apply (rule infsum_mono)
      using abs_summable_add asummable bsummable apply blast
      using asummable bsummable summable_on_add apply blast
      by (simp add: norm_triangle_ineq)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. norm (a x)) + (\<Sum>\<^sub>\<infinity>x. norm (b x))\<close>
      using asummable bsummable by (rule infsum_add)
    finally show \<open>(\<Sum>\<^sub>\<infinity>x. norm (a x + b x)) \<le> (\<Sum>\<^sub>\<infinity>x. norm (a x)) + (\<Sum>\<^sub>\<infinity>x. norm (b x))\<close>
      by -
  qed
  show \<open>norm (r *\<^sub>R a) = \<bar>r\<bar> * norm a\<close> for r :: real
    apply transfer
    by (simp add: infsum_cmult_right')
  show \<open>norm (s *\<^sub>C a) = cmod s * norm a\<close> for s :: complex
    apply transfer
    by (simp add: infsum_cmult_right')
qed
end

instance cq_operator :: (type,type) cbanach
proof intro_classes
  fix F :: \<open>nat \<Rightarrow> ('a, 'b) cq_operator\<close>
  define f where \<open>f n x = cq_operator_at (F n) x\<close> for x n
  assume \<open>Cauchy F\<close>
  have cauchy_sum_f: \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>S. finite S \<longrightarrow> (\<Sum>x\<in>S. norm (f m x - f n x)) < e\<close> if \<open>e > 0\<close> for e
  proof -
    from \<open>Cauchy F\<close> that obtain M where cauchy_X: \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. norm (F m - F n) < e\<close>
      by (auto simp: Cauchy_iff)
    have \<open>(\<Sum>x\<in>S. norm (f m x - f n x)) < e\<close> if \<open>m \<ge> M\<close> and \<open>n \<ge> M\<close> and \<open>finite S\<close> for m n S
    proof -
      from cauchy_X have \<open>norm (F m - F n) < e\<close>
        using that by auto
      then have *: \<open>(\<Sum>\<^sub>\<infinity>x. norm (f m x - f n x)) < e\<close>
        unfolding f_def apply (transfer fixing: n m M) using that by auto
      have \<open>(\<Sum>x\<in>S. norm (f m x - f n x)) \<le> (\<Sum>\<^sub>\<infinity>x. norm (f m x - f n x))\<close>
        apply (rule finite_sum_le_infsum)
          apply (smt (verit, del_insts) f_def cq_operator_at mem_Collect_eq minus_cq_operator.rep_eq summable_on_cong)
        by (simp_all add: that)
      also have \<open>\<dots> < e\<close>
        using "*" by blast
      finally show ?thesis
        by -
    qed
    then show ?thesis
      by auto
  qed

  have cauchy_f: \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm (f m x - f n x) < e\<close> if \<open>e > 0\<close> for e
  proof -
    from cauchy_sum_f[OF \<open>e > 0\<close>]
    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. (\<Sum>x\<in>{x}. norm (f m x - f n x)) < e\<close>
      apply (rule ex_mono[rule_format, rotated])
      by blast
    then show ?thesis
      by simp
  qed

  have \<open>Cauchy (\<lambda>n. f n x)\<close> for x
    apply (rule CauchyI)
    using cauchy_f 
    by meson
  then have \<open>convergent (\<lambda>n. f n x)\<close> for x
    using Cauchy_convergent by blast
  then obtain l where f_l: \<open>(\<lambda>n. f n x) \<longlonglongrightarrow> l x\<close> for x
    apply atomize_elim apply (rule choice)
    using convergent_def by blast
  have X_l_conv: \<open>\<exists>M. \<forall>n\<ge>M. ((\<lambda>x. f n x - l x) abs_summable_on UNIV) \<and> (\<Sum>\<^sub>\<infinity>x. norm (f n x - l x)) < e\<close> if \<open>e > 0\<close> for e
  proof -
    define d where \<open>d = e/2\<close>
    then have \<open>d > 0\<close>
      using half_gt_zero that by blast
    from cauchy_sum_f[OF this] obtain M where f_sum_d: \<open>(\<Sum>x\<in>S. norm (f m x - f n x)) < d\<close> 
      if \<open>m\<ge>M\<close> and \<open>n\<ge>M\<close> and \<open>finite S\<close> for m n S
      by auto
    have \<open>(\<lambda>n. \<Sum>x\<in>S. norm (f m x - f n x)) \<longlonglongrightarrow> (\<Sum>x\<in>S. norm (f m x - l x))\<close> if \<open>m \<ge> M\<close> and \<open>finite S\<close> for m S
      by (intro tendsto_sum tendsto_norm tendsto_diff tendsto_const f_l)
    then have *: \<open>(\<Sum>x\<in>S. norm (f m x - l x)) \<le> d\<close> if \<open>m \<ge> M\<close> and \<open>finite S\<close> for m S
      apply (rule Lim_bounded[where M=M])
      using f_sum_d[OF \<open>m \<ge> M\<close> _ \<open>finite S\<close>] that
      using less_imp_le by auto
    then have **: \<open>(\<lambda>x. f m x - l x) abs_summable_on UNIV\<close> if \<open>m \<ge> M\<close> for m
      apply (subst abs_summable_iff_bdd_above)
      using that by fastforce
    then have \<open>(\<Sum>\<^sub>\<infinity>x. norm (f m x - l x)) \<le> d\<close> if \<open>m \<ge> M\<close> for m
      apply (rule infsum_le_finite_sums)
      using that * by auto
    then have \<open>(\<Sum>\<^sub>\<infinity>x. norm (f m x - l x)) < e\<close> if \<open>m \<ge> M\<close> for m
      using that \<open>0 < e\<close> by (fastforce simp: d_def)
    with ** show ?thesis
      by (auto intro!: exI[of _ M])
  qed

  have l_sum: \<open>(\<lambda>x. l x) abs_summable_on UNIV\<close>
  proof -
    from X_l_conv obtain M where \<open>((\<lambda>x. f M x - l x) abs_summable_on UNIV)\<close>
      by (meson gt_ex order_refl)
    moreover have \<open>f M abs_summable_on UNIV\<close>
      using f_def[abs_def] cq_operator_at by blast
    ultimately have \<open>(\<lambda>x. f M x - (f M x - l x)) abs_summable_on UNIV\<close>
      apply (rule_tac abs_summable_minus) by auto
    then show ?thesis
      by auto
  qed
  define L where \<open>L = Abs_cq_operator l\<close>
  have Ll: \<open>cq_operator_at L = l\<close>
    by (simp add: L_def l_sum Abs_cq_operator_inverse)
  have \<open>F \<longlonglongrightarrow> L\<close>
    apply (rule LIMSEQ_I)
    apply (simp add: norm_cq_operator.rep_eq minus_cq_operator.rep_eq Ll flip: f_def)
    using X_l_conv by fast
  then show \<open>convergent F\<close>
    using convergent_def by blast
qed

instantiation cq_operator :: (type,type) order begin
lift_definition less_eq_cq_operator :: \<open>('a, 'b) cq_operator \<Rightarrow> ('a, 'b) cq_operator \<Rightarrow> bool\<close> is
  \<open>\<lambda>a b. \<forall>x. a x \<le> b x\<close>.
definition less_cq_operator :: \<open>('a, 'b) cq_operator \<Rightarrow> ('a, 'b) cq_operator \<Rightarrow> bool\<close> where
  \<open>less_cq_operator a b \<longleftrightarrow> a \<le> b \<and> \<not> (b \<le> a)\<close>
instance
proof intro_classes
  fix x y z :: \<open>('a, 'b) cq_operator\<close>
  show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
    by (simp add: less_cq_operator_def)
  show \<open>x \<le> x\<close>
    by (simp add: less_eq_cq_operator.rep_eq)
  show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
    apply (simp add: less_eq_cq_operator.rep_eq)
    using basic_trans_rules(23) by blast
  show \<open>x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
    by (auto simp add: less_eq_cq_operator.rep_eq
        intro!: cq_operator_at_inject[THEN iffD1] ext antisym)
qed
end

definition \<open>kraus_map_id = kraus_map_of_op id_cblinfun\<close>

instantiation kraus_map :: (chilbert_space, chilbert_space) comm_monoid_add begin
lift_definition zero_kraus_map :: \<open>('a,'b) kraus_map\<close> is \<open>\<lambda>_. 0::nat\<close>
  by (simp add: kraus_equivalent_def)
lift_definition plus_kraus_map :: \<open>('a,'b) kraus_map \<Rightarrow> ('a,'b) kraus_map \<Rightarrow> ('a,'b) kraus_map\<close> is
  \<open>\<lambda>a b x. a x + b x\<close>
  apply (simp add: kraus_equivalent_def)
  sorry
instance
  sorry
end


datatype raw_program =
  Seq \<open>raw_program\<close> \<open>raw_program\<close>
  | Skip
  | Sample \<open>cl distr expression\<close>
  | IfThenElse \<open>bool expression\<close> \<open>raw_program\<close> \<open>raw_program\<close>
  | While \<open>bool expression\<close> \<open>raw_program\<close>
  | QuantumOp \<open>(qu ell2, qu ell2) kraus_map expression\<close>
  | Measurement \<open>(cl, qu) measurement expression\<close>
  | InstantiateOracles \<open>raw_program\<close> \<open>raw_program list\<close>
  | LocalQ \<open>qu QREGISTER\<close> \<open>(qu ell2, qu ell2) trace_class\<close> \<open>raw_program\<close>
  | LocalC \<open>cl CREGISTER\<close> \<open>cl \<Rightarrow> cl\<close> \<open>raw_program\<close>
  | OracleCall nat

fun oracle_number :: \<open>raw_program \<Rightarrow> nat\<close> where
  \<open>oracle_number (Seq c d) = max (oracle_number c) (oracle_number d)\<close>
| \<open>oracle_number Skip = 0\<close>
| \<open>oracle_number (Sample _) = 0\<close>
| \<open>oracle_number (QuantumOp _) = 0\<close>
| \<open>oracle_number (Measurement _) = 0\<close>
| \<open>oracle_number (IfThenElse e c d) = max (oracle_number c) (oracle_number d)\<close>
| \<open>oracle_number (While e c) = oracle_number c\<close>
| \<open>oracle_number (InstantiateOracles _ _) = 0\<close>
| \<open>oracle_number (LocalQ _ _ c) = oracle_number c\<close>
| \<open>oracle_number (LocalC _ _ c) = oracle_number c\<close>
| \<open>oracle_number (OracleCall i) = Suc i\<close>


inductive valid_oracle_program :: \<open>raw_program \<Rightarrow> bool\<close> and valid_program :: \<open>raw_program \<Rightarrow> bool\<close> where
  \<open>valid_oracle_program c \<Longrightarrow> valid_oracle_program d \<Longrightarrow> valid_oracle_program (Seq c d)\<close>
| \<open>valid_oracle_program Skip\<close>
| \<open>(\<And>m. weight (e m) \<le> 1) \<Longrightarrow> valid_oracle_program (Sample e)\<close>
| \<open>valid_oracle_program c \<Longrightarrow> valid_oracle_program d \<Longrightarrow> valid_oracle_program (IfThenElse e c d)\<close>
| \<open>valid_oracle_program c \<Longrightarrow> valid_oracle_program (While e c)\<close>
| \<open>(\<And>m. kraus_map_norm (e m) \<le> 1) \<Longrightarrow> valid_oracle_program (QuantumOp e)\<close>
| \<open>valid_oracle_program (Measurement e)\<close>
| \<open>(\<And>d. d \<in> set ds \<Longrightarrow> valid_program d) \<Longrightarrow> valid_oracle_program c \<Longrightarrow> 
  oracle_number c \<le> length ds \<Longrightarrow> valid_oracle_program (InstantiateOracles c ds)\<close>
| \<open>valid_oracle_program c \<Longrightarrow> ACTUAL_QREGISTER q \<Longrightarrow> norm \<rho> = 1 \<Longrightarrow> from_trace_class \<rho> \<in> Rep_QREGISTER q \<Longrightarrow> valid_oracle_program (LocalQ q \<rho> c)\<close>
| \<open>valid_oracle_program c \<Longrightarrow> Some o f \<in> Rep_CREGISTER x \<Longrightarrow> 
    (\<And>g. Some o g \<in> Rep_CREGISTER x \<Longrightarrow> f o g = f) \<Longrightarrow> valid_oracle_program (LocalC x f c)\<close>
| \<open>valid_oracle_program c \<Longrightarrow> oracle_number c = 0 \<Longrightarrow> valid_program c\<close>


typedef program = \<open>Collect valid_program\<close>
  apply (rule exI[of _ Skip])
  by (simp add: valid_oracle_program_valid_program.intros)
setup_lifting type_definition_program

typedef oracle_program = \<open>Collect valid_oracle_program\<close>
  apply (rule exI[of _ Skip])
  by (simp add: valid_oracle_program_valid_program.intros)
setup_lifting type_definition_oracle_program

lift_definition oracle_program_from_program :: \<open>program \<Rightarrow> oracle_program\<close> is id
  by (simp add: valid_program.simps)

lift_definition block :: \<open>program list \<Rightarrow> program\<close> is
  \<open>\<lambda>ps. fold Seq ps Skip\<close>
proof -
  fix ps
  assume \<open>list_all (\<lambda>x. x \<in> Collect valid_program) ps\<close>
  then have \<open>list_all valid_program ps\<close>
    by simp
  then have \<open>valid_oracle_program (fold Seq ps Skip)\<close> and \<open>oracle_number (fold Seq ps Skip) = 0\<close>
  proof (induction ps rule:rev_induct)
    case Nil
    show \<open>valid_oracle_program (fold Seq [] Skip)\<close>
      by (auto intro!: valid_oracle_program_valid_program.intros)
    show \<open>oracle_number (fold Seq [] Skip) = 0\<close>
      by simp
  next
    case (snoc p ps)
    then show \<open>valid_oracle_program (fold Seq (ps @ [p]) Skip)\<close>
      if \<open>list_all valid_program (ps @ [p])\<close>
      using that apply (auto intro!: valid_oracle_program_valid_program.intros)
      using valid_program.simps by blast
    show \<open>oracle_number (fold Seq (ps @ [p]) Skip) = 0\<close>
      if \<open>list_all valid_program (ps @ [p])\<close>
      using that snoc apply simp
      using valid_program.simps by blast
  qed
  then show \<open>fold Seq ps Skip \<in> Collect valid_program\<close>
    by (simp add: valid_program.simps)
qed

lift_definition sample :: \<open>'a cvariable \<Rightarrow> 'a distr expression \<Rightarrow> program\<close> is
  \<open>\<lambda>X e. Sample (\<lambda>m::cl. map_distr (\<lambda>x. setter X x m) (e m))\<close>
  by (simp add: valid_oracle_program_valid_program.intros(3) valid_program.simps)

definition assign :: \<open>'a cvariable \<Rightarrow> 'a expression \<Rightarrow> program\<close> where
  \<open>assign x e = sample x (point_distr o e)\<close>

lift_definition qapply :: \<open>'a qvariable \<Rightarrow> ('a,'a) l2bounded expression \<Rightarrow> program\<close> is
  \<open>\<lambda>Q e. if qregister Q then
      QuantumOp (\<lambda>m. kraus_map_of_op (apply_qregister Q (if norm (e m) \<le> 1 then e m else 0))) else Skip\<close>
  apply (auto intro!: valid_oracle_program_valid_program.intros)
  by (simp add: power_le_one)

consts
  ifthenelse :: "bool expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> program"
  while :: "bool expression \<Rightarrow> program list \<Rightarrow> program"
  qinit :: "'a qvariable \<Rightarrow> 'a ell2 expression \<Rightarrow> program"
  measurement :: "'a cvariable \<Rightarrow> 'b qvariable \<Rightarrow> ('a,'b) measurement expression \<Rightarrow> program"
  instantiateOracles :: "oracle_program \<Rightarrow> program list \<Rightarrow> program"
  localvars :: "'a cvariable \<Rightarrow> 'b qvariable \<Rightarrow> program list \<Rightarrow> program"

consts fvq_program :: "program \<Rightarrow> QVARIABLE"
consts fvc_program :: "program \<Rightarrow> CVARIABLE"
consts fvcw_program :: "program \<Rightarrow> CVARIABLE"
consts fvq_oracle_program :: "oracle_program \<Rightarrow> QVARIABLE"
consts fvc_oracle_program :: "oracle_program \<Rightarrow> CVARIABLE"
consts fvcw_oracle_program :: "oracle_program \<Rightarrow> CVARIABLE"

(* consts fvq_program :: "program \<Rightarrow> string set" *)
lemma fvq_program_sequence: "fvq_program (block b) = fold (\<lambda>p v. QREGISTER_pair (fvq_program p) v) b QREGISTER_unit"
  sorry
lemma fvq_program_assign: "fvq_program (assign x e) = QREGISTER_unit"
  sorry
lemma fvq_program_sample: "fvq_program (sample xs e2) = QREGISTER_unit"
  sorry
lemma fvq_program_ifthenelse: "fvq_program (ifthenelse c p1 p2) =
  QREGISTER_pair (fvq_program (block p1)) (fvq_program (block p2))"
  sorry
lemma fvq_program_while: "fvq_program (while c b) = (fvq_program (block b))"
  sorry
lemma fvq_program_qinit: "fvq_program (qinit Q e3) = QREGISTER_of Q"
  sorry
lemma fvq_program_qapply: "fvq_program (qapply Q e4) = QREGISTER_of Q"
  sorry
lemma fvq_program_measurement: "fvq_program (measurement x R e5) = QREGISTER_of R"
  sorry

lemma fvc_program_sequence: "fvc_program (block b) = fold (\<lambda>p v. CREGISTER_pair (fvc_program p) v) b CREGISTER_unit"
  sorry
lemma fvc_program_assign: "fvc_program (assign x e) = CREGISTER_pair (CREGISTER_of x) (fv_expression e)"
  sorry
lemma fvc_program_sample: "fvc_program (sample x e) = CREGISTER_pair (CREGISTER_of x) (fv_expression e)"
  sorry
lemma fvc_program_ifthenelse: "fvc_program (ifthenelse c p1 p2) =
  CREGISTER_pair (fv_expression c) (CREGISTER_pair (fvc_program (block p1)) (fvc_program (block p2)))"
  sorry
lemma fvc_program_while: "fvc_program (while c b) = 
  CREGISTER_pair (fv_expression c) (fvc_program (block b))"
  sorry
lemma fvc_program_qinit: "fvc_program (qinit Q e3) = fv_expression e3"
  sorry
lemma fvc_program_qapply: "fvc_program (qapply Q e4) = fv_expression e4"
  sorry
lemma fvc_program_measurement: "fvc_program (measurement x R e) = CREGISTER_pair (CREGISTER_of x) (fv_expression e)"
  sorry

lemma fvcw_program_sequence: "fvcw_program (block b) = fold (\<lambda>p v. CREGISTER_pair (fvcw_program p) v) b CREGISTER_unit"
  sorry
lemma fvcw_program_assign: "fvcw_program (assign x e) = CREGISTER_of x"
  sorry
lemma fvcw_program_sample: "fvcw_program (sample x e2) = CREGISTER_of x"
  sorry
lemma fvcw_program_ifthenelse: "fvcw_program (ifthenelse c p1 p2) =
  CREGISTER_pair (fvc_program (block p1)) (fvc_program (block p2))"
  sorry
lemma fvcw_program_while: "fvcw_program (while c b) = fvcw_program (block b)"
  sorry
lemma fvcw_program_qinit: "fvcw_program (qinit Q e3) = CREGISTER_unit"
  sorry
lemma fvcw_program_qapply: "fvcw_program (qapply Q e4) = CREGISTER_unit"
  sorry
lemma fvcw_program_measurement: "fvcw_program (measurement x R e5) = CREGISTER_of x"
  sorry

lemma localvars_empty: "localvars empty_cregister empty_qregister P = block P"
  sorry

lemma singleton_block: "block [P] = P"
  sorry

type_synonym program_state = \<open>(cl,qu) cq_operator\<close>

fun denotation_raw :: "raw_program \<Rightarrow> program_state \<Rightarrow> program_state" where
  denotation_raw_Skip: \<open>denotation_raw Skip \<rho> = \<rho>\<close>
| denotation_raw_Seq: \<open>denotation_raw (Seq c d) \<rho> = denotation_raw d (denotation_raw c \<rho>)\<close>
(* TODO missing cases *)

lift_definition denotation :: "program \<Rightarrow> program_state \<Rightarrow> program_state" is denotation_raw.

lift_definition program_state_distrib :: "program_state \<Rightarrow> cl distr" is
  \<open>\<lambda>\<rho> m. if \<rho> \<ge> 0 \<and> norm \<rho> \<le> 1 then norm (cq_operator_at \<rho> m) else 0\<close>
proof -
  fix \<rho> :: \<open>(cl, qu) cq_operator\<close>
  show \<open>is_distribution
        (\<lambda>m. if 0 \<le> \<rho> \<and> norm \<rho> \<le> 1 then norm (cq_operator_at \<rho> m) else 0)\<close>
  proof (cases \<open>0 \<le> \<rho> \<and> norm \<rho> \<le> 1\<close>)
    case True
    then show ?thesis
      apply (subst if_P)
      using cq_operator_at
      by (auto simp add: is_distribution_def norm_cq_operator.rep_eq)
  next
    case False
    then show ?thesis
      apply (subst if_not_P)
      by (auto simp add: is_distribution_def)
  qed
qed

lemma denotation_block: "denotation (block ps) = foldr denotation ps"
  apply transfer
  subgoal for ps
    apply (induction ps rule:rev_induct)
    by (auto intro!: ext)
  done

definition probability :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" where
  "probability e p \<rho> = Prob (program_state_distrib (denotation p \<rho>)) (Collect e)"

(* consts "probability_syntax" :: "bool \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" ("Pr[_ : (_'(_'))]")
translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability (Expr[a]) b c"
hide_const probability_syntax *)

lemma probability_sample: 
  "probability (expression m f) (block [sample m (const_expression D)]) rho
  = Prob D (Collect f)"
  sorry

lemma equal_until_bad: 
  assumes "probability (map_expression2 (|) e b) g3 rho \<ge> probability b g4 rho"
  assumes "probability (map_expression2 (\<lambda>e b. \<not>e&b) e b) g3 rho \<le> probability b g4 rho"
  shows "abs (probability b g3 rho - probability b g4 rho) \<le> probability e g3 rho"
proof -
  define d3 d4 B E where "d3 = program_state_distrib (Programs.denotation g3 rho)"
    and "d4 = program_state_distrib (Programs.denotation g4 rho)"
    and "B = Collect (expression_eval b)"
    and "E = Collect (expression_eval e)"
  note defs = this

  have EorB: "B\<union>E = Collect (expression_eval (map_expression2 (|) e b))"
    unfolding defs by auto
  have EandB: "B-E = Collect (expression_eval (map_expression2 (\<lambda>e b. \<not>e&b) e b))"
    unfolding defs by auto

  from assms(1) have a1: "Prob d4 B \<le> Prob d3 (B\<union>E)"
    unfolding EorB unfolding defs probability_def by auto
  from assms(2) have a2: "Prob d3 (B-E) \<le> Prob d4 B"
    unfolding EandB unfolding defs probability_def by auto

  have "Prob d3 B \<le> Prob d3 (B-E) + Prob d3 E"
    apply (subst Prob_setdiff) by simp
  also have "\<dots> \<le> Prob d4 B + Prob d3 E"
    using a2 by linarith
  finally have bound1: "Prob d3 B - Prob d4 B \<le> Prob d3 E"
    by linarith

  have "Prob d4 B \<le> Prob d3 (B\<union>E)"
    using a1 by assumption
  also have "\<dots> \<le> Prob d3 B + Prob d3 E"
    unfolding Prob_union by simp
  finally have bound2: "Prob d4 B - Prob d3 B \<le> Prob d3 E"
    by linarith

  from bound1 bound2 have "\<bar>Prob d3 B - Prob d4 B\<bar> \<le> Prob d3 E"
    by linarith

  then show ?thesis
    unfolding probability_def defs by simp
qed

named_theorems program_bodies
named_theorems program_fv


ML_file "programs.ML"

consts "probability_syntax" :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" ("Pr[_:(_'(_'))]")
translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability (Expr[a]) b c"
(* translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability a b c" *)
hide_const probability_syntax

end
