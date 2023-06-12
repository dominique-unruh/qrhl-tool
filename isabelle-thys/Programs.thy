theory Programs
  imports QRHL_Core Expressions Wlog.Wlog
begin

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

type_synonym ('a,'b) kraus_family = \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> nat\<close>

definition \<open>kraus_family \<EE> \<longleftrightarrow> (\<exists>B. \<forall>F. finite F \<longrightarrow> norm (\<Sum>E\<in>F. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> B)\<close>
  for \<EE> :: \<open>(_::chilbert_space, _::chilbert_space) kraus_family\<close>
definition \<open>krause_norm \<EE> = (SUP F\<in>Collect finite. norm (\<Sum>E\<in>F. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)))\<close>

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
  \<open>kraus_family_of_op E F = (if E=F then 1 else 0)\<close>

lemma kraus_family_kraus_family_of_op[simp]: \<open>kraus_family (kraus_family_of_op E)\<close>
proof -
  have \<open>(\<Sum>F\<in>M. kraus_family_of_op E F *\<^sub>C (F* o\<^sub>C\<^sub>L F)) = (if E\<in>M then E* o\<^sub>C\<^sub>L E else 0)\<close> if \<open>finite M\<close> for M
    apply (subst sum_single[where i=E])
    using that by (auto simp: kraus_family_of_op_def)
  then show ?thesis
    by (auto simp add: kraus_family_def)
qed

lift_definition kraus_map_of_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> ('a,'b) kraus_map\<close>
  is kraus_family_of_op
  by (simp add: kraus_equivalent_def)

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

(* Strengthening of Nat.of_nat_0_le_iff: wider type. *)
lemma of_nat_0_le_iff: \<open>of_nat x \<ge> (0::_::{ordered_ab_semigroup_add,zero_less_one})\<close>
  apply (induction x)
   apply auto
  by (metis add_mono semiring_norm(50) zero_less_one_class.zero_le_one)

lemma sandwich_mono: \<open>sandwich A B \<le> sandwich A C\<close> if \<open>B \<le> C\<close>
  by (metis cblinfun.real.diff_right diff_ge_0_iff_ge sandwich_pos that)

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
  shows \<open>(\<lambda>E. of_nat (\<EE> E) *\<^sub>C Abs_trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E*)) summable_on UNIV\<close>
  apply (rule abs_summable_summable)
  using assms by (rule kraus_family_map_abs_summable)

lemma kraus_family_comp_apply:
  assumes \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) = kraus_family_map \<EE> \<circ> kraus_family_map \<FF>\<close>
  sorry

lift_definition kraus_map_comp :: \<open>('a::chilbert_space,'b::chilbert_space) kraus_map
                                \<Rightarrow> ('c::chilbert_space,'a) kraus_map \<Rightarrow> ('c,'b) kraus_map\<close>
  is kraus_family_comp
  by (auto intro!: kraus_family_kraus_family_comp
      simp add: kraus_equivalent_def kraus_family_comp_apply)


datatype raw_program =
  Seq \<open>raw_program\<close> \<open>raw_program\<close>
  | Skip
  | Sample \<open>cl distr expression\<close>
  | IfThenElse \<open>bool expression\<close> \<open>raw_program\<close> \<open>raw_program\<close>
  | While \<open>bool expression\<close> \<open>raw_program\<close>
  | QuantumOp \<open>(qu ell2, qu ell2) kraus_map expression\<close>
  | Measurement \<open>(cl, qu) measurement expression\<close>
  | InstantiateOracles \<open>raw_program\<close> \<open>raw_program list\<close>
(* TODO: Localvars *)
  
axiomatization valid_program :: \<open>raw_program \<Rightarrow> bool\<close>
axiomatization valid_oracle_program :: \<open>raw_program \<Rightarrow> bool\<close>

typedef program = \<open>Collect valid_program\<close>
  sorry
setup_lifting type_definition_program

typedef oracle_program = \<open>Collect valid_oracle_program\<close>
  sorry
setup_lifting type_definition_oracle_program

lift_definition oracle_program_from_program :: \<open>program \<Rightarrow> oracle_program\<close> is id
  sorry

lift_definition block :: \<open>program list \<Rightarrow> program\<close> is
  \<open>\<lambda>ps. fold Seq ps Skip\<close>
  sorry

lift_definition sample :: \<open>'a cvariable \<Rightarrow> 'a distr expression \<Rightarrow> program\<close> is
  \<open>\<lambda>X e. Sample (\<lambda>m::cl. map_distr (\<lambda>x. setter X x m) (e m))\<close>
  sorry

definition assign :: \<open>'a cvariable \<Rightarrow> 'a expression \<Rightarrow> program\<close> where
  \<open>assign x e = sample x (point_distr o e)\<close>

lift_definition qapply :: \<open>'a qvariable \<Rightarrow> ('a,'a) l2bounded expression \<Rightarrow> program\<close> is
  \<open>\<lambda>Q e. QuantumOp (\<lambda>m. kraus_map_of_op (apply_qregister Q (e m)))\<close>
  sorry

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

type_synonym program_state = \<open>(cl,qu) cq_operator\<close>

axiomatization
  denotation :: "program \<Rightarrow> program_state \<Rightarrow> program_state"

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

lemma denotation_block: "denotation (block ps) = fold denotation ps"
  sorry

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
