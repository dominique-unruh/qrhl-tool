theory Missing2
  imports Complex_Bounded_Operators.Cblinfun_Code
    Tensor_Product.Weak_Operator_Topology
    Tensor_Product.Trace_Class
    Tensor_Product.Hilbert_Space_Tensor_Product
begin

unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)
unbundle jnf_notation
hide_const (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Order.top
hide_const (open) Coset.kernel
hide_fact (open) Infinite_Set_Sum.abs_summable_on_comparison_test

lemma has_sum_in_finite:
  assumes "finite F"
  assumes \<open>sum f F \<in> topspace T\<close>
  shows "has_sum_in T f F (sum f F)"
  using assms
  by (simp add: finite_subsets_at_top_finite has_sum_in_def limitin_def eventually_principal)

lemma tendsto_le_complex:
  fixes x y :: complex
  assumes F: "\<not> trivial_limit F"
    and x: "(f \<longlongrightarrow> x) F"
    and y: "(g \<longlongrightarrow> y) F"
    and ev: "eventually (\<lambda>x. g x \<le> f x) F"
  shows "y \<le> x"
proof (rule less_eq_complexI)
  note F
  moreover have \<open>((\<lambda>x. Re (f x)) \<longlongrightarrow> Re x) F\<close>
    by (simp add: assms tendsto_Re)
  moreover have \<open>((\<lambda>x. Re (g x)) \<longlongrightarrow> Re y) F\<close>
    by (simp add: assms tendsto_Re)
  moreover from ev have "eventually (\<lambda>x. Re (g x) \<le> Re (f x)) F"
    apply (rule eventually_mono)
    by (simp add: less_eq_complex_def)
  ultimately show \<open>Re y \<le> Re x\<close>
    by (rule tendsto_le)
next
  note F
  moreover have \<open>((\<lambda>x. Im (g x)) \<longlongrightarrow> Im y) F\<close>
    by (simp add: assms tendsto_Im)
  moreover 
  have \<open>((\<lambda>x. Im (g x)) \<longlongrightarrow> Im x) F\<close>
  proof -
    have \<open>((\<lambda>x. Im (f x)) \<longlongrightarrow> Im x) F\<close>
      by (simp add: assms tendsto_Im)
    moreover from ev have \<open>\<forall>\<^sub>F x in F. Im (f x) = Im (g x)\<close>
      apply (rule eventually_mono)
      by (simp add: less_eq_complex_def)
    ultimately show ?thesis
      by (rule Lim_transform_eventually)
  qed
  ultimately show \<open>Im y = Im x\<close>
    by (rule tendsto_unique)
qed


lemma infsum_wot_is_Sup:
  fixes f :: \<open>'b \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space)\<close>
  (* assumes bounded: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> X \<Longrightarrow> sum f F \<le> B\<close> *)
  assumes summable: \<open>summable_on_in cweak_operator_topology f X\<close>
    \<comment> \<open>See also @{thm [source] summable_wot_boundedI} for proving this.\<close>
  assumes pos: \<open>\<And>x. x \<in> X \<Longrightarrow> f x \<ge> 0\<close>
  defines \<open>S \<equiv> infsum_in cweak_operator_topology f X\<close>
  shows \<open>is_Sup ((\<lambda>F. \<Sum>x\<in>F. f x) ` {F. finite F \<and> F \<subseteq> X}) S\<close>
proof (rule is_SupI)
  have has_sum: \<open>has_sum_in cweak_operator_topology f X S\<close>
    unfolding S_def
    apply (rule has_sum_in_infsum_in)
    using assms by auto
  show \<open>s \<le> S\<close> if \<open>s \<in> ((\<lambda>F. \<Sum>x\<in>F. f x) ` {F. finite F \<and> F \<subseteq> X})\<close> for s
  proof -
    from that obtain F where [simp]: \<open>finite F\<close> and \<open>F \<subseteq> X\<close> and s_def: \<open>s = (\<Sum>x\<in>F. f x)\<close>
      by auto
    show ?thesis
    proof (rule has_sum_mono_neutral_wot)
      show \<open>has_sum_in cweak_operator_topology f F s\<close>
        by (auto intro!: has_sum_in_finite simp: s_def)
      show \<open>has_sum_in cweak_operator_topology f X S\<close>
        by (fact has_sum)
      show \<open>f x \<le> f x\<close> for x
        by simp
      show \<open>f x \<le> 0\<close> if \<open>x \<in> F - X\<close> for x
        using \<open>F \<subseteq> X\<close> that by auto
      show \<open>f x \<ge> 0\<close> if \<open>x \<in> X - F\<close> for x
        using that pos by auto
    qed
  qed
  show \<open>S \<le> y\<close>
    if y_bound: \<open>\<And>x. x \<in> ((\<lambda>F. \<Sum>x\<in>F. f x) ` {F. finite F \<and> F \<subseteq> X}) \<Longrightarrow> x \<le> y\<close> for y
  proof (rule cblinfun_leI, rename_tac \<psi>)
    fix \<psi> :: 'a
    define g where \<open>g x = \<psi> \<bullet>\<^sub>C Rep_cblinfun_wot x \<psi>\<close> for x
    from has_sum have lim: \<open>((\<lambda>i. \<psi> \<bullet>\<^sub>C ((\<Sum>x\<in>i. f x) *\<^sub>V \<psi>)) \<longlongrightarrow> \<psi> \<bullet>\<^sub>C (S *\<^sub>V \<psi>)) (finite_subsets_at_top X)\<close>
      by (simp add: has_sum_in_def limitin_cweak_operator_topology)
    have bound: \<open>\<psi> \<bullet>\<^sub>C (\<Sum>x\<in>F. f x) \<psi> \<le> \<psi> \<bullet>\<^sub>C y \<psi>\<close> if \<open>finite F\<close> \<open>F \<subseteq> X\<close> for F
      using y_bound less_eq_cblinfun_def that(1) that(2) by fastforce
    show \<open>\<psi> \<bullet>\<^sub>C (S *\<^sub>V \<psi>) \<le> \<psi> \<bullet>\<^sub>C y \<psi>\<close>
      using finite_subsets_at_top_neq_bot tendsto_const lim apply (rule tendsto_le_complex)
      using bound by (auto intro!: eventually_finite_subsets_at_top_weakI)
  qed
qed

lemma pos_imp_selfadjoint: \<open>a \<ge> 0 \<Longrightarrow> selfadjoint a\<close>
  using positive_hermitianI selfadjoint_def by blast

lemma bdd_above_mono2:
  assumes \<open>bdd_above (g ` B)\<close>
  assumes \<open>A \<subseteq> B\<close>
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows \<open>bdd_above (f ` A)\<close>
  by (smt (verit, del_insts) Set.basic_monos(7) assms(1) assms(2) assms(3) basic_trans_rules(23) bdd_above.I2 bdd_above.unfold imageI)

lemma infsum_in_finite:
  assumes "finite F"
  assumes \<open>Hausdorff_space T\<close>
  assumes \<open>sum f F \<in> topspace T\<close>
  shows "infsum_in T f F = sum f F"
  using has_sum_in_finite[OF assms(1,3)]
  using assms(2) has_sum_in_infsum_in has_sum_in_unique summable_on_in_def by blast

lemma sandwich_tc_scaleC_right: \<open>sandwich_tc e (c *\<^sub>C t) = c *\<^sub>C sandwich_tc e t\<close>
  apply (transfer fixing: e c)
  by (simp add: cblinfun.scaleC_right)



lemma sandwich_tc_plus: \<open>sandwich_tc e (t + u) = sandwich_tc e t + sandwich_tc e u\<close>
  by (simp add: sandwich_tc_def compose_tcr.add_right compose_tcl.add_left)

lemma sandwich_tc_minus: \<open>sandwich_tc e (t - u) = sandwich_tc e t - sandwich_tc e u\<close>
  by (simp add: sandwich_tc_def compose_tcr.diff_right compose_tcl.diff_left)

lemma sandwich_tc_uminus_right: \<open>sandwich_tc e (- t) = - sandwich_tc e t\<close>
  by (metis (no_types, lifting) add.right_inverse arith_simps(50) diff_0 group_cancel.sub1 sandwich_tc_minus)


lemma abs_summable_norm:
  assumes \<open>f abs_summable_on A\<close>
  shows \<open>(\<lambda>x. norm (f x)) abs_summable_on A\<close>
  using assms by simp

lemma abs_summable_on_add:
  assumes \<open>f abs_summable_on A\<close> and \<open>g abs_summable_on A\<close>
  shows \<open>(\<lambda>x. f x + g x) abs_summable_on A\<close>
proof -
  from assms have \<open>(\<lambda>x. norm (f x) + norm (g x)) summable_on A\<close>
    using summable_on_add by blast
  then show ?thesis
    apply (rule Infinite_Sum.abs_summable_on_comparison_test')
    using norm_triangle_ineq by blast
qed

lemma trace_comp_pos:
  fixes a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>trace_class b\<close>
  assumes \<open>a \<ge> 0\<close> and \<open>b \<ge> 0\<close>
  shows \<open>trace (a o\<^sub>C\<^sub>L b) \<ge> 0\<close>
proof -
  obtain c :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>a = c* o\<^sub>C\<^sub>L c\<close>
  by (metis assms(2) positive_hermitianI sqrt_op_pos sqrt_op_square)
  then have \<open>trace (a o\<^sub>C\<^sub>L b) = trace (sandwich c b)\<close>
    by (simp add: sandwich_apply assms(1) cblinfun_assoc_left(1) circularity_of_trace trace_class_comp_right)
  also have \<open>\<dots> \<ge> 0\<close>
    by (auto intro!: trace_pos sandwich_pos assms)
  finally show ?thesis
    by -
qed

lemma bdd_above_transform_mono_pos:
  assumes bdd: \<open>bdd_above ((\<lambda>x. g x) ` M)\<close>
  assumes gpos: \<open>\<And>x. x \<in> M \<Longrightarrow> g x \<ge> 0\<close>
  assumes mono: \<open>mono_on (Collect ((\<le>) 0)) f\<close>
  shows \<open>bdd_above ((\<lambda>x. f (g x)) ` M)\<close>
proof (cases \<open>M = {}\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  from bdd obtain B where B: \<open>g x \<le> B\<close> if \<open>x \<in> M\<close> for x
  by (meson bdd_above.unfold imageI)
  with gpos False have \<open>B \<ge> 0\<close>
    using dual_order.trans by blast
  have \<open>f (g x) \<le> f B\<close> if \<open>x \<in> M\<close> for x
    using mono _ _ B
    apply (rule mono_onD)
    by (auto intro!: gpos that  \<open>B \<ge> 0\<close>)
  then show ?thesis
    by fast
qed

lemma has_sum_in_cweak_operator_topology_pointwise:
  \<open>has_sum_in cweak_operator_topology f X s \<longleftrightarrow> (\<forall>\<psi> \<phi>. ((\<lambda>x. \<psi> \<bullet>\<^sub>C f x \<phi>) has_sum \<psi> \<bullet>\<^sub>C s \<phi>) X)\<close>
  by (simp add: has_sum_in_def has_sum_def limitin_cweak_operator_topology
      cblinfun.sum_left cinner_sum_right)

lemma Ex_iffI:
  assumes \<open>\<And>x. P x \<Longrightarrow> Q (f x)\<close>
  assumes \<open>\<And>x. Q x \<Longrightarrow> P (g x)\<close>
  shows \<open>Ex P \<longleftrightarrow> Ex Q\<close>
  using assms(1) assms(2) by auto

lemma summable_wot_bdd_above:
  fixes f :: \<open>'b \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space)\<close>
  assumes summable: \<open>summable_on_in cweak_operator_topology f X\<close>
    \<comment> \<open>See also @{thm [source] summable_wot_boundedI} for proving this.\<close>
  assumes pos: \<open>\<And>x. x \<in> X \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>bdd_above (sum f ` {F. finite F \<and> F \<subseteq> X})\<close>
  using infsum_wot_is_Sup[OF assms]
  by (auto intro!: simp: is_Sup_def bdd_above_def)

lemma is_Proj_leq_id: \<open>is_Proj P \<Longrightarrow> P \<le> id_cblinfun\<close>
  by (metis diff_ge_0_iff_ge is_Proj_algebraic is_Proj_complement positive_cblinfun_squareI)

lemma sum_butterfly_leq_id: 
  assumes \<open>is_ortho_set E\<close>
  assumes \<open>\<And>e. e\<in>E \<Longrightarrow> norm e = 1\<close>
  shows \<open>(\<Sum>i\<in>E. butterfly i i) \<le> id_cblinfun\<close>
proof -
  have \<open>is_Proj (\<Sum>\<psi>\<in>E. butterfly \<psi> \<psi>)\<close>
    using assms by (rule sum_butterfly_is_Proj)
  then show ?thesis
    by (auto intro!: is_Proj_leq_id)
qed

lemma abs_op_one_dim: \<open>abs_op x = one_dim_iso (abs (one_dim_iso x :: complex))\<close>
  by (metis (mono_tags, lifting) abs_opI abs_op_scaleC of_complex_def one_cblinfun_adj one_comp_one_cblinfun one_dim_iso_is_of_complex one_dim_iso_of_one one_dim_iso_of_zero one_dim_loewner_order one_dim_scaleC_1 zero_less_one_class.zero_le_one)


lemma trace_norm_one_dim: \<open>trace_norm x = cmod (one_dim_iso x)\<close>
  apply (rule of_real_hom.injectivity[where 'a=complex])
  apply (simp add: abs_op_one_dim flip: trace_abs_op)
  by (simp add: abs_complex_def)



instantiation trace_class :: (one_dim, one_dim) complex_inner begin
lift_definition cinner_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> complex\<close> is \<open>(\<bullet>\<^sub>C)\<close>.
instance
proof intro_classes
  fix x y z :: \<open>('a, 'b) trace_class\<close>
  show \<open>x \<bullet>\<^sub>C y = cnj (y \<bullet>\<^sub>C x)\<close>
    apply transfer'
    by simp
  show \<open>(x + y) \<bullet>\<^sub>C z = x \<bullet>\<^sub>C z + y \<bullet>\<^sub>C z\<close>
    apply transfer'
    by (simp add: cinner_simps)
  show \<open>r *\<^sub>C x \<bullet>\<^sub>C y = cnj r * (x \<bullet>\<^sub>C y)\<close> for r
    apply (transfer' fixing: r)
    using cinner_simps by blast
  show \<open>0 \<le> x \<bullet>\<^sub>C x\<close>
    apply transfer'
    by simp
  show \<open>(x \<bullet>\<^sub>C x = 0) = (x = 0)\<close>
    apply transfer'
    by auto
  show \<open>norm x = sqrt (cmod (x \<bullet>\<^sub>C x))\<close>
  proof transfer'
    fix x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    define c :: complex where \<open>c = one_dim_iso x\<close>
    then have xc: \<open>x = c *\<^sub>C 1\<close>
      by simp
    have \<open>trace_norm x = norm c\<close>
      by (simp add: trace_norm_one_dim xc)
    also have \<open>norm c = sqrt (cmod (x \<bullet>\<^sub>C x))\<close>
      by (metis inner_real_def norm_eq_sqrt_cinner norm_one norm_scaleC real_inner_1_right xc)
    finally show \<open>trace_norm x = sqrt (cmod (x \<bullet>\<^sub>C x)) \<close>
      by (simp add: cinner_cblinfun_def)
  qed
qed
end


instantiation trace_class :: (one_dim, one_dim) one_dim begin
lift_definition one_trace_class :: \<open>('a, 'b) trace_class\<close> is 1
  by auto
lift_definition times_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class\<close> is \<open>(*)\<close>
  by auto
lift_definition divide_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class\<close> is \<open>(/)\<close>
  by auto
lift_definition inverse_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class\<close> is \<open>Fields.inverse\<close>
  by auto
definition canonical_basis_trace_class :: \<open>('a, 'b) trace_class list\<close> where \<open>canonical_basis_trace_class = [1]\<close>
definition canonical_basis_length_trace_class :: \<open>('a, 'b) trace_class itself \<Rightarrow> nat\<close> where \<open>canonical_basis_length_trace_class = 1\<close>
instance
proof intro_classes
  fix x y z :: \<open>('a, 'b) trace_class\<close>
  have [simp]: \<open>1 \<noteq> (0 :: ('a, 'b) trace_class)\<close>
    using one_trace_class.rep_eq by force
  then have [simp]: \<open>0 \<noteq> (1 :: ('a, 'b) trace_class)\<close>
    by force
  show \<open>distinct (canonical_basis :: (_,_) trace_class list)\<close>
    by (simp add: canonical_basis_trace_class_def)
  show \<open>cindependent (set canonical_basis :: (_,_) trace_class set)\<close>
    by (simp add: canonical_basis_trace_class_def)
  show \<open>canonical_basis_length TYPE(('a, 'b) trace_class) = length (canonical_basis :: (_,_) trace_class list)\<close>
    by (simp add: canonical_basis_length_trace_class_def canonical_basis_trace_class_def)
  show \<open>x \<in> set canonical_basis \<Longrightarrow> norm x = 1\<close>
    apply (simp add: canonical_basis_trace_class_def)
    by (smt (verit, ccfv_threshold) one_trace_class_def cinner_trace_class.abs_eq cnorm_eq_1 one_cinner_one one_trace_class.rsp)
  show \<open>canonical_basis = [1 :: ('a,'b) trace_class]\<close>
    by (simp add: canonical_basis_trace_class_def)
  show \<open>a *\<^sub>C 1 * b *\<^sub>C 1 = (a * b) *\<^sub>C (1 :: ('a,'b) trace_class)\<close> for a b :: complex
    apply (transfer' fixing: a b)
    by simp
  show \<open>x div y = x * inverse y\<close>
    apply transfer'
    by (simp add: divide_cblinfun_def)
  show \<open>inverse (a *\<^sub>C 1 :: ('a,'b) trace_class) = 1 /\<^sub>C a\<close> for a :: complex
    apply transfer'
    by simp
  show \<open>is_ortho_set (set canonical_basis :: ('a,'b) trace_class set)\<close>
    by (simp add: is_ortho_set_def canonical_basis_trace_class_def)
  show \<open>cspan (set canonical_basis :: ('a,'b) trace_class set) = UNIV\<close>
  proof (intro Set.set_eqI iffI UNIV_I)
    fix x :: \<open>('a,'b) trace_class\<close>
    have \<open>\<exists>c. y = c *\<^sub>C 1\<close> for y :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      apply (rule exI[where x=\<open>one_dim_iso y\<close>])
      by simp
    then obtain c where \<open>x = c *\<^sub>C 1\<close>
      apply transfer'
      by auto
    then show \<open>x \<in> cspan (set canonical_basis)\<close>
      by (auto intro!: complex_vector.span_base complex_vector.span_clauses
          simp: canonical_basis_trace_class_def)
  qed
qed
end

lemma summable_on_in_cweak_operator_topology_pointwise:
  assumes \<open>summable_on_in cweak_operator_topology f X\<close>
  shows \<open>(\<lambda>x. a \<bullet>\<^sub>C f x b) summable_on X\<close>
  using assms
  by (auto simp: summable_on_in_def summable_on_def has_sum_in_cweak_operator_topology_pointwise)

lemma has_sum_Sigma'_banach:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::banach\<close>
  assumes "((\<lambda>(x,y). f x y) has_sum S) (Sigma A B)"
  shows \<open>((\<lambda>x. infsum (f x) (B x)) has_sum S) A\<close>
  by (metis (no_types, lifting) assms has_sum_cong has_sum_imp_summable has_sum_infsum infsumI infsum_Sigma'_banach summable_on_Sigma_banach)

lemma infsum_in_cweak_operator_topology_pointwise:
  assumes \<open>summable_on_in cweak_operator_topology f X\<close>
  shows \<open>a \<bullet>\<^sub>C (infsum_in cweak_operator_topology f X) b = (\<Sum>\<^sub>\<infinity>x\<in>X. a \<bullet>\<^sub>C f x b)\<close>
  by (metis (mono_tags, lifting) assms has_sum_in_cweak_operator_topology_pointwise has_sum_in_infsum_in hausdorff_cweak_operator_topology infsumI)

instance cblinfun_wot :: (complex_normed_vector, complex_inner) topological_ab_group_add
  by intro_classes

lemma from_trace_class_one_dim_iso[simp]: \<open>from_trace_class = one_dim_iso\<close>
proof (rule ext)
  fix x:: \<open>('a, 'b) trace_class\<close>
  have \<open>from_trace_class x = from_trace_class (one_dim_iso x *\<^sub>C 1)\<close>
    by simp
  also have \<open>\<dots> = one_dim_iso x *\<^sub>C from_trace_class 1\<close>
    using scaleC_trace_class.rep_eq by blast
  also have \<open>\<dots> = one_dim_iso x *\<^sub>C 1\<close>
    by (simp add: one_trace_class.rep_eq)
  also have \<open>\<dots> = one_dim_iso x\<close>
    by simp
  finally show \<open>from_trace_class x = one_dim_iso x\<close>
    by -
qed

lemma trace_tc_one_dim_iso[simp]: \<open>trace_tc = one_dim_iso\<close>
  by (simp add: trace_tc.rep_eq[abs_def])

lemma compose_tcr_id_left[simp]: \<open>compose_tcr id_cblinfun t = t\<close>
  by (auto intro!: from_trace_class_inject[THEN iffD1] simp: compose_tcr.rep_eq)

lemma compose_tcl_id_right[simp]: \<open>compose_tcl t id_cblinfun = t\<close>
  by (auto intro!: from_trace_class_inject[THEN iffD1] simp: compose_tcl.rep_eq)


lemma sandwich_tc_id_cblinfun[simp]: \<open>sandwich_tc id_cblinfun t = t\<close>
  by (simp add: from_trace_class_inverse sandwich_tc_def)

lemma bounded_clinear_sandwich_tc[bounded_clinear]: \<open>bounded_clinear (sandwich_tc e)\<close>
  using norm_sandwich_tc[of e]
  by (auto intro!: bounded_clinearI[where K=\<open>(norm e)\<^sup>2\<close>]
      simp: sandwich_tc_plus sandwich_tc_scaleC_right cross3_simps)

lemma clinear_of_complex[iff]: \<open>clinear of_complex\<close>
  by (simp add: clinearI)

(* definition some_onb_of :: \<open>'a ccsubspace \<Rightarrow> 'a::chilbert_space set\<close> where
  \<open>some_onb_of S = (SOME B::'a set. is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> ccspan B = S)\<close> *)

(* lemma is_ortho_set_some_onb_of[iff]: 
  fixes S :: \<open>'a::chilbert_space ccsubspace\<close>
  shows \<open>is_ortho_set (some_onb_of S)\<close> (is \<open>?thesis1\<close>)
  and some_onb_of_normed: \<open>b \<in> some_onb_of S \<Longrightarrow> norm b = 1\<close> (is \<open>PROP ?thesis2\<close>)
  and ccspan_some_onb_of[simp]: \<open>ccspan (some_onb_of S) = S\<close> (is \<open>?thesis3\<close>)
proof -
  define P where \<open>P B \<longleftrightarrow> is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> ccspan B = S\<close> for B
  from orthonormal_subspace_basis_exists[where S=\<open>{}\<close>]
  have \<open>\<exists>B. P B\<close>
    by (auto simp: P_def)
  then have \<open>P (SOME B. P B)\<close>
    by (simp add: someI_ex)
  then have \<open>P (some_onb_of S)\<close>
    by (simp add: P_def some_onb_of_def)
  then show ?thesis1 \<open>PROP ?thesis2\<close> ?thesis3
    by (simp_all add: P_def)
qed *)

lemma some_onb_of_0[simp]: \<open>some_onb_of (0 :: 'a::chilbert_space ccsubspace) = {}\<close>
proof -
  have no0: \<open>0 \<notin> some_onb_of (0 :: 'a ccsubspace)\<close>
    using some_onb_of_norm1
    by fastforce
  have \<open>ccspan (some_onb_of 0) = (0 :: 'a ccsubspace)\<close>
    by simp
  then have \<open>some_onb_of 0 \<subseteq> space_as_set (0 :: 'a ccsubspace)\<close>
    by (metis ccspan_superset)
  also have \<open>\<dots> = {0}\<close>
    by simp
  finally show ?thesis
    using no0
    by blast
qed


definition spectral_dec_vecs :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> 'a::chilbert_space set\<close> where
  \<open>spectral_dec_vecs a = (\<Union>n. scaleC (csqrt (spectral_dec_val a n)) ` some_onb_of (spectral_dec_space a n))\<close>

lift_definition spectral_dec_vecs_tc :: \<open>('a,'a) trace_class \<Rightarrow> 'a::chilbert_space set\<close> is
  spectral_dec_vecs.

lemma spectral_dec_vecs_ortho:
  assumes \<open>selfadjoint a\<close> and \<open>compact_op a\<close>
  shows \<open>is_ortho_set (spectral_dec_vecs a)\<close>
proof (unfold is_ortho_set_def, intro conjI ballI impI)
  show \<open>0 \<notin> spectral_dec_vecs a\<close>
  proof (rule notI)
    assume \<open>0 \<in> spectral_dec_vecs a\<close>
    then obtain n v where v0: \<open>0 = csqrt (spectral_dec_val a n) *\<^sub>C v\<close> and v_in: \<open>v \<in> some_onb_of (spectral_dec_space a n)\<close>
      by (auto simp: spectral_dec_vecs_def)
    from v_in have \<open>v \<noteq> 0\<close>
      using some_onb_of_norm1 by fastforce
    from v_in have \<open>spectral_dec_space a n \<noteq> 0\<close>
      using some_onb_of_0 by force
    then have \<open>spectral_dec_val a n \<noteq> 0\<close>
      by (meson spectral_dec_space.elims)
    with v0 \<open>v \<noteq> 0\<close> show False
      by force
  qed
  fix g h assume g: \<open>g \<in> spectral_dec_vecs a\<close> and h: \<open>h \<in> spectral_dec_vecs a\<close> and \<open>g \<noteq> h\<close>
  from g obtain ng g' where gg': \<open>g = csqrt (spectral_dec_val a ng) *\<^sub>C g'\<close> and g'_in: \<open>g' \<in> some_onb_of (spectral_dec_space a ng)\<close>
    by (auto simp: spectral_dec_vecs_def)
  from h obtain nh h' where hh': \<open>h = csqrt (spectral_dec_val a nh) *\<^sub>C h'\<close> and h'_in: \<open>h' \<in> some_onb_of (spectral_dec_space a nh)\<close>
    by (auto simp: spectral_dec_vecs_def)
  have \<open>is_orthogonal g' h'\<close>
  proof (cases \<open>ng = nh\<close>)
    case True
    with h'_in have \<open>h' \<in> some_onb_of (spectral_dec_space a nh)\<close>
      by simp
    with g'_in True \<open>g \<noteq> h\<close> gg' hh'
    show ?thesis
      using  is_ortho_set_def by fastforce
  next
    case False
    then have \<open>orthogonal_spaces (spectral_dec_space a ng) (spectral_dec_space a nh)\<close>
      by (auto intro!: spectral_dec_space_orthogonal assms simp: )
    with h'_in g'_in show \<open>is_orthogonal g' h'\<close>
      using orthogonal_spaces_ccspan by force
  qed
  then show \<open>is_orthogonal g h\<close>
    by (simp add: gg' hh')
qed

lemma pos_selfadjoint: \<open>selfadjoint a\<close> if \<open>a \<ge> 0\<close>
  using adj_0 comparable_hermitean selfadjoint_def that by blast

(* TODO move next to *) thm one_dim_loewner_order
lemma one_dim_loewner_order_strict: \<open>A > B \<longleftrightarrow> one_dim_iso A > (one_dim_iso B :: complex)\<close> for A B :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::{chilbert_space, one_dim}\<close>
  by (auto simp: less_cblinfun_def one_dim_loewner_order)

lemma one_dim_cblinfun_zero_le_one: \<open>0 < (1 :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  by (simp add: one_dim_loewner_order_strict)
lemma one_dim_cblinfun_one_pos: \<open>0 \<le> (1 :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  by (simp add: one_dim_loewner_order)

lemma compact_from_trace_class[iff]: \<open>compact_op (from_trace_class t)\<close>
  by (auto intro!: simp: trace_class_compact)

lemma eigenvalues_nonneg:
  assumes \<open>a \<ge> 0\<close> and \<open>v \<in> eigenvalues a\<close>
  shows \<open>v \<ge> 0\<close>
proof -
  from assms obtain h where \<open>norm h = 1\<close> and ahvh: \<open>a *\<^sub>V h = v *\<^sub>C h\<close>
    using unit_eigenvector_ex by blast
  have \<open>0 \<le> h \<bullet>\<^sub>C a h\<close>
    by (simp add: assms(1) cinner_pos_if_pos)
  also have \<open>\<dots> = v * (h \<bullet>\<^sub>C h)\<close>
    by (simp add: ahvh)
  also have \<open>\<dots> = v\<close>
    using \<open>norm h = 1\<close> cnorm_eq_1 by auto
  finally show \<open>v \<ge> 0\<close>
    by blast
qed


lemma spectral_dec_val_nonneg:
  assumes \<open>a \<ge> 0\<close>
  assumes \<open>compact_op a\<close>
  shows \<open>spectral_dec_val a n \<ge> 0\<close>
proof -
  define v where \<open>v = spectral_dec_val a n\<close>
  wlog non0: \<open>spectral_dec_val a n \<noteq> 0\<close> generalizing v keeping v_def
    using negation by force
  have [simp]: \<open>selfadjoint a\<close>
    using adj_0 assms(1) comparable_hermitean selfadjoint_def by blast
  have \<open>v \<in> eigenvalues a\<close>
    by (auto intro!: non0 spectral_dec_val_eigenvalue assms simp: v_def)
  then show \<open>spectral_dec_val a n \<ge> 0\<close>
    using assms(1) eigenvalues_nonneg v_def by blast
qed

lemma inj_scaleC:
  fixes A :: \<open>'a::complex_vector set\<close>
  assumes \<open>c \<noteq> 0\<close>
  shows \<open>inj_on (scaleC c) A\<close>
  by (meson assms inj_onI scaleC_left_imp_eq)

lemma finite_dim_ccsubspace_zero[iff]: \<open>finite_dim_ccsubspace 0\<close>
proof -
  have *: \<open>cfinite_dim (cspan {0})\<close>
    by blast
  show ?thesis
    apply transfer
    using * by simp
qed


lemma finite_dim_ccsubspace_bot[iff]: \<open>finite_dim_ccsubspace \<bottom>\<close>
  using finite_dim_ccsubspace_zero by auto


lemma spectral_dec_space_finite_dim[intro]:
  assumes \<open>compact_op a\<close>
  shows \<open>finite_dim_ccsubspace (spectral_dec_space a n)\<close>
  by (auto intro!: compact_op_eigenspace_finite_dim spectral_dec_op_compact assms simp: spectral_dec_space_def)

lemma some_onb_of_finite_dim:
  fixes S :: \<open>'a::chilbert_space ccsubspace\<close>
  assumes \<open>finite_dim_ccsubspace S\<close>
  shows \<open>finite (some_onb_of S)\<close>
proof -
  from assms obtain C where CS: \<open>cspan C = space_as_set S\<close> and \<open>finite C\<close>
    by (meson cfinite_dim_subspace_has_basis csubspace_space_as_set finite_dim_ccsubspace.rep_eq)
  then show \<open>finite (some_onb_of S)\<close>
    using ccspan_superset complex_vector.independent_span_bound is_ortho_set_cindependent by fastforce
qed

lemma some_onb_of_in_space[iff]:
  fixes S :: \<open>'a::chilbert_space ccsubspace\<close>
  shows \<open>some_onb_of S \<subseteq> space_as_set S\<close>
  using ccspan_superset by fastforce


lemma sum_some_onb_of_butterfly:
  fixes S :: \<open>'a::chilbert_space ccsubspace\<close>
  assumes \<open>finite_dim_ccsubspace S\<close>
  shows \<open>(\<Sum>x\<in>some_onb_of S. butterfly x x) = Proj S\<close>
proof -
  obtain B where onb_S_in_B: \<open>some_onb_of S \<subseteq> B\<close> and \<open>is_onb B\<close>
    apply atomize_elim
    apply (rule orthonormal_basis_exists)
    by (simp_all add: some_onb_of_norm1)
  have S_ccspan: \<open>S = ccspan (some_onb_of S)\<close>
    by simp

  show ?thesis
  proof (rule cblinfun_eq_gen_eqI[where G=B])
    show \<open>ccspan B = \<top>\<close>
      using \<open>is_onb B\<close> is_onb_def by blast
    fix b assume \<open>b \<in> B\<close>
    show \<open>(\<Sum>x\<in>some_onb_of S. selfbutter x) *\<^sub>V b = Proj S *\<^sub>V b\<close>
    proof (cases \<open>b \<in> some_onb_of S\<close>)
      case True
      have \<open>(\<Sum>x\<in>some_onb_of S. selfbutter x) *\<^sub>V b = (\<Sum>x\<in>some_onb_of S. selfbutter x *\<^sub>V b)\<close>
        using cblinfun.sum_left by blast
      also have \<open>\<dots> = b\<close>
        apply (subst sum_single[where i=b])
        using True apply (auto intro!: simp add: assms some_onb_of_finite_dim) 
        using is_ortho_set_def apply fastforce
        using cnorm_eq_1 some_onb_of_norm1 by force
      also have \<open>\<dots> = Proj S *\<^sub>V b\<close>
        apply (rule Proj_fixes_image[symmetric])
        using True some_onb_of_in_space by blast
      finally show ?thesis
        by -
    next
      case False
      have *: \<open>is_orthogonal x b\<close> if \<open>x \<in> some_onb_of S\<close> and \<open>x \<noteq> 0\<close> for x
      proof -
        have \<open>x \<in> B\<close>
          using onb_S_in_B that(1) by fastforce
        moreover note \<open>b \<in> B\<close>
        moreover have \<open>x \<noteq> b\<close>
          using False that(1) by blast
        moreover note \<open>is_onb B\<close>
        ultimately show \<open>is_orthogonal x b\<close>
          by (simp add: is_onb_def is_ortho_set_def)
      qed
      have \<open>(\<Sum>x\<in>some_onb_of S. selfbutter x) *\<^sub>V b = (\<Sum>x\<in>some_onb_of S. selfbutter x *\<^sub>V b)\<close>
        using cblinfun.sum_left by blast
      also have \<open>\<dots> = 0\<close>
        by (auto intro!: sum.neutral simp: * )
      also have \<open>\<dots> = Proj S *\<^sub>V b\<close>
        apply (rule Proj_0_compl[symmetric])
        apply (subst S_ccspan)
        apply (rule mem_ortho_ccspanI)
        using "*" cinner_zero_right is_orthogonal_sym by blast
      finally show ?thesis 
        by -
    qed
  qed
qed



lemma sum_some_onb_of_tc_butterfly:
  assumes \<open>finite_dim_ccsubspace S\<close>
  shows \<open>(\<Sum>x\<in>some_onb_of S. tc_butterfly x x) = Abs_trace_class (Proj S)\<close>
  by (metis (mono_tags, lifting) assms from_trace_class_inverse from_trace_class_sum sum.cong sum_some_onb_of_butterfly tc_butterfly.rep_eq)


lemma spectral_dec_space_0:
  assumes \<open>spectral_dec_val a n = 0\<close>
  shows \<open>spectral_dec_space a n = 0\<close>
  by (simp add: assms spectral_dec_space_def)

lemma cdim_infinite_0:
  assumes \<open>\<not> cfinite_dim S\<close>
  shows \<open>cdim S = 0\<close>
proof -
  from assms have not_fin_cspan: \<open>\<not> cfinite_dim (cspan S)\<close>
    using cfinite_dim_def cfinite_dim_subspace_has_basis complex_vector.span_superset by fastforce
  obtain B where \<open>cindependent B\<close> and \<open>cspan S = cspan B\<close>
    using csubspace_has_basis by blast
  with not_fin_cspan have \<open>infinite B\<close>
    by auto
  then have \<open>card B = 0\<close>
    by force
  have \<open>cdim (cspan S) = 0\<close> 
    apply (rule complex_vector.dim_unique[of B])
       apply (auto intro!: simp add: \<open>cspan S = cspan B\<close> complex_vector.span_superset)
    using \<open>cindependent B\<close> \<open>card B = 0\<close> by auto
  then show ?thesis
    by simp
qed


lemma some_onb_of_card:
  fixes S :: \<open>'a::chilbert_space ccsubspace\<close>
  shows \<open>card (some_onb_of S) = cdim (space_as_set S)\<close>
proof (cases \<open>finite_dim_ccsubspace S\<close>)
  case True
  show ?thesis
    apply (rule complex_vector.dim_eq_card[symmetric])
     apply (auto simp: is_ortho_set_cindependent)
     apply (metis True ccspan_finite some_onb_of_ccspan complex_vector.span_clauses(1) some_onb_of_finite_dim)
    by (metis True ccspan_finite some_onb_of_ccspan complex_vector.span_eq_iff csubspace_space_as_set some_onb_of_finite_dim)
next
  case False
  then have \<open>cdim (space_as_set S) = 0\<close>
    by (simp add: cdim_infinite_0 finite_dim_ccsubspace.rep_eq)
  moreover from False have \<open>infinite (some_onb_of S)\<close>
    using ccspan_finite_dim by fastforce
  ultimately show ?thesis 
    by simp
qed

lemma Proj_pos[iff]: \<open>Proj S \<ge> 0\<close>
  apply (rule positive_cblinfun_squareI[where B=\<open>Proj S\<close>])
  by (simp add: adj_Proj)

lemma abs_op_Proj[simp]: \<open>abs_op (Proj S) = Proj S\<close>
  by (simp add: abs_op_id_on_pos)


lemma trace_class_Proj: \<open>trace_class (Proj S) \<longleftrightarrow> finite_dim_ccsubspace S\<close>
proof -
  define C where \<open>C = some_onb_of S\<close>
  then obtain B where \<open>is_onb B\<close> and \<open>C \<subseteq> B\<close>
    using orthonormal_basis_exists some_onb_of_norm1 by blast
  have card_C: \<open>card C = cdim (space_as_set S)\<close>
    by (simp add: C_def some_onb_of_card)
  have S_C: \<open>S = ccspan C\<close>
    by (simp add: C_def)

  from \<open>is_onb B\<close>
  have \<open>trace_class (Proj S) \<longleftrightarrow> ((\<lambda>x. x \<bullet>\<^sub>C (abs_op (Proj S) *\<^sub>V x)) abs_summable_on B)\<close>
    by (rule trace_class_iff_summable)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>x. cmod (x \<bullet>\<^sub>C (Proj S *\<^sub>V x))) abs_summable_on B)\<close>
    by simp
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>x. 1::real) abs_summable_on C)\<close>
  proof (rule summable_on_cong_neutral)
    fix x :: 'a
    show \<open>norm 1 = 0\<close> if \<open>x \<in> C - B\<close>
      using that \<open>C \<subseteq> B\<close> by auto
    show \<open>norm (cmod (x \<bullet>\<^sub>C (Proj S *\<^sub>V x))) = norm (1::real)\<close> if \<open>x \<in> B \<inter> C\<close>
      apply (subst Proj_fixes_image)
      using C_def Int_absorb1 that \<open>is_onb B\<close>
      by (auto simp: is_onb_def cnorm_eq_1)
    show \<open>norm (cmod (x \<bullet>\<^sub>C (Proj S *\<^sub>V x))) = 0\<close> if \<open>x \<in> B - C\<close>
      apply (subst Proj_0_compl)
       apply (subst S_C)
       apply (rule mem_ortho_ccspanI)
      using that \<open>is_onb B\<close> \<open>C \<subseteq> B\<close>
      by (force simp: is_onb_def is_ortho_set_def)+
  qed
  also have \<open>\<dots> \<longleftrightarrow> finite C\<close>
    using infsum_diverge_constant[where A=C and c=\<open>1::real\<close>]
    by auto
  also have \<open>\<dots> \<longleftrightarrow> finite_dim_ccsubspace S\<close>
    by (metis C_def S_C ccspan_finite_dim some_onb_of_finite_dim)
  finally show ?thesis
    by -
qed

lemma not_trace_class_trace0: \<open>trace a = 0\<close> if \<open>\<not> trace_class a\<close>
  using that by (simp add: trace_def)

lemma trace_Proj: \<open>trace (Proj S) = cdim (space_as_set S)\<close>
proof (cases \<open>finite_dim_ccsubspace S\<close>)
  case True
  define C where \<open>C = some_onb_of S\<close>
  then obtain B where \<open>is_onb B\<close> and \<open>C \<subseteq> B\<close>
    using orthonormal_basis_exists some_onb_of_norm1 by blast
  have [simp]: \<open>finite C\<close>
    using C_def True some_onb_of_finite_dim by blast
  have card_C: \<open>card C = cdim (space_as_set S)\<close>
    by (simp add: C_def some_onb_of_card)
  have S_C: \<open>S = ccspan C\<close>
    by (simp add: C_def)

  from True have \<open>trace_class (Proj S)\<close>
    by (simp add: trace_class_Proj)
  with \<open>is_onb B\<close> have \<open>((\<lambda>e. e \<bullet>\<^sub>C (Proj S *\<^sub>V e)) has_sum trace (Proj S)) B\<close>
    by (rule trace_has_sum)
  then have \<open>((\<lambda>e. 1) has_sum trace (Proj S)) C\<close>
  proof (rule has_sum_cong_neutral[THEN iffD1, rotated -1])
    fix x :: 'a
    show \<open>1 = 0\<close> if \<open>x \<in> C - B\<close>
      using that \<open>C \<subseteq> B\<close> by auto
    show \<open>x \<bullet>\<^sub>C (Proj S *\<^sub>V x) = 1\<close> if \<open>x \<in> B \<inter> C\<close>
      apply (subst Proj_fixes_image)
      using C_def Int_absorb1 that \<open>is_onb B\<close>
      by (auto simp: is_onb_def cnorm_eq_1)
    show \<open>is_orthogonal x (Proj S *\<^sub>V x)\<close> if \<open>x \<in> B - C\<close>
      apply (subst Proj_0_compl)
       apply (subst S_C)
       apply (rule mem_ortho_ccspanI)
      using that \<open>is_onb B\<close> \<open>C \<subseteq> B\<close>
      by (force simp: is_onb_def is_ortho_set_def)+
  qed
  then have \<open>trace (Proj S) = card C\<close>
    using has_sum_constant[OF \<open>finite C\<close>, of 1]
    apply simp
    using has_sum_unique by blast
  also have \<open>\<dots> = cdim (space_as_set S)\<close>
    using card_C by presburger
  finally show ?thesis
    by -
next
  case False
  then have \<open>\<not> trace_class (Proj S)\<close>
    using trace_class_Proj by blast
  then have \<open>trace (Proj S) = 0\<close>
    by (rule not_trace_class_trace0)
  moreover from False have \<open>cdim (space_as_set S) = 0\<close>
    apply transfer
    by (simp add: cdim_infinite_0)
  ultimately show ?thesis
    by simp
qed



lemma butterfly_spectral_dec_vec_tc_has_sum:
  assumes \<open>t \<ge> 0\<close>
  shows \<open>((\<lambda>v. tc_butterfly v v) has_sum t) (spectral_dec_vecs_tc t)\<close>
proof -
  define t' where \<open>t' = from_trace_class t\<close>
  note power2_csqrt[unfolded power2_eq_square, simp]
  note Reals_cnj_iff[simp]
  have [simp]: \<open>compact_op t'\<close>
    by (simp add: t'_def)
  from assms have \<open>selfadjoint_tc t\<close>
    apply transfer
    apply (rule comparable_hermitean[of 0])
    by simp_all
  have spectral_real[simp]: \<open>spectral_dec_val t' n \<in> \<real>\<close> for n
    apply (rule spectral_dec_val_real)
    using \<open>selfadjoint_tc t\<close> by (auto intro!: trace_class_compact simp: selfadjoint_tc.rep_eq t'_def)

  have *: \<open>((\<lambda>(n,v). tc_butterfly v v) has_sum t) (SIGMA n:UNIV. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close>
  proof (rule has_sum_SigmaI[where g=\<open>\<lambda>n. spectral_dec_val t' n *\<^sub>C spectral_dec_proj_tc t n\<close>])
    have \<open>spectral_dec_val t' n \<ge> 0\<close> for n
      by (simp add: assms from_trace_class_pos spectral_dec_val_nonneg t'_def)
    then have [simp]: \<open>cnj (csqrt (spectral_dec_val t' n)) * csqrt (spectral_dec_val t' n) = spectral_dec_val t' n\<close> for n
      apply (auto simp add: csqrt_of_real_nonneg less_eq_complex_def)
      by (metis of_real_Re of_real_mult spectral_real sqrt_sqrt)
    have sum: \<open>(\<Sum>y\<in>(\<lambda>x. csqrt (spectral_dec_val t' n) *\<^sub>C x) ` some_onb_of (spectral_dec_space t' n). tc_butterfly y y) = spectral_dec_val t' n *\<^sub>C spectral_dec_proj_tc t n\<close> for n
    proof (cases \<open>spectral_dec_val t' n = 0\<close>)
      case True
      then show ?thesis
        by (metis (mono_tags, lifting) csqrt_0 imageE scaleC_eq_0_iff sum.neutral tc_butterfly_scaleC_left)
    next
      case False
      then have \<open>inj_on (\<lambda>x. csqrt (spectral_dec_val t' n) *\<^sub>C x) X\<close> for X :: \<open>'a set\<close>
        by (meson csqrt_eq_0 inj_scaleC)
      then show ?thesis 
        by (simp add: sum.reindex False spectral_dec_space_finite_dim sum_some_onb_of_tc_butterfly
            spectral_dec_proj_def spectral_dec_proj_tc_def flip: scaleC_sum_right t'_def)
    qed
    then show \<open>((\<lambda>y. case (n, y) of (n, v) \<Rightarrow> tc_butterfly v v) has_sum spectral_dec_val t' n *\<^sub>C spectral_dec_proj_tc t n)
          ((*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close> for n
      by (auto intro!: has_sum_finiteI finite_imageI some_onb_of_finite_dim spectral_dec_space_finite_dim simp: t'_def)
    show \<open>((\<lambda>n. spectral_dec_val t' n *\<^sub>C spectral_dec_proj_tc t n) has_sum t) UNIV\<close>
      by (auto intro!: spectral_dec_has_sum_tc \<open>selfadjoint_tc t\<close> simp: t'_def simp flip: spectral_dec_val_tc.rep_eq)
    show \<open>(\<lambda>(n, v). tc_butterfly v v) summable_on (SIGMA n:UNIV. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close>
    proof -
      have inj: \<open>inj_on ((*\<^sub>C) (csqrt (spectral_dec_val t' n))) (some_onb_of (spectral_dec_space t' n))\<close> for n
      proof (cases \<open>spectral_dec_val t' n = 0\<close>)
        case True
        then have \<open>spectral_dec_space t' n = 0\<close>
          using spectral_dec_space_0 by blast
        then have \<open>some_onb_of (spectral_dec_space t' n) = {}\<close>
          using some_onb_of_0 by auto
        then show ?thesis
          by simp
      next
        case False
        then show ?thesis
          by (auto intro!: inj_scaleC)
      qed
      have 1: \<open>(\<lambda>x. tc_butterfly x x) abs_summable_on (\<lambda>xa. csqrt (spectral_dec_val t' n) *\<^sub>C xa) ` some_onb_of (spectral_dec_space t' n)\<close> for n
        by (auto intro!: summable_on_finite some_onb_of_finite_dim spectral_dec_space_finite_dim simp: t'_def)
      (* have \<open>(\<Sum>\<^sub>\<infinity>x\<in>some_onb_of (spectral_dec_space t' h). norm (tc_butterfly x x)) = spectral_dec_proj t' h\<close> for h *)
      have \<open>(\<lambda>n. cmod (spectral_dec_val t' n) * (\<Sum>\<^sub>\<infinity>h\<in>some_onb_of (spectral_dec_space t' n). norm (tc_butterfly h h))) abs_summable_on UNIV\<close>
      proof -
        have *: \<open>(\<Sum>\<^sub>\<infinity>h\<in>some_onb_of (spectral_dec_space t' n). norm (tc_butterfly h h)) = norm (spectral_dec_proj_tc t n)\<close> for n
        proof -
          have \<open>(\<Sum>\<^sub>\<infinity>h\<in>some_onb_of (spectral_dec_space t' n). norm (tc_butterfly h h))
              = (\<Sum>\<^sub>\<infinity>h\<in>some_onb_of (spectral_dec_space t' n). 1)\<close>
            by (simp add: infsum_cong norm_tc_butterfly some_onb_of_norm1)
          also have \<open>\<dots> = card (some_onb_of (spectral_dec_space t' n))\<close>
            by simp
          also have \<open>\<dots> = cdim (space_as_set (spectral_dec_space t' n))\<close>
            by (simp add: some_onb_of_card)
          also have \<open>\<dots> = norm (spectral_dec_proj_tc t n)\<close>
            unfolding t'_def 
            apply transfer
            by (metis of_real_eq_iff of_real_of_nat_eq spectral_dec_proj_def spectral_dec_proj_pos
                trace_Proj trace_norm_pos)
          finally show ?thesis
            by -
        qed
        show ?thesis
          apply (simp add: * )
          by (metis (no_types, lifting) \<open>selfadjoint_tc t\<close> norm_scaleC spectral_dec_summable_tc
              spectral_dec_val_tc.rep_eq summable_on_cong t'_def)
      qed
      then have 2: \<open>(\<lambda>n. \<Sum>\<^sub>\<infinity>v\<in>(*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n).
            norm (tc_butterfly v v)) abs_summable_on UNIV\<close>
        apply (subst infsum_reindex)
        by (auto intro!: inj simp: o_def infsum_cmult_right' norm_mult (* inj_on_def *) simp del: real_norm_def)
      show ?thesis
        apply (rule abs_summable_summable)
        apply (rule abs_summable_on_Sigma_iff[THEN iffD2])
        using 1 2 by auto
    qed
  qed
  have \<open>((\<lambda>v. tc_butterfly v v) has_sum t) (\<Union>n. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close>
  proof -
    have **: \<open>(\<Union>n. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n)) =
              snd ` (SIGMA n:UNIV. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close>
      by force
    have inj: \<open>inj_on snd (SIGMA n:UNIV. (\<lambda>x. csqrt (spectral_dec_val t' n) *\<^sub>C x) ` some_onb_of (spectral_dec_space t' n))\<close>
    proof (rule inj_onI)
      fix nh assume nh: \<open>nh \<in> (SIGMA n:UNIV. (\<lambda>x. csqrt (spectral_dec_val t' n) *\<^sub>C x) ` some_onb_of (spectral_dec_space t' n))\<close>
      fix mg assume mg: \<open>mg \<in> (SIGMA m:UNIV. (\<lambda>x. csqrt (spectral_dec_val t' m) *\<^sub>C x) ` some_onb_of (spectral_dec_space t' m))\<close>
      assume \<open>snd nh = snd mg\<close>
      from nh obtain n h where nh': \<open>nh = (n, csqrt (spectral_dec_val t' n) *\<^sub>C h)\<close> and h: \<open>h \<in> some_onb_of (spectral_dec_space t' n)\<close>
        by blast
      from mg obtain m g where mg': \<open>mg = (m, csqrt (spectral_dec_val t' m) *\<^sub>C g)\<close> and g: \<open>g \<in> some_onb_of (spectral_dec_space t' m)\<close>
        by blast
      have \<open>n = m\<close>
      proof (rule ccontr)
        assume [simp]: \<open>n \<noteq> m\<close>
        from h have val_not_0: \<open>spectral_dec_val t' n \<noteq> 0\<close>
          using some_onb_of_0 spectral_dec_space_0 by fastforce
        from \<open>snd nh = snd mg\<close> nh' mg' have eq: \<open>csqrt (spectral_dec_val t' n) *\<^sub>C h = csqrt (spectral_dec_val t' m) *\<^sub>C g\<close>
          by simp
        from \<open>n \<noteq> m\<close> have \<open>orthogonal_spaces (spectral_dec_space t' n) (spectral_dec_space t' m)\<close>
          apply (rule spectral_dec_space_orthogonal[rotated -1])
          using \<open>selfadjoint_tc t\<close> by (auto intro!: trace_class_compact simp: t'_def selfadjoint_tc.rep_eq)
        with h g have \<open>is_orthogonal h g\<close>
          using orthogonal_spaces_ccspan by fastforce
        then have \<open>is_orthogonal (csqrt (spectral_dec_val t' n) *\<^sub>C h) (csqrt (spectral_dec_val t' m) *\<^sub>C g)\<close>
          by force
        with eq have val_h_0: \<open>csqrt (spectral_dec_val t' n) *\<^sub>C h = 0\<close>
          by simp
        with val_not_0 have \<open>h = 0\<close>
          by fastforce
        with h show False
          using some_onb_of_is_ortho_set
          by (auto simp: is_ortho_set_def)
      qed
      with \<open>snd nh = snd mg\<close> nh' mg' show \<open>nh = mg\<close>
        by simp
    qed
    from * show ?thesis
      apply (subst ** )
      apply (rule has_sum_reindex[THEN iffD2, rotated])
      by (auto intro!: inj simp: o_def case_prod_unfold)
  qed
  then show ?thesis
    by (simp add: spectral_dec_vecs_tc.rep_eq spectral_dec_vecs_def flip: t'_def)
qed


lemma spectral_dec_vec_tc_norm_summable:
  assumes \<open>t \<ge> 0\<close>
  shows \<open>(\<lambda>v. (norm v)\<^sup>2) summable_on (spectral_dec_vecs_tc t)\<close>
proof -
  from butterfly_spectral_dec_vec_tc_has_sum[OF assms]
  have \<open>(\<lambda>v. tc_butterfly v v) summable_on (spectral_dec_vecs_tc t)\<close>
    using has_sum_imp_summable by blast
  then have \<open>(\<lambda>v. trace_tc (tc_butterfly v v)) summable_on (spectral_dec_vecs_tc t)\<close>
    apply (rule summable_on_bounded_linear[rotated])
    by (simp add: bounded_clinear.bounded_linear)
  moreover have *: \<open>trace_tc (tc_butterfly v v) = of_real ((norm v)\<^sup>2)\<close> for v :: 'a
    by (metis norm_tc_butterfly norm_tc_pos power2_eq_square tc_butterfly_pos)
  ultimately have \<open>(\<lambda>v. complex_of_real ((norm v)\<^sup>2)) summable_on (spectral_dec_vecs_tc t)\<close>
    by simp
  then show ?thesis
    by (smt (verit, ccfv_SIG) *
        complex_Re_le_cmod norm_tc_butterfly of_real_hom.hom_power power2_eq_square power2_norm_eq_cinner 
        power2_norm_eq_cinner' summable_on_cong summable_on_iff_abs_summable_on_complex trace_tc_norm)
qed

lemma summable_on_in_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "summable_on_in T f A \<longleftrightarrow> summable_on_in T g A"
  by (simp add: summable_on_in_def has_sum_in_cong[OF assms])

definition diagonal_operator where \<open>diagonal_operator f = 
  (if bdd_above (range (\<lambda>x. cmod (f x))) then explicit_cblinfun (\<lambda>x y. of_bool (x=y) * f x) else 0)\<close>


lemma diagonal_operator_exists:
  assumes \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  shows \<open>explicit_cblinfun_exists (\<lambda>x y. of_bool (x = y) * f x)\<close>
proof -
  from assms obtain B where B: \<open>cmod (f x) \<le> B\<close> for x
    by (auto simp: bdd_above_def)
  show ?thesis
  proof (rule explicit_cblinfun_exists_bounded)
    fix S T :: \<open>'a set\<close> and \<psi> :: \<open>'a \<Rightarrow> complex\<close>
    assume [simp]: \<open>finite S\<close> \<open>finite T\<close>
    assume \<open>\<psi> a = 0\<close> if \<open>a \<notin> T\<close> for a
    have \<open>(\<Sum>b\<in>S. (cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C (of_bool (b = a) * f b)))\<^sup>2)
        = (\<Sum>b\<in>S. (cmod (of_bool (b \<in> T) * \<psi> b * f b))\<^sup>2)\<close>
      apply (rule sum.cong[OF refl])
      subgoal for b
        apply (subst sum_single[where i=b])
        by auto
      by -
    also have \<open>\<dots> = (\<Sum>b\<in>S\<inter>T. (cmod (\<psi> b * f b))\<^sup>2)\<close>
      apply (rule sum.mono_neutral_cong_right)
      by auto
    also have \<open>\<dots> \<le> (\<Sum>b\<in>T. (cmod (\<psi> b * f b))\<^sup>2)\<close>
      by (simp add: sum_mono2)
    also have \<open>\<dots> \<le> (\<Sum>b\<in>T. B\<^sup>2 * (cmod (\<psi> b))\<^sup>2)\<close>
      apply (rule sum_mono)
      apply (auto intro!: simp: norm_mult power_mult_distrib)
      apply (subst mult.commute)
      by (simp add: B mult_right_mono power_mono)
    also have \<open>\<dots> = B\<^sup>2 * (\<Sum>b\<in>T. (cmod (\<psi> b))\<^sup>2)\<close>
      by (simp add: vector_space_over_itself.scale_sum_right)
    finally
    show \<open>(\<Sum>b\<in>S. (cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C (of_bool (b = a) * f b)))\<^sup>2)
       \<le> B\<^sup>2 * (\<Sum>a\<in>T. (cmod (\<psi> a))\<^sup>2)\<close>
      by -
  qed
qed


lemma diagonal_operator_ket:
  assumes \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  shows \<open>diagonal_operator f (ket x) = f x *\<^sub>C ket x\<close>
proof -
  have [simp]: \<open>has_ell2_norm (\<lambda>b. of_bool (b = x) * f b)\<close>
    by (auto intro!: finite_nonzero_values_imp_summable_on simp: has_ell2_norm_def)
  have \<open>Abs_ell2 (\<lambda>b. of_bool (b = x) * f b) = f x *\<^sub>C ket x\<close>
    apply (rule Rep_ell2_inject[THEN iffD1])
    by (auto simp: Abs_ell2_inverse scaleC_ell2.rep_eq ket.rep_eq)
  then show ?thesis
    by (auto intro!: simp: diagonal_operator_def assms explicit_cblinfun_ket diagonal_operator_exists)
qed

lemma diagonal_operator_invalid:
  assumes \<open>\<not> bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  shows \<open>diagonal_operator f = 0\<close>
  by (simp add: assms diagonal_operator_def)


lemma diagonal_operator_adj: \<open>diagonal_operator f* = diagonal_operator (\<lambda>x. cnj (f x))\<close>
  apply (cases \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>)
  by (auto intro!: equal_ket cinner_ket_eqI 
      simp: diagonal_operator_ket cinner_adj_right diagonal_operator_invalid)

lemma diagonal_operator_comp:
  assumes \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  assumes \<open>bdd_above (range (\<lambda>x. cmod (g x)))\<close>
  shows \<open>diagonal_operator f o\<^sub>C\<^sub>L diagonal_operator g = diagonal_operator (\<lambda>x. (f x * g x))\<close>
proof -
  have \<open>bdd_above (range (\<lambda>x. cmod (f x * g x)))\<close>
  proof -
    from assms(1) obtain F where \<open>cmod (f x) \<le> F\<close> for x
      by (auto simp: bdd_above_def)
    moreover from assms(2) obtain G where \<open>cmod (g x) \<le> G\<close> for x
      by (auto simp: bdd_above_def)
    ultimately have \<open>cmod (f x * g x) \<le> F * G\<close> for x
      by (smt (verit, del_insts) mult_right_mono norm_ge_zero norm_mult ordered_comm_semiring_class.comm_mult_left_mono)
    then show ?thesis
      by fast
  qed
  then show ?thesis
    by (auto intro!: equal_ket simp: diagonal_operator_ket assms cblinfun.scaleC_right)
qed


lemma diagonal_operator_pos:
  assumes \<open>\<And>x. f x \<ge> 0\<close>
  shows \<open>diagonal_operator f \<ge> 0\<close>
proof (cases \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>)
  case True
  have [simp]: \<open>csqrt (f x) = sqrt (cmod (f x))\<close> for x
    by (simp add: Extra_Ordered_Fields.complex_of_real_cmod assms abs_pos of_real_sqrt)
  have bdd: \<open>bdd_above (range (\<lambda>x. sqrt (cmod (f x))))\<close>
  proof -
    from True obtain B where \<open>cmod (f x) \<le> B\<close> for x
      by (auto simp: bdd_above_def)
    then show ?thesis
      by (auto intro!: bdd_aboveI[where M=\<open>sqrt B\<close>] simp: )
  qed
  show ?thesis
    apply (rule positive_cblinfun_squareI[where B=\<open>diagonal_operator (\<lambda>x. csqrt (f x))\<close>])
    by (simp add: assms diagonal_operator_adj diagonal_operator_comp bdd complex_of_real_cmod abs_pos
        flip: of_real_mult)
next
  case False
  then show ?thesis
    by (simp add: diagonal_operator_invalid)
qed

lemma abs_op_diagonal_operator: 
  \<open>abs_op (diagonal_operator f) = diagonal_operator (\<lambda>x. abs (f x))\<close>
proof (cases \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>)
  case True
  show ?thesis
    apply (rule abs_opI[symmetric])
    by (auto intro!: diagonal_operator_pos abs_nn simp: True diagonal_operator_adj diagonal_operator_comp cnj_x_x)
next
  case False
  then show ?thesis
    by (simp add: diagonal_operator_invalid)
qed



lift_definition diagonal_operator_tc :: \<open>('a \<Rightarrow> complex) \<Rightarrow> ('a ell2, 'a ell2) trace_class\<close> is
  \<open>\<lambda>f. if f abs_summable_on UNIV then diagonal_operator f else 0\<close>
proof (rule CollectI)
  fix f :: \<open>'a \<Rightarrow> complex\<close>
  show \<open>trace_class (if f abs_summable_on UNIV then diagonal_operator f else 0)\<close>
  proof (cases \<open>f abs_summable_on UNIV\<close>)
    case True
    have bdd: \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
    proof (rule bdd_aboveI2)
      fix x
      have \<open>cmod (f x) = (\<Sum>\<^sub>\<infinity>x\<in>{x}. cmod (f x))\<close>
        by simp
      also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x. cmod (f x))\<close>
        apply (rule infsum_mono_neutral)
        by (auto intro!: True)
      finally show \<open>cmod (f x) \<le> (\<Sum>\<^sub>\<infinity>x. cmod (f x))\<close>
        by -
    qed
    have \<open>trace_class (diagonal_operator f)\<close>
      by (auto intro!: trace_classI[OF is_onb_ket] summable_on_reindex[THEN iffD2] True
          simp: abs_op_diagonal_operator o_def diagonal_operator_ket bdd)
    with True show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by simp
  qed
qed

lemma summable_on_in_finite:
  fixes f :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add,topological_space}\<close>
  assumes "finite F"
  assumes \<open>sum f F \<in> topspace T\<close>
  shows "summable_on_in T f F"
  using assms summable_on_in_def has_sum_in_finite by blast

lemma unitary_tensor_ell2_right_CARD_1:
  fixes \<psi> :: \<open>'a :: {CARD_1,enum} ell2\<close>
  assumes \<open>norm \<psi> = 1\<close>
  shows \<open>unitary (tensor_ell2_right \<psi>)\<close>
proof (rule unitaryI)
  show \<open>tensor_ell2_right \<psi>* o\<^sub>C\<^sub>L tensor_ell2_right \<psi> = id_cblinfun\<close>
    by (simp add: assms isometry_tensor_ell2_right)
  have *: \<open>(\<psi> \<bullet>\<^sub>C \<phi>) * (\<phi> \<bullet>\<^sub>C \<psi>) = \<phi> \<bullet>\<^sub>C \<phi>\<close> for \<phi>
  proof -
    define \<psi>' \<phi>' where \<open>\<psi>' = 1 \<bullet>\<^sub>C \<psi>\<close> and \<open>\<phi>' = 1 \<bullet>\<^sub>C \<phi>\<close>
    have \<psi>: \<open>\<psi> = \<psi>' *\<^sub>C 1\<close>
      by (metis \<psi>'_def one_cinner_a_scaleC_one)
  have \<phi>: \<open>\<phi> = \<phi>' *\<^sub>C 1\<close>
      by (metis \<phi>'_def one_cinner_a_scaleC_one)
    show ?thesis
      apply (simp add: \<psi> \<phi>)
      by (metis (no_types, lifting) Groups.mult_ac(1) \<psi> assms cinner_simps(5) cinner_simps(6) norm_one of_complex_def of_complex_inner_1 power2_norm_eq_cinner)
  qed
  show \<open>tensor_ell2_right \<psi> o\<^sub>C\<^sub>L tensor_ell2_right \<psi>* = id_cblinfun\<close>
    apply (rule cblinfun_cinner_tensor_eqI)
    by (simp add: * )
qed

lemma trace_tc_pos: \<open>t \<ge> 0 \<Longrightarrow> trace_tc t \<ge> 0\<close>
  using trace_tc_mono by fastforce

lemma summable_on_bdd_above_real: \<open>bdd_above (f ` M)\<close> if \<open>f summable_on M\<close> for f :: \<open>'a \<Rightarrow> real\<close>
proof -
  from that have \<open>f abs_summable_on M\<close>
    unfolding summable_on_iff_abs_summable_on_real[symmetric]
    by -
  then have \<open>bdd_above (sum (\<lambda>x. norm (f x)) ` {F. F \<subseteq> M \<and> finite F})\<close>
    unfolding abs_summable_iff_bdd_above by simp
  then have \<open>bdd_above (sum (\<lambda>x. norm (f x)) ` (\<lambda>x. {x}) ` M)\<close>
    apply (rule bdd_above_mono)
    by auto
  then have \<open>bdd_above ((\<lambda>x. norm (f x)) ` M)\<close>
    by (simp add: image_image)
  then show ?thesis
    by (simp add: bdd_above_mono2)
qed

lift_definition tc_apply :: \<open>('a::chilbert_space,'b::chilbert_space) trace_class \<Rightarrow> 'a \<Rightarrow> 'b\<close> is cblinfun_apply.

lemma bounded_cbilinear_tc_apply: \<open>bounded_cbilinear tc_apply\<close>
  apply (rule bounded_cbilinear.intro; transfer)
      apply (auto intro!: simp: )
  apply (auto intro!: exI[of _ 1] cblinfun.add_left cblinfun.add_right cblinfun.scaleC_right)
  by (smt (verit, del_insts) norm_leq_trace_norm mult_hom.hom_zero mult_less_cancel_right norm_cblinfun norm_not_less_zero not_square_less_zero ordered_field_class.sign_simps(5) ordered_field_class.sign_simps(50) rel_simps(70) vector_space_over_itself.scale_eq_0_iff vector_space_over_itself.scale_left_commute vector_space_over_itself.vector_space_assms(3))

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



lemma tc_butterfly_scaleC_infsum:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) = diagonal_operator_tc f\<close>
proof (cases \<open>f abs_summable_on UNIV\<close>)
  case True
  then show ?thesis
    using infsumI tc_butterfly_scaleC_has_sum by fastforce
next
  case False
  then have [simp]: \<open>diagonal_operator_tc f = 0\<close>
    apply (transfer fixing: f) by simp
  have \<open>\<not> (\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) summable_on UNIV\<close>
  proof (rule notI)
    assume \<open>(\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) summable_on UNIV\<close>
    then have \<open>(\<lambda>x. trace_tc (f x *\<^sub>C tc_butterfly (ket x) (ket x))) summable_on UNIV\<close>
      apply (rule summable_on_bounded_linear[rotated])
      by (simp add: bounded_clinear.bounded_linear)
    then have \<open>f summable_on UNIV\<close>
      apply (rule summable_on_cong[THEN iffD1, rotated])
      apply (transfer' fixing: f)
      by (simp add: trace_scaleC trace_butterfly)
    with False
    show False
      by (metis summable_on_iff_abs_summable_on_complex)
  qed
  then have [simp]: \<open>(\<Sum>\<^sub>\<infinity>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) = 0\<close>
    using infsum_not_exists by blast
  show ?thesis 
    by simp
qed

lemma infsum_of_bool_scaleC: \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. of_bool (x=y) *\<^sub>C f x) = of_bool (y\<in>X) *\<^sub>C f y\<close> for f :: \<open>_ \<Rightarrow> _::complex_vector\<close>
  apply (cases \<open>y\<in>X\<close>)
   apply (subst infsum_cong_neutral[where T=\<open>{y}\<close> and g=f])
      apply auto[4]
  apply (subst infsum_cong_neutral[where T=\<open>{}\<close> and g=f])
  by auto

lemma diagonal_operator_tc_invalid: \<open>\<not> f abs_summable_on UNIV \<Longrightarrow> diagonal_operator_tc f = 0\<close>
  apply (transfer fixing: f) by simp

lemma infsum_in_0:
  assumes \<open>Hausdorff_space T\<close> and \<open>0 \<in> topspace T\<close>
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 0\<close>
  shows \<open>infsum_in T f M = 0\<close>
proof -
  have \<open>has_sum_in T f M 0\<close>
    using assms
    by (auto intro!: has_sum_in_0 Hausdorff_imp_t1_space)
  then show ?thesis
    by (meson assms(1) has_sum_in_infsum_in has_sum_in_unique not_summable_infsum_in_0)
qed

lemma has_sum_in_wot_compose_left:
  fixes f :: \<open>'c \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>has_sum_in cweak_operator_topology f X s\<close>
  shows \<open>has_sum_in cweak_operator_topology (\<lambda>x. a o\<^sub>C\<^sub>L f x) X (a o\<^sub>C\<^sub>L s)\<close>
proof (rule has_sum_in_cweak_operator_topology_pointwise[THEN iffD2], intro allI, rename_tac g h)
  fix g h
  from assms have \<open>((\<lambda>x. (a*) g \<bullet>\<^sub>C f x h) has_sum (a*) g \<bullet>\<^sub>C s h) X\<close>
    by (metis has_sum_in_cweak_operator_topology_pointwise)
  then show \<open>((\<lambda>x. g \<bullet>\<^sub>C (a o\<^sub>C\<^sub>L f x) h) has_sum g \<bullet>\<^sub>C (a o\<^sub>C\<^sub>L s) h) X\<close>
    by (metis (no_types, lifting) cblinfun_apply_cblinfun_compose cinner_adj_left has_sum_cong)
qed

lemma has_sum_in_wot_compose_right:
  fixes f :: \<open>'c \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner\<close>
  assumes \<open>has_sum_in cweak_operator_topology f X s\<close>
  shows \<open>has_sum_in cweak_operator_topology (\<lambda>x. f x o\<^sub>C\<^sub>L a) X (s o\<^sub>C\<^sub>L a)\<close>
proof (rule has_sum_in_cweak_operator_topology_pointwise[THEN iffD2], intro allI, rename_tac g h)
  fix g h
  from assms have \<open>((\<lambda>x. g \<bullet>\<^sub>C f x (a h)) has_sum g \<bullet>\<^sub>C s (a h)) X\<close>
    by (metis has_sum_in_cweak_operator_topology_pointwise)
  then show \<open>((\<lambda>x. g \<bullet>\<^sub>C (f x o\<^sub>C\<^sub>L a) h) has_sum g \<bullet>\<^sub>C (s o\<^sub>C\<^sub>L a) h) X\<close>
    by simp
qed



lemma summable_on_in_wot_compose_left:
  fixes f :: \<open>'c \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>summable_on_in cweak_operator_topology f X\<close>
  shows \<open>summable_on_in cweak_operator_topology (\<lambda>x. a o\<^sub>C\<^sub>L f x) X\<close>
  using has_sum_in_wot_compose_left assms
  by (fastforce simp: summable_on_in_def)

lemma summable_on_in_wot_compose_right:
  assumes \<open>summable_on_in cweak_operator_topology f X\<close>
  shows \<open>summable_on_in cweak_operator_topology (\<lambda>x. f x o\<^sub>C\<^sub>L a) X\<close>
  using has_sum_in_wot_compose_right assms
  by (fastforce simp: summable_on_in_def)


lemma infsum_in_wot_compose_left:
  fixes f :: \<open>'c \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>summable_on_in cweak_operator_topology f X\<close>
  shows \<open>infsum_in cweak_operator_topology (\<lambda>x. a o\<^sub>C\<^sub>L f x) X = a o\<^sub>C\<^sub>L (infsum_in cweak_operator_topology f X)\<close>
  by (metis (mono_tags, lifting) assms has_sum_in_infsum_in has_sum_in_unique hausdorff_cweak_operator_topology
      has_sum_in_wot_compose_left summable_on_in_wot_compose_left)

lemma infsum_in_wot_compose_right:
  fixes f :: \<open>'c \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner\<close>
  assumes \<open>summable_on_in cweak_operator_topology f X\<close>
  shows \<open>infsum_in cweak_operator_topology (\<lambda>x. f x o\<^sub>C\<^sub>L a) X = (infsum_in cweak_operator_topology f X) o\<^sub>C\<^sub>L a\<close>
  by (metis (mono_tags, lifting) assms has_sum_in_infsum_in has_sum_in_unique hausdorff_cweak_operator_topology
      has_sum_in_wot_compose_right summable_on_in_wot_compose_right)

lemma infsum_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{topological_comm_monoid_add, t3_space}\<close>
  assumes summableAB: "f summable_on (Sigma A B)"
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (\<lambda>y. f (x, y)) summable_on (B x)\<close>
  shows "infsum f (Sigma A B) = (\<Sum>\<^sub>\<infinity>x\<in>A. \<Sum>\<^sub>\<infinity>y\<in>B x. f (x, y))"
proof -
  have 1: \<open>(f has_sum infsum f (Sigma A B)) (Sigma A B)\<close>
    by (simp add: assms)
  define b where \<open>b x = (\<Sum>\<^sub>\<infinity>y\<in>B x. f (x, y))\<close> for x
  have 2: \<open>((\<lambda>y. f (x, y)) has_sum b x) (B x)\<close> if \<open>x \<in> A\<close> for x
    using b_def assms(2) that by auto
  have 3: \<open>(b has_sum (\<Sum>\<^sub>\<infinity>x\<in>A. b x)) A\<close>
    using 1 2 by (metis has_sum_SigmaD infsumI)
  have 4: \<open>(f has_sum (\<Sum>\<^sub>\<infinity>x\<in>A. b x)) (Sigma A B)\<close>
    using 2 3 apply (rule has_sum_SigmaI)
    using assms by auto
  from 1 4 show ?thesis
    using b_def[abs_def] infsumI by blast
qed



end
