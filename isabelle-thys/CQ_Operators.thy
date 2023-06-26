theory CQ_Operators
  imports Tensor_Product.Trace_Class Registers2.Missing_Bounded_Operators Discrete_Distributions
begin

typedef ('a,'b) cq_operator = \<open>{f :: 'a \<Rightarrow> ('b ell2, 'b ell2) trace_class. f abs_summable_on UNIV}\<close>
  morphisms cq_operator_at Abs_cq_operator
  apply (rule exI[of _ \<open>\<lambda>_. 0\<close>])
  by auto
setup_lifting type_definition_cq_operator

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

lift_definition cq_operator_cases :: \<open>('cin \<Rightarrow> ('qin ell2, 'qin ell2) trace_class \<Rightarrow> ('cout,'qout) cq_operator)
                                    \<Rightarrow> ('cin,'qin) cq_operator \<Rightarrow> ('cout,'qout) cq_operator\<close> is
\<open>\<lambda>(f::'cin \<Rightarrow> ('qin ell2, 'qin ell2) trace_class \<Rightarrow> ('cout \<Rightarrow> ('qout ell2, 'qout ell2) trace_class))
 (cqin::'cin \<Rightarrow> ('qin ell2, 'qin ell2) trace_class) 
 (cout::'cout). (\<Sum>\<^sub>\<infinity>cin::'cin. f cin (cqin cin) cout)\<close>
proof -
  fix f :: \<open>'cin \<Rightarrow> ('qin ell2, 'qin ell2) trace_class \<Rightarrow> ('cout \<Rightarrow> ('qout ell2, 'qout ell2) trace_class)\<close>
  fix cqin :: \<open>'cin \<Rightarrow> ('qin ell2, 'qin ell2) trace_class\<close>
  assume \<open>f cin qin abs_summable_on UNIV\<close> for cin qin
  assume \<open>cqin abs_summable_on UNIV\<close>
  have \<open>(\<lambda>(cout,cin). f cin (cqin cin) cout) abs_summable_on UNIV \<times> UNIV\<close>
    (* by x *)
    sorry
  then show \<open>(\<lambda>cout. \<Sum>\<^sub>\<infinity>cin. f cin (cqin cin) cout) abs_summable_on UNIV\<close>
    unfolding abs_summable_on_Sigma_iff
    apply auto
    sorry
qed

lift_definition cq_from_distrib :: \<open>'c distr \<Rightarrow> ('q ell2, 'q ell2) trace_class \<Rightarrow> ('c,'q) cq_operator\<close> is
  \<open>\<lambda>(\<mu>::'c distr) (\<rho>::('q ell2, 'q ell2) trace_class) x. prob \<mu> x *\<^sub>R \<rho>\<close>
  by (intro Extra_Vector_Spaces.abs_summable_on_scaleR_left prob_abs_summable)

lift_definition deterministic_cq :: \<open>'c \<Rightarrow> ('q ell2, 'q ell2) trace_class \<Rightarrow> ('c,'q) cq_operator\<close> is
  \<open>\<lambda>(x::'c) (\<rho>::('q ell2, 'q ell2) trace_class) y. of_bool (x=y) *\<^sub>R \<rho>\<close>
proof (rename_tac c \<rho>)
  fix c :: 'c and \<rho> :: \<open>('q ell2, 'q ell2) trace_class\<close>
  show \<open>(\<lambda>x. of_bool (c = x) *\<^sub>R \<rho>) abs_summable_on UNIV\<close>
    apply (rule summable_on_cong_neutral[where T=\<open>{c}\<close>, THEN iffD2])
    by auto
qed

lemma cq_from_distrib_point_distr: \<open>cq_from_distrib (point_distr x) \<rho> = deterministic_cq x \<rho>\<close>
  apply (rule cq_operator_at_inject[THEN iffD1])
  by (auto simp add: cq_from_distrib.rep_eq deterministic_cq.rep_eq)

end