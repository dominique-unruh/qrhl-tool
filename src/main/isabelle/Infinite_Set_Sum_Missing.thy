theory Infinite_Set_Sum_Missing
  imports "HOL-Analysis.Infinite_Set_Sum" Ordered_Complex
begin

lemma abs_summable_finiteI0:
  assumes "\<And>F. finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum (\<lambda>x. norm (f x)) F \<le> B"
    and "B \<ge> 0"
  shows "f abs_summable_on S" and "infsetsum (\<lambda>x. norm (f x)) S \<le> B"
  unfolding atomize_conj
proof (cases "S={}")
  case True
  then show "f abs_summable_on S \<and> infsetsum (\<lambda>x. norm (f x)) S \<le> B" 
    using assms by auto
next
  case False
  define M normf where "M = count_space S" and "normf x = ennreal (norm (f x))" for x

  have normf_B: "finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum normf F \<le> ennreal B" for F
        using assms[THEN ennreal_leI] 
        apply (subst (asm) sum_ennreal[symmetric], simp)
        unfolding normf_def[symmetric] by simp

  have "integral\<^sup>S M g \<le> B" if "simple_function M g" and "g \<le> normf" for g 
  proof -
    define gS where "gS = g ` S"
    have "finite gS"
      using that unfolding gS_def M_def simple_function_count_space by simp
    have "gS \<noteq> {}" unfolding gS_def using False by auto
    define part where "part r = g -` {r} \<inter> S" for r
    have r_finite: "r < \<infinity>" if "r : gS" for r 
      using \<open>g \<le> normf\<close> that unfolding gS_def le_fun_def normf_def apply auto
      using ennreal_less_top neq_top_trans top.not_eq_extremum by blast
    define B' where "B' r = (SUP F:{F. finite F \<and> F\<subseteq>part r}. sum normf F)" for r
    have B'fin: "B' r < \<infinity>" for r
    proof -
      have "B' r \<le> (SUP F:{F. finite F \<and> F\<subseteq>part r}. sum normf F)"
        unfolding B'_def
        by (metis (mono_tags, lifting) SUP_least SUP_upper)
      also have "\<dots> \<le> B"
        using normf_B unfolding part_def
        by (metis (no_types, lifting) Int_subset_iff SUP_least mem_Collect_eq)
      also have "\<dots> < \<infinity>"
        by simp
      finally show ?thesis by simp
    qed
    have sumB': "sum B' gS \<le> ennreal B + \<epsilon>" if "\<epsilon>>0" for \<epsilon>
    proof -
      define N \<epsilon>N where "N = card gS" and "\<epsilon>N = \<epsilon> / N"
      have "N > 0" 
        unfolding N_def using \<open>gS\<noteq>{}\<close> \<open>finite gS\<close>
        by (simp add: card_gt_0_iff)
      from \<epsilon>N_def that have "\<epsilon>N > 0"
        by (simp add: ennreal_of_nat_eq_real_of_nat ennreal_zero_less_divide)
      obtain F where F: "sum normf (F r) + \<epsilon>N \<ge> B' r" and Ffin: "finite (F r)" and Fpartr: "F r \<subseteq> part r" for r
        apply atomize_elim apply (subst all_conj_distrib[symmetric])+ apply (rule choice) apply (rule allI)
        apply (rename_tac r) apply (case_tac "B' r = 0") 
      proof -
        fix r assume "B' r = 0" 
        then show "\<exists>F. B' r \<le> sum normf F + \<epsilon>N \<and> finite F \<and> F \<subseteq> part r" by auto
      next
        fix r :: ennreal
        assume "B' r \<noteq> 0"
        with \<open>\<epsilon>N > 0\<close> B'fin have "B' r - \<epsilon>N < B' r"
          by (metis ennreal_between infinity_ennreal_def le_zero_eq not_le)
        then obtain F where "B' r - \<epsilon>N \<le> sum normf F" and "finite F" and "F \<subseteq> part r"
          apply atomize_elim apply (subst (asm) (2) B'_def)
          by (metis (no_types, lifting) leD le_cases less_SUP_iff mem_Collect_eq)
        then show "\<exists>F. B' r \<le> sum normf F + \<epsilon>N \<and> finite F \<and> F \<subseteq> part r"
          by (metis add.commute ennreal_minus_le_iff)
      qed
      have "sum B' gS \<le> (\<Sum>r\<in>gS. sum normf (F r) + \<epsilon>N)"
        using F by (simp add: sum_mono)
      also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + (\<Sum>r\<in>gS. \<epsilon>N)"
        by (simp add: sum.distrib)
      also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + (card gS * \<epsilon>N)"
        by auto
      also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + \<epsilon>"
        unfolding \<epsilon>N_def N_def[symmetric] using \<open>N>0\<close> 
        by (simp add: ennreal_times_divide mult.commute mult_divide_eq_ennreal)
      also have "\<dots> = sum normf (UNION gS F) + \<epsilon>" 
        apply (subst sum.UNION_disjoint[symmetric])
        using \<open>finite gS\<close> apply assumption
        using Ffin apply simp
        using Fpartr[unfolded part_def] apply auto[1]
        apply (metis subsetCE vimage_singleton_eq)
        by simp
      also have "\<dots> \<le> B + \<epsilon>"
        apply (rule add_right_mono)
        apply (rule normf_B)
        using \<open>finite gS\<close> Ffin Fpartr unfolding part_def by auto
      finally show ?thesis
        by auto
    qed
    then have sumB': "sum B' gS \<le> B"
      using ennreal_le_epsilon ennreal_less_zero_iff by blast
(*     hence "B' r < \<infinity>" if "r \<in> gS" for r
    proof -
      have "sum B' gS = sum B' (gS - {r}) + B' r"
        by (simp add: \<open>finite gS\<close> add.commute sum.remove that)
      moreover have "0 \<le> sum B' (gS - {r})" by auto
      ultimately have "B' r \<le> B" 
        using sumB'
        by (metis add.commute add.right_neutral add_mono_thms_linordered_semiring(1) dual_order.antisym le_cases)
      then show ?thesis
        using le_less_trans by fastforce
    qed *)
    obtain B'' where B'': "B' r = ennreal (B'' r)" if "r \<in> gS" for r
      apply atomize_elim apply (rule_tac choice) 
      using B'fin apply auto using less_top_ennreal by blast
    have cases[case_names zero finite infinite]: "P" if "r=0 \<Longrightarrow> P" and "finite (part r) \<Longrightarrow> P"
        and "infinite (part r) \<Longrightarrow> r\<noteq>0 \<Longrightarrow> P" for P r
      using that by metis
    have emeasure_B': "r * emeasure M (part r) \<le> B' r" if "r : gS" for r
    proof (cases rule:cases[of r])
      case zero
      then show ?thesis by simp
    next
      case finite
      have "r * of_nat (card (part r)) = r * (\<Sum>x\<in>part r. 1)" by simp
      also have "\<dots> = (\<Sum>x\<in>part r. r)"
        using mult.commute by auto
      also have "\<dots> = (\<Sum>x\<in>part r. g x)"
        unfolding part_def by auto
      also have "\<dots> \<le> (SUP F:{F. finite F \<and> F\<subseteq>part r}. sum g F)"
        using finite apply auto
        by (simp add: Sup_upper)
      also have "\<dots> \<le> B' r"
        unfolding B'_def
        apply (rule SUP_subset_mono, simp) 
        apply (rule sum_mono) 
        using \<open>g \<le> normf\<close>
        by (simp add: le_fun_def) 
      finally have "r * of_nat (card (part r)) \<le> B' r" by assumption
      then show ?thesis
        unfolding M_def
        apply (subst emeasure_count_space_finite)
        using part_def finite by auto
    next
      case infinite
      from r_finite[OF \<open>r : gS\<close>] obtain r' where r': "r = ennreal r'"
        using ennreal_cases by auto
      with infinite have "r' > 0"
        using ennreal_less_zero_iff not_gr_zero by blast
      obtain N::nat where N:"N > B / r'" and "real N > 0" apply atomize_elim
        using reals_Archimedean2
        by (metis less_trans linorder_neqE_linordered_idom)
      obtain F where "finite F" and "card F = N" and "F \<subseteq> part r"
        apply atomize_elim using infinite
        by (simp add: infinite_arbitrarily_large)
      from \<open>F \<subseteq> part r\<close> have "F \<subseteq> S" unfolding part_def by simp
      have "B < r * N"
        using N unfolding r' ennreal_of_nat_eq_real_of_nat
        apply (subst ennreal_mult[symmetric])
        using ennreal_le_iff2 ennreal_neg infinite(2) r' apply blast
         apply simp
        apply (rule ennreal_lessI)
        using \<open>r' > 0\<close> \<open>real N > 0\<close> apply simp
        using \<open>r' > 0\<close> by (simp add: linordered_field_class.pos_divide_less_eq mult.commute)
      also have "r * N = (\<Sum>x\<in>F. r)"
        using \<open>card F = N\<close> by (simp add: mult.commute)
      also have "(\<Sum>x\<in>F. r) = (\<Sum>x\<in>F. g x)"
        apply (rule sum.cong)
        using \<open>F \<subseteq> part r\<close> using part_def by auto
      also have "(\<Sum>x\<in>F. g x) \<le> (\<Sum>x\<in>F. ennreal (norm (f x)))"
        apply (rule sum_mono) using \<open>g \<le> normf\<close> unfolding normf_def le_fun_def by auto
      also have "(\<Sum>x\<in>F. ennreal (norm (f x))) \<le> B" 
         apply auto using assms(1)[OF \<open>finite F\<close> \<open>F \<subseteq> S\<close>] by (rule ennreal_leI)
      finally have "B < B" by auto
      then show ?thesis by simp
    qed

    have "integral\<^sup>S M g = (\<Sum>r \<in> gS. r * emeasure M (part r))"
      unfolding simple_integral_def gS_def M_def part_def by simp
    also have "\<dots> \<le> (\<Sum>r \<in> gS. B' r)"
      apply (rule sum_mono) using emeasure_B' by auto
    also have "\<dots> \<le> B"
      using sumB' by blast
    finally show ?thesis by assumption
  qed
  hence int_leq_B: "integral\<^sup>N M normf \<le> B"
    unfolding nn_integral_def by (metis (no_types, lifting) SUP_least mem_Collect_eq)
  hence "integral\<^sup>N M normf < \<infinity>"
    using le_less_trans by fastforce
  hence "integrable M f"
    unfolding M_def normf_def by (rule integrableI_bounded[rotated], simp)
  then have f_sum_S: "f abs_summable_on S"
    unfolding abs_summable_on_def M_def by simp
  have "infsetsum (\<lambda>x. norm (f x)) S \<le> B"
    apply (subst ennreal_le_iff[symmetric], simp add: assms)
    apply (subst nn_integral_conv_infsetsum[symmetric])
    using f_sum_S int_leq_B 
    unfolding normf_def M_def by auto
  with f_sum_S
  show "f abs_summable_on S \<and> infsetsum (\<lambda>x. norm (f x)) S \<le> B" by simp
qed

lemma abs_summable_finiteI:
  assumes "\<And>F. finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum (\<lambda>x. norm (f x)) F \<le> B"
  shows "f abs_summable_on S"
proof -
  from assms have "sum (\<lambda>x. norm (f x)) {} \<le> B" by blast
  then have "0 \<le> B" by simp
  then show ?thesis 
    using assms by (rule abs_summable_finiteI0[rotated])
qed

lemma infsetsum_finite_sets:
  assumes "\<And>F. finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum (\<lambda>x. norm (f x)) F \<le> B"
    and "B \<ge> 0" and "\<And>x. f x \<ge> 0"
  shows "infsetsum f S \<le> B"
  using abs_summable_finiteI0(2)[where f=f and S=S, OF assms(1-2), simplified]
  using assms(3) by auto

lemma abs_summable_finiteI_converse:
  assumes f_sum_S: "f abs_summable_on S"
  defines "B \<equiv> (infsetsum (\<lambda>x. norm (f x)) S)"
  assumes finite_F: "finite F" and FS: "F\<subseteq>S"
  shows "sum (\<lambda>x. norm (f x)) F \<le> B"
proof -
  have "sum (\<lambda>x. norm (f x)) F = infsetsum (\<lambda>x. norm (f x)) F"
    apply (rule infsetsum_finite[symmetric]) by (fact finite_F)
  also have "infsetsum (\<lambda>x. norm (f x)) F \<le> B"
    unfolding B_def 
    apply (rule infsetsum_mono_neutral_left)
    using finite_F apply (rule abs_summable_on_finite)
    using f_sum_S apply (rule abs_summable_on_normI)
    apply (rule order.refl)
    apply (fact FS)
    by (rule norm_ge_zero)
  finally show ?thesis by assumption
qed

lemma abs_summable_countable:
  fixes \<mu> :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes "\<mu> abs_summable_on T"
  shows "countable {x\<in>T. 0 \<noteq> \<mu> x}"
proof -
  define B where "B = infsetsum (\<lambda>x. norm (\<mu> x)) T"
  have \<mu>sum: "sum (\<lambda>x. norm (\<mu> x)) F \<le> B" if "finite F" and "F \<subseteq> T" for F
    unfolding B_def apply (rule abs_summable_finiteI_converse)
    using assms that by auto
  define S where "S i = {x\<in>T. 1/real (Suc i) < norm (\<mu> x)}" for i::nat
  have "\<exists>i. x \<in> S i" if "0 < norm (\<mu> x)" and "x \<in> T" for x
    using that unfolding S_def apply (auto simp del: real_norm_def)
    by (metis inverse_eq_divide not0_implies_Suc of_nat_Suc real_arch_inverse that(1))
  then have union: "{x\<in>T. 0 < norm (\<mu> x)} = (\<Union>i. S i)"
    unfolding S_def by auto
  have finiteS: "finite (S i)" for i
  proof (rule ccontr)
    assume "infinite (S i)"
    then obtain F where F_Si: "F \<subseteq> S i" and cardF: "card F > (Suc i)*B" and finiteF: "finite F"
      by (metis One_nat_def ex_less_of_nat_mult infinite_arbitrarily_large lessI mult.commute mult.left_neutral of_nat_0_less_iff of_nat_1)
    from F_Si have F_T: "F \<subseteq> T" 
      unfolding S_def by blast
    from finiteF \<mu>sum F_T have sumF: "sum (\<lambda>x. norm (\<mu> x)) F \<le> B" by simp
    have "sum (\<lambda>x. norm (\<mu> x)) F \<ge> sum (\<lambda>_. 1/real (Suc i)) F" (is "_ \<ge> \<dots>")
      apply (rule sum_mono)
      using F_Si S_def by auto
    moreover have "\<dots> = real (card F) / (Suc i)"
      by (subst sum_constant_scale, auto)
    moreover have "\<dots> > B"
      using cardF
      by (simp add: linordered_field_class.mult_imp_less_div_pos ordered_field_class.sign_simps)
    ultimately have "sum (\<lambda>x. norm (\<mu> x)) F > B"
      by linarith 
    with sumF show False by simp
  qed
  have "countable (\<Union>i. S i)"
    apply (rule countable_UN, simp)
    apply (rule countable_finite)
    using finiteS by simp
  then have "countable {x\<in>T. 0 < norm (\<mu> x)}"
    unfolding union by simp
  then show ?thesis
    by simp
qed


lemma infsetsum_cnj[simp]: "infsetsum (\<lambda>x. cnj (f x)) M = cnj (infsetsum f M)"
  unfolding infsetsum_def by (rule integral_cnj)

lemma infsetsum_Re: 
  assumes "f abs_summable_on M"
  shows "infsetsum (\<lambda>x. Re (f x)) M = Re (infsetsum f M)"
  unfolding infsetsum_def apply (rule integral_Re)
  using assms by (simp add: abs_summable_on_def)
  
lemma infsetsum_Im: 
  assumes "f abs_summable_on M"
  shows "infsetsum (\<lambda>x. Im (f x)) M = Im (infsetsum f M)"
  unfolding infsetsum_def apply (rule integral_Im)
  using assms by (simp add: abs_summable_on_def)

lemma infsetsum_mono_complex:
  fixes f g :: "'a \<Rightarrow> complex"
  assumes f_sum: "f abs_summable_on A" and g_sum: "g abs_summable_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows   "infsetsum f A \<le> infsetsum g A"
proof -
  have "infsetsum f A = Complex (Re (infsetsum f A)) (Im (infsetsum f A))" by auto
  also have "Re (infsetsum f A) = infsetsum (\<lambda>x. Re (f x)) A"
    unfolding infsetsum_def apply (rule integral_Re[symmetric])
    using assms by (simp add: abs_summable_on_def)
  also have "Im (infsetsum f A) = infsetsum (\<lambda>x. Im (f x)) A"
    using f_sum by (rule infsetsum_Im[symmetric])
    (* unfolding infsetsum_def apply (rule integral_Im[symmetric]) *)
    (* using assms by (simp add: abs_summable_on_def) *)
  finally have fsplit: "infsetsum f A = Complex (\<Sum>\<^sub>ax\<in>A. Re (f x)) (\<Sum>\<^sub>ax\<in>A. Im (f x))" by assumption

  have "infsetsum g A = Complex (Re (infsetsum g A)) (Im (infsetsum g A))" by auto
  also have "Re (infsetsum g A) = infsetsum (\<lambda>x. Re (g x)) A"
    using g_sum by (rule infsetsum_Re[symmetric])
    (* unfolding infsetsum_def apply (rule integral_Re[symmetric]) *)
    (* using assms by (simp add: abs_summable_on_def) *)
  also have "Im (infsetsum g A) = infsetsum (\<lambda>x. Im (g x)) A "
    using g_sum by (rule infsetsum_Im[symmetric])
    (* unfolding infsetsum_def apply (rule integral_Im[symmetric]) *)
    (* using assms by (simp add: abs_summable_on_def) *)
  finally have gsplit: "infsetsum g A = Complex (\<Sum>\<^sub>ax\<in>A. Re (g x)) (\<Sum>\<^sub>ax\<in>A. Im (g x))" by assumption

  have Re_leq: "Re (f x) \<le> Re (g x)" if "x\<in>A" for x
    using that assms unfolding less_eq_complex_def by simp
  have Im_eq: "Im (f x) = Im (g x)" if "x\<in>A" for x
    using that assms 
    unfolding less_eq_complex_def by simp

  have Refsum: "(\<lambda>x. Re (f x)) abs_summable_on A"
    using assms(1) apply (rule abs_summable_on_comparison_test[where g=f])
    using abs_Re_le_cmod by auto
  have Regsum: "(\<lambda>x. Re (g x)) abs_summable_on A"
    using assms(2) apply (rule abs_summable_on_comparison_test[where g=g])
    using abs_Re_le_cmod by auto
    
  show "infsetsum f A \<le> infsetsum g A"
    unfolding fsplit gsplit
    apply (rule less_eq_complexI; simp)
    using Refsum Regsum Re_leq apply (rule infsetsum_mono)
    using Im_eq by auto
qed

lemma infsetsum_subset_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "f abs_summable_on B" and "A \<subseteq> B" and "\<And>x. x\<notin>A \<Longrightarrow> f x \<ge> 0"
  shows "infsetsum f A \<le> infsetsum f B"
proof -
  have fBA: "f abs_summable_on B - A"
    by (meson Diff_subset abs_summable_on_subset assms(1))

  have "0 = infsetsum (\<lambda>_.0) (B-A)" by auto
  also have "... \<le> infsetsum f (B - A)"
    apply (rule infsetsum_mono_complex)
    using assms fBA by auto
  also have "... = infsetsum f B - infsetsum f A"
    apply (rule infsetsum_Diff)
    using assms by auto
  finally show ?thesis by auto
qed

lemma abs_summable_product:
  fixes x :: "'a \<Rightarrow> 'b::{real_normed_div_algebra,banach,second_countable_topology}"
  assumes x2_sum: "(\<lambda>i. (x i) * (x i)) abs_summable_on A"
  and y2_sum: "(\<lambda>i. (y i) * (y i)) abs_summable_on A"
  shows "(\<lambda>i. x i * y i) abs_summable_on A"
proof (rule abs_summable_finiteI)
  have aux: "a\<le>a' \<Longrightarrow> b\<le>b' \<Longrightarrow> a+b \<le> a'+b'" for a b a' b' :: real by simp
  fix F assume "finite F" and "F \<subseteq> A"
  define B :: real where "B = (\<Sum>\<^sub>ai\<in>A. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>A. norm (y i * y i))"
  have "norm (x i * y i) \<le> norm (x i * x i) + norm (y i * y i)" for i
    unfolding norm_mult
    by (smt mult_left_mono mult_nonneg_nonneg mult_right_mono norm_ge_zero)
  then have "(\<Sum>i\<in>F. norm (x i * y i)) \<le> (\<Sum>i\<in>F. norm (x i * x i) + norm (y i * y i))"
    by (simp add: sum_mono)
  also have "\<dots> = (\<Sum>i\<in>F. norm (x i * x i)) + (\<Sum>i\<in>F. norm (y i * y i))"
    by (simp add: sum.distrib)
  also have "\<dots> = (\<Sum>\<^sub>ai\<in>F. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>F. norm (y i * y i))" 
    apply (subst infsetsum_finite[OF \<open>finite F\<close>])+ by rule
  also have "\<dots> \<le> (\<Sum>\<^sub>ai\<in>A. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>A. norm (y i * y i))" 
    apply (rule aux)
     apply (rule infsetsum_mono_neutral_left)
    using \<open>finite F\<close> apply (rule abs_summable_on_finite)
    using x2_sum apply (rule abs_summable_on_normI)
       apply (rule order.refl)
      apply (fact \<open>F \<subseteq> A\<close>)
     apply (rule norm_ge_zero)
    apply (rule infsetsum_mono_neutral_left)
    using \<open>finite F\<close> apply (rule abs_summable_on_finite)
    using y2_sum apply (rule abs_summable_on_normI)
      apply (rule order.refl)
     apply (fact \<open>F \<subseteq> A\<close>)
    by (rule norm_ge_zero)
  also have "\<dots> = B"
    unfolding B_def by simp
  finally show "(\<Sum>i\<in>F. norm (x i * y i)) \<le> B" by assumption
qed

lemma abs_summable_cnj_iff[simp]:
  "(\<lambda>i. cnj (f i)) abs_summable_on A \<longleftrightarrow> f abs_summable_on A"
  apply (subst (1) abs_summable_on_norm_iff[symmetric])
  apply (subst (2) abs_summable_on_norm_iff[symmetric])
  by simp

lemma ennreal_Sup:
  assumes "bdd_above A" and nonempty: "A\<noteq>{}"
  shows "ennreal (Sup A) = Sup (ennreal ` A)"
proof (rule Sup_eqI[symmetric])
  fix y assume "y \<in> ennreal ` A" then show "y \<le> ennreal (Sup A)"
    using assms cSup_upper ennreal_leI by auto
next
  fix y assume asm: "\<And>z. z \<in> ennreal ` A \<Longrightarrow> z \<le> y"
  show "ennreal (Sup A) \<le> y"
  proof (cases y)
    case (real r)
    with asm show ?thesis 
      apply auto
      apply (rule cSup_least)
      using nonempty apply auto
      using ennreal_le_iff by blast
  next
    case top
    then show ?thesis by auto
  qed
qed

lemma infsetsum_nonneg_is_SUPREMUM:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
  assumes fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "infsetsum f A = SUPREMUM {F. finite F \<and> F \<subseteq> A} (sum f)"
proof -
  have sum_F_A: "sum f F \<le> infsetsum f A" if "F : {F. finite F \<and> F \<subseteq> A}" for F
  proof -
    from that have "finite F" and "F \<subseteq> A" by auto
    (* then have summableA: "f abs_summable_on F" by auto *)
    from \<open>finite F\<close> have "sum f F = infsetsum f F" by auto
    also have "\<dots> \<le> infsetsum f A"
      apply (rule infsetsum_mono_neutral_left)
      using fnn summable \<open>F\<subseteq>A\<close> \<open>finite F\<close> by auto
    finally show ?thesis by assumption
  qed
  then have geq: "infsetsum f A \<ge> SUPREMUM {F. finite F \<and> F \<subseteq> A} (sum f)"
    apply (rule_tac cSUP_least) by auto

  define fe where "fe x = ennreal (f x)" for x

  have sum_f_int: "infsetsum f A = \<integral>\<^sup>+ x. fe x \<partial>(count_space A)"
    unfolding infsetsum_def fe_def
    apply (rule nn_integral_eq_integral[symmetric])
    using assms by (simp_all add: abs_summable_on_def AE_count_space)
  also have "\<dots> = (SUP g : {g. finite (g`A) \<and> g \<le> fe}. integral\<^sup>S (count_space A) g)"
    unfolding nn_integral_def simple_function_count_space by simp
  also have "\<dots> \<le> SUPREMUM {F. finite F \<and> F \<subseteq> A} (sum f)"
  proof (rule Sup_least)
    fix x assume "x \<in> integral\<^sup>S (count_space A) ` {g. finite (g ` A) \<and> g \<le> fe}"
    then obtain g where xg: "x = integral\<^sup>S (count_space A) g" and fin_gA: "finite (g`A)" and g_fe: "g \<le> fe" by auto
    define F where "F = {z:A. g z \<noteq> 0}"
    then have "F \<subseteq> A" by simp

    have fin: "finite {z:A. g z = t}" if "t \<noteq> 0" for t
    proof (rule ccontr)
      assume inf: "infinite {z:A. g z = t}"
      then have tgA: "t \<in> g ` A"
        by (metis (mono_tags, lifting) image_eqI not_finite_existsD)
      have "x = (\<Sum>x \<in> g ` A. x * emeasure (count_space A) (g -` {x} \<inter> A))"
        unfolding xg simple_integral_def space_count_space by simp
      also have "\<dots> \<ge> (\<Sum>x \<in> {t}. x * emeasure (count_space A) (g -` {x} \<inter> A))" (is "_ \<ge> \<dots>")
        apply (rule sum_mono2)
        using fin_gA inf tgA by auto
      also have "\<dots> = t * emeasure (count_space A) (g -` {t} \<inter> A)"
        by auto
      also have "\<dots> = t * \<infinity>"
        apply (subst emeasure_count_space_infinite)
        using inf apply auto
        by (smt Collect_cong Int_def vimage_singleton_eq) 
      also have "\<dots> = \<infinity>" using \<open>t \<noteq> 0\<close>
        by (simp add: ennreal_mult_eq_top_iff)
      finally have x_inf: "x = \<infinity>"
        using neq_top_trans by auto

      have "x = integral\<^sup>S (count_space A) g" by (fact xg)
      also have "\<dots> = integral\<^sup>N (count_space A) g"
        by (simp add: fin_gA nn_integral_eq_simple_integral)
      also have "\<dots> \<le> integral\<^sup>N (count_space A) fe"
        using g_fe
        by (simp add: le_funD nn_integral_mono)
      also have "\<dots> < \<infinity>"
        by (metis sum_f_int ennreal_less_top infinity_ennreal_def) 
      finally have x_fin: "x < \<infinity>" by simp

      from x_inf x_fin show False by simp
    qed
    have "finite F"
    proof -
      have F: "F = (\<Union>t\<in>g`A-{0}. {z\<in>A. g z = t})"
        unfolding F_def by auto
      show "finite F"
        unfolding F using fin_gA fin by auto
    qed

    have "x = integral\<^sup>N (count_space A) g"
      unfolding xg
      by (simp add: fin_gA nn_integral_eq_simple_integral)
    also have "\<dots> = set_nn_integral (count_space UNIV) A g"
      by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)
    also have "\<dots> = set_nn_integral (count_space UNIV) F g"
      unfolding F_def indicator_def apply auto
      by (smt mult.right_neutral mult_zero_right nn_integral_cong) 
    also have "\<dots> = integral\<^sup>N (count_space F) g"
      by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)
    also have "\<dots> = sum g F" 
      using \<open>finite F\<close> by (rule nn_integral_count_space_finite)
    also have "sum g F \<le> sum fe F"
      apply (rule sum_mono) using g_fe unfolding le_fun_def by simp
    also have "\<dots> \<le> SUPREMUM {F. finite F \<and> F \<subseteq> A} (sum fe)"
      using \<open>finite F\<close> \<open>F\<subseteq>A\<close>
      by (simp add: SUP_upper)
    also have "\<dots> = SUPREMUM {F. finite F \<and> F \<subseteq> A} (\<lambda>F. ennreal (sum f F))"
      apply (rule SUP_cong[OF refl]) unfolding fe_def apply auto
      by (metis fnn subsetCE sum_ennreal)
    also have "\<dots> = SUPREMUM {F. finite F \<and> F \<subseteq> A} (sum f)"
      apply (subst ennreal_Sup)
      using sum_F_A apply fastforce
      by auto
    finally show "x \<le> ennreal (SUPREMUM {F. finite F \<and> F \<subseteq> A} (sum f))" by simp
  qed
  finally have leq: "infsetsum f A \<le> SUPREMUM {F. finite F \<and> F \<subseteq> A} (sum f)"
    apply (subst ennreal_le_iff[symmetric])
     apply (rule cSUP_upper2[where u=0 and x="{}"])
    using sum_F_A apply fastforce
    by auto

  from leq geq show ?thesis by simp
qed

lemma infsetsum_geq0_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "f abs_summable_on M"
  assumes fnn: "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsetsum f M \<ge> 0" (is "?lhs \<ge> _")
proof -
  have "?lhs \<ge> infsetsum (\<lambda>x. 0) M" (is "_ \<ge> \<dots>")
    apply (rule infsetsum_mono_complex)
    using assms by auto
  also have "\<dots> = 0"
    by auto
  finally show ?thesis by assumption
qed

lemma infsetsum_cmod:
  assumes "f abs_summable_on M"
  assumes fnn: "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsetsum (\<lambda>x. cmod (f x)) M = cmod (infsetsum f M)"
proof -
  have nn: "infsetsum f M \<ge> 0" 
    using assms by (rule infsetsum_geq0_complex) 
  have "infsetsum (\<lambda>x. cmod (f x)) M = infsetsum (\<lambda>x. Re (f x)) M"
    using fnn cmod_eq_Re less_eq_complex_def by auto
  also have "\<dots> = Re (infsetsum f M)"
    using assms(1) infsetsum_Re by blast
  also have "\<dots> = cmod (infsetsum f M)" using nn cmod_eq_Re less_eq_complex_def by auto
  finally show ?thesis by assumption
qed

theorem infsetsum_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes summable: "f abs_summable_on (Sigma A B)"
  shows   "infsetsum f (Sigma A B) = infsetsum (\<lambda>x. infsetsum (\<lambda>y. f (x, y)) (B x)) A"
proof -
  from summable have countable_Sigma: "countable {x \<in> Sigma A B. 0 \<noteq> f x}"
    by (rule abs_summable_countable)
(*   define A' where "A' = {a\<in>A. \<exists>b\<in>B a. 0 \<noteq> f (a,b)}"
  have "countable A"
    using countable_Sigma apply auto *)
  define A' where "A' = fst ` {x \<in> Sigma A B. 0 \<noteq> f x}"
  have countA': "countable A'"
    using countable_Sigma unfolding A'_def by auto

  define B' where "B' a = snd ` ({x \<in> Sigma A B. 0 \<noteq> f x} \<inter> {(a,b) | b. True})" for a
  have countB': "countable (B' a)" for a
    using countable_Sigma unfolding B'_def by auto

  have Sigma_eq: "x \<in> Sigma A B \<longleftrightarrow> x \<in> Sigma A' B'" if "f x \<noteq> 0" for x
    unfolding A'_def B'_def Sigma_def apply auto
    using that by force

  have Sigma'_smaller: "Sigma A' B' \<subseteq> Sigma A B"
    unfolding A'_def B'_def by auto
  with summable have summable': "f abs_summable_on Sigma A' B'"
    using abs_summable_on_subset by blast

  have A'_smaller: "A' \<subseteq> A"
    unfolding A'_def by auto
  have B'_smaller: "B' a \<subseteq> B a" for a
    unfolding B'_def by auto

  have "infsetsum f (Sigma A B) = infsetsum f (Sigma A' B')"
    apply (rule infsetsum_cong_neutral) using Sigma_eq by auto
  also from countA' countB' summable' have "\<dots> = (\<Sum>\<^sub>aa\<in>A'. \<Sum>\<^sub>ab\<in>B' a. f (a, b))"
    by (rule infsetsum_Sigma)
  also have "\<dots> = (\<Sum>\<^sub>aa\<in>A. \<Sum>\<^sub>ab\<in>B' a. f (a, b))" (is "_ = (\<Sum>\<^sub>aa\<in>A. ?inner a)" is "_ = ?rhs")
    apply (rule infsetsum_cong_neutral)
    using A'_smaller apply auto
    unfolding A'_def B'_def Sigma_def apply auto
    by (smt Int_Collect fst_conv image_iff infsetsum_all_0)
  also have "?inner a = (\<Sum>\<^sub>ab\<in>B a. f (a, b))" if "a\<in>A" for a
    apply (rule infsetsum_cong_neutral)
    using that unfolding A'_def B'_def Sigma_def apply auto
    by (smt Int_Collect image_iff mem_Collect_eq snd_conv)
  then have "?rhs = (\<Sum>\<^sub>aa\<in>A. \<Sum>\<^sub>ab\<in>B a. f (a, b))"
    by (rule infsetsum_cong, auto)
  finally show ?thesis 
    by simp
qed

lemma infsetsum_Sigma':
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on (Sigma A B)"
  shows   "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) (B x)) A = infsetsum (\<lambda>(x,y). f x y) (Sigma A B)"
  using assms by (subst infsetsum_Sigma) auto

lemma infsetsum_Times:
  fixes A :: "'a set" and B :: "'b set"
  assumes summable: "f abs_summable_on (A \<times> B)"
  shows   "infsetsum f (A \<times> B) = infsetsum (\<lambda>x. infsetsum (\<lambda>y. f (x, y)) B) A"
  using assms by (subst infsetsum_Sigma) auto

lemma infsetsum_Times':
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on (A \<times> B)"
  shows   "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>(x,y). f x y) (A \<times> B)"
  using assms by (subst infsetsum_Times) auto

lemma infsetsum_swap:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on A \<times> B"
  shows   "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>y. infsetsum (\<lambda>x. f x y) A) B"
proof -
  from summable have summable': "(\<lambda>(x,y). f y x) abs_summable_on B \<times> A"
    by (subst abs_summable_on_Times_swap) auto
  have bij: "bij_betw (\<lambda>(x, y). (y, x)) (B \<times> A) (A \<times> B)"
    by (auto simp: bij_betw_def inj_on_def)
  have "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>(x,y). f x y) (A \<times> B)"
    using summable by (subst infsetsum_Times) auto
  also have "\<dots> = infsetsum (\<lambda>(x,y). f y x) (B \<times> A)"
    by (subst infsetsum_reindex_bij_betw[OF bij, of "\<lambda>(x,y). f x y", symmetric])
       (simp_all add: case_prod_unfold)
  also have "\<dots> = infsetsum (\<lambda>y. infsetsum (\<lambda>x. f x y) A) B"
    using summable' by (subst infsetsum_Times) auto
  finally show ?thesis .
qed


end
