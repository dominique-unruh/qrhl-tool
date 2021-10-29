theory Infinite_Sum_Missing
  imports "HOL-Analysis.Infinite_Sum" "HOL-Library.FuncSet"
begin

lemma has_sum_leq_finite_sums:
  fixes a :: \<open>'a::{comm_monoid_add,topological_space,linorder_topology}\<close>
  assumes \<open>has_sum f A a\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> sum f F \<le> b\<close>
  shows \<open>a \<le> b\<close>
proof -
  from assms(1)
  have 1: \<open>(sum f \<longlongrightarrow> a) (finite_subsets_at_top A)\<close>
    unfolding has_sum_def by -
  from assms(2)
  have 2: \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. sum f F \<le> b\<close>
    by (rule_tac eventually_finite_subsets_at_top_weakI)
  show \<open>a \<le> b\<close>
    using _ _ 1 2
    apply (rule tendsto_le[where f=\<open>\<lambda>_. b\<close>])
    by auto
qed

lemma infsum_leq_finite_sums:
  fixes b :: \<open>'a::{comm_monoid_add,topological_space,linorder_topology}\<close>
  assumes \<open>f summable_on A\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> sum f F \<le> b\<close>
  shows \<open>infsum f A \<le> b\<close>
  by (meson assms(1) assms(2) has_sum_infsum has_sum_leq_finite_sums)

lemma abs_summable_countable:
  assumes \<open>f abs_summable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 0}\<close>
proof -
  have fin: \<open>finite {x\<in>A. norm (f x) \<ge> t}\<close> if \<open>t > 0\<close> for t
  proof (rule ccontr)
    assume *: \<open>infinite {x \<in> A. t \<le> norm (f x)}\<close>
    have \<open>infsum (\<lambda>x. norm (f x)) A \<ge> b\<close> for b
    proof -
      obtain b' where b': \<open>of_nat b' \<ge> b / t\<close>
        by (meson real_arch_simple)
      from *
      obtain F where cardF: \<open>card F \<ge> b'\<close> and \<open>finite F\<close> and F: \<open>F \<subseteq> {x \<in> A. t \<le> norm (f x)}\<close>
        by (meson finite_if_finite_subsets_card_bdd nle_le)
      have \<open>b \<le> of_nat b' * t\<close>
        by (metis (no_types, opaque_lifting) b' less_le_not_le linorder_linear mult.commute mult_left_mono nonzero_mult_div_cancel_left order_refl that times_divide_eq_right)
      also have \<open>\<dots> \<le> of_nat (card F) * t\<close>
        by (simp add: cardF that)
      also have \<open>\<dots> = sum (\<lambda>x. t) F\<close>
        by simp
      also have \<open>\<dots> \<le> sum (\<lambda>x. norm (f x)) F\<close>
        by (metis (mono_tags, lifting) F in_mono mem_Collect_eq sum_mono)
      also have \<open>\<dots> = infsum (\<lambda>x. norm (f x)) F\<close>
        using \<open>finite F\<close> by (rule infsum_finite[symmetric])
      also have \<open>\<dots> \<le> infsum (\<lambda>x. norm (f x)) A\<close>
        apply (rule infsum_mono_neutral)
        using \<open>finite F\<close> assms F by auto
      finally show ?thesis
        by -
    qed
    then show False
      by (meson gt_ex linorder_not_less)
  qed
  have \<open>countable (\<Union>i\<in>{1..}. {x\<in>A. norm (f x) \<ge> 1/of_nat i})\<close>
    apply (rule countable_UN)
    using fin by (auto intro!: countable_finite)
  also have \<open>\<dots> = {x\<in>A. norm (f x) > 0}\<close>
    apply (auto, rename_tac x)
    apply (rule_tac x=\<open>nat (ceiling (1/norm (f x)))\<close> in bexI)
    apply (smt (verit, best) ceiling_divide_upper divide_eq_0_iff linordered_field_class.pos_less_divide_eq mult.commute nat_0_iff of_nat_le_0_iff of_nat_nat zero_le_divide_iff zero_less_norm_iff)
    using not_less_eq_eq by fastforce
  also have \<open>\<dots> = {x\<in>A. f x \<noteq> 0}\<close>
    by auto
  finally show ?thesis
    by -
qed

lemma summable_countable_real:
  fixes f :: \<open>'a \<Rightarrow> real\<close>
  assumes \<open>f summable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 0}\<close>
  using abs_summable_countable assms summable_on_iff_abs_summable_on_real by blast

lemma summable_countable_complex:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>f summable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 0}\<close>
  using abs_summable_countable assms summable_on_iff_abs_summable_on_complex by blast

lemma summable_on_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "(\<lambda>x. f (g x)) summable_on A \<longleftrightarrow> f summable_on B"
proof -
  thm summable_on_reindex
  have \<open>(\<lambda>x. f (g x)) summable_on A \<longleftrightarrow> f summable_on g ` A\<close>
    apply (rule summable_on_reindex[symmetric, unfolded o_def])
    using assms bij_betw_imp_inj_on by blast
  also have \<open>\<dots> \<longleftrightarrow> f summable_on B\<close>
    using assms bij_betw_imp_surj_on by blast
  finally show ?thesis
    by -
qed

lemma infsum_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "infsum (\<lambda>x. f (g x)) A = infsum f B"
proof -
  have \<open>infsum (\<lambda>x. f (g x)) A = infsum f (g ` A)\<close>
    by (metis (mono_tags, lifting) assms bij_betw_imp_inj_on infsum_cong infsum_reindex o_def)
  also have \<open>\<dots> = infsum f B\<close>
    using assms bij_betw_imp_surj_on by blast
  finally show ?thesis
    by -
qed

lemma summable_on_scaleR_left [intro]:
  fixes c :: \<open>'a :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>R c) summable_on A"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. f x *\<^sub>R c) = (\<lambda>y. y *\<^sub>R c) o f\<close>], simp add: o_def)
   apply (rule summable_on_comm_additive)
  using assms by (auto simp add: scaleR_left.additive_axioms)


lemma summable_on_scaleR_right [intro]:
  fixes f :: \<open>'a \<Rightarrow> 'b :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "(\<lambda>x. c *\<^sub>R f x) summable_on A"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. c *\<^sub>R f x) = (\<lambda>y. c *\<^sub>R y) o f\<close>], simp add: o_def)
   apply (rule summable_on_comm_additive)
  using assms by (auto simp add: scaleR_right.additive_axioms)

lemma infsum_scaleR_left:
  fixes c :: \<open>'a :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "infsum (\<lambda>x. f x *\<^sub>R c) A = infsum f A *\<^sub>R c"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. f x *\<^sub>R c) = (\<lambda>y. y *\<^sub>R c) o f\<close>], simp add: o_def)
   apply (rule infsum_comm_additive)
  using assms by (auto simp add: scaleR_left.additive_axioms)

lemma infsum_scaleR_right:
  fixes f :: \<open>'a \<Rightarrow> 'b :: real_normed_vector\<close>
  shows   "infsum (\<lambda>x. c *\<^sub>R f x) A = c *\<^sub>R infsum f A"
proof -
  consider (summable) \<open>f summable_on A\<close> | (c0) \<open>c = 0\<close> | (not_summable) \<open>\<not> f summable_on A\<close> \<open>c \<noteq> 0\<close>
    by auto
  then show ?thesis
  proof cases
    case summable
    then show ?thesis
      apply (subst asm_rl[of \<open>(\<lambda>x. c *\<^sub>R f x) = (\<lambda>y. c *\<^sub>R y) o f\<close>], simp add: o_def)
      apply (rule infsum_comm_additive)
      using summable by (auto simp add: scaleR_right.additive_axioms)
  next
    case c0
    then show ?thesis by auto
  next
    case not_summable
    have \<open>\<not> (\<lambda>x. c *\<^sub>R f x) summable_on A\<close>
    proof (rule notI)
      assume \<open>(\<lambda>x. c *\<^sub>R f x) summable_on A\<close>
      then have \<open>(\<lambda>x. inverse c *\<^sub>R c *\<^sub>R f x) summable_on A\<close>
        using summable_on_scaleR_right by blast
      then have \<open>f summable_on A\<close>
        using not_summable by auto
      with not_summable show False
        by simp
    qed
    then show ?thesis
      by (simp add: infsum_not_exists not_summable(1)) 
  qed
qed

lemma abs_summable_on_Sigma_iff:
  shows   "f abs_summable_on Sigma A B \<longleftrightarrow>
             (\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x) \<and>
             ((\<lambda>x. infsum (\<lambda>y. norm (f (x, y))) (B x)) abs_summable_on A)"
proof (intro iffI conjI ballI)
  assume asm: \<open>f abs_summable_on Sigma A B\<close>
  then have \<open>(\<lambda>x. infsum (\<lambda>y. norm (f (x,y))) (B x)) summable_on A\<close>
    apply (rule_tac summable_on_Sigma_banach)
    by (auto simp: case_prod_unfold)
  then show \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x, y))) abs_summable_on A\<close>
    using summable_on_iff_abs_summable_on_real by force

  show \<open>(\<lambda>y. f (x, y)) abs_summable_on B x\<close> if \<open>x \<in> A\<close> for x
  proof -
    from asm have \<open>f abs_summable_on Pair x ` B x\<close>
      apply (rule summable_on_subset_banach)
      using that by auto
    then show ?thesis
      apply (subst (asm) summable_on_reindex)
      by (auto simp: o_def inj_on_def)
  qed
next
  assume asm: \<open>(\<forall>x\<in>A. (\<lambda>xa. f (x, xa)) abs_summable_on B x) \<and>
    (\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x, y))) abs_summable_on A\<close>
  have \<open>(\<Sum>xy\<in>F. norm (f xy)) \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x, y)))\<close>
    if \<open>F \<subseteq> Sigma A B\<close> and [simp]: \<open>finite F\<close> for F
  proof -
    have [simp]: \<open>(SIGMA x:fst ` F. {y. (x, y) \<in> F}) = F\<close>
      by (auto intro!: set_eqI simp add: Domain.DomainI fst_eq_Domain)
    have [simp]: \<open>finite {y. (x, y) \<in> F}\<close> for x
      by (metis \<open>finite F\<close> Range.intros finite_Range finite_subset mem_Collect_eq subsetI)
    have \<open>(\<Sum>xy\<in>F. norm (f xy)) = (\<Sum>x\<in>fst ` F. \<Sum>y\<in>{y. (x,y)\<in>F}. norm (f (x,y)))\<close>
      apply (subst sum.Sigma)
      by auto
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>{y. (x,y)\<in>F}. norm (f (x,y)))\<close>
      apply (subst infsum_finite)
      by auto
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x,y)))\<close>
      apply (rule infsum_mono)
      apply auto[2]
      apply (rule infsum_mono_neutral)
      using asm that(1) by auto
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x,y)))\<close>
      apply (rule infsum_mono_neutral)
      using asm that(1) summable_on_iff_abs_summable_on_real apply auto
      using infsum_nonneg norm_ge_zero by blast
    finally show ?thesis
      by -
  qed
  then show \<open>f abs_summable_on Sigma A B\<close>
    apply (rule_tac pos_summable_on)
    apply auto
    by (smt (verit, best) bdd_above.unfold image_iff mem_Collect_eq)
qed

lemma abs_summable_on_comparison_test:
  assumes "g abs_summable_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (f x) \<le> norm (g x)"
  shows   "f abs_summable_on A"
proof -
  from assms(1)
  have \<open>sum (\<lambda>x. norm (f x)) F \<le> sum (\<lambda>x. norm (g x)) F\<close> if \<open>F \<subseteq> A\<close> for F
    by (meson assms(2) subsetD sum_mono that)
  also have \<open>\<dots> F = infsum (\<lambda>x. norm (g x)) F\<close> if \<open>finite F\<close> for F
    by (simp add: that)
  also have \<open>\<dots> F \<le> infsum (\<lambda>x. norm (g x)) A\<close> if \<open>F \<subseteq> A\<close> for F
    by (smt (verit, best) Diff_eq_empty_iff assms(1) empty_iff infsum_mono_neutral norm_ge_zero summable_on_subset_banach that)
  finally show ?thesis
    apply (rule_tac pos_summable_on)
    apply auto by fastforce
qed

lemma abs_summable_on_comparison_test':
  assumes "g abs_summable_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (f x) \<le> g x"
  shows   "f abs_summable_on A"
  oops

lemma infsum_Un_Int:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add, t2_space}"
  assumes [simp]: "f summable_on A - B" "f summable_on B - A" \<open>f summable_on A \<inter> B\<close>
  shows   "infsum f (A \<union> B) = infsum f A + infsum f B - infsum f (A \<inter> B)"
proof -
  have [simp]: \<open>f summable_on A\<close>
    apply (subst asm_rl[of \<open>A = (A-B) \<union> (A\<inter>B)\<close>]) apply auto[1]
    apply (rule summable_on_Un_disjoint)
    by auto
  have \<open>infsum f (A \<union> B) = infsum f A + infsum f (B - A)\<close>
    apply (subst infsum_Un_disjoint[symmetric])
    by auto
  moreover have \<open>infsum f B = infsum f (B - A) + infsum f (A \<inter> B)\<close>
    apply (subst infsum_Un_disjoint[symmetric])
       apply auto
    by (metis Int_commute Un_Diff_Int)
  ultimately show ?thesis
    by auto
qed

(*
theorem has_sum_prod_PiE:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {comm_monoid_mult,uniform_space,
                                 topological_semigroup_mult,semiring_0}"
  assumes plus_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x+y)\<close>
  assumes finite: "finite A"
  assumes sums: "\<And>x. x \<in> A \<Longrightarrow> has_sum (f x) (B x) (s x)"
  assumes sums2: \<open>has_sum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B) \<close>
  shows   "has_sum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B) (\<Prod>x\<in>A. s x)"
proof (use finite in induction)
  case empty
  have \<open>has_sum (\<lambda>g. 1) {\<lambda>_. undefined} (\<Sum>\<^sub>\<infinity>x\<in>{\<lambda>_. undefined}. 1)\<close>
    by (metis (mono_tags, lifting) empty_iff finite.intros(1) finite_insert has_sum_infsum infsum_finite sum.empty sum.insert summable_on_finite)
  then show ?case 
    by auto
next
  case (insert x F)
  have pi: \<open>Pi\<^sub>E (insert x F) B = (\<lambda>(g,y). g(x:=y)) ` (Pi\<^sub>E F B \<times> B x)\<close>
    apply (auto simp: case_prod_beta PiE_def)
    apply (auto simp: Pi_def extensional_def image_def)
    by (smt (verit, ccfv_threshold) Int_Collect fun_upd_def fun_upd_triv fun_upd_upd mem_Collect_eq)
  have prod: \<open>(\<Prod>x'\<in>F. f x' ((p(x:=y)) x')) = (\<Prod>x'\<in>F. f x' (p x'))\<close> for p y
    apply (rule prod.cong)
    using insert.hyps by auto

  have inj: \<open>inj_on (\<lambda>(g, y). g(x := y)) (Pi\<^sub>E F B \<times> B x)\<close>
    by (smt (verit, ccfv_threshold) PiE_ext SigmaE fun_upd_same fun_upd_triv fun_upd_twist inj_onI insert.hyps(2) old.prod.case)

  define sxF where \<open>sxF = (\<Prod>x\<in>insert x F. s x)\<close>
  define sF where \<open>sF = (\<Prod>x\<in>F. s x)\<close>

  from insert have \<open>has_sum (\<lambda>g. \<Prod>x\<in>F. f x (g x)) (Pi\<^sub>E F B) sF\<close>
    by (simp only: sF_def)
  then have \<open>has_sum (\<lambda>p. s x * (\<Prod>x'\<in>F. f x' (p x'))) (Pi\<^sub>E F B) (s x * sF)\<close>
    using has_sum_cmult_right by blast
  then have \<open>has_sum (\<lambda>(p,y). f x y * (\<Prod>x'\<in>F. f x' (p x'))) (Pi\<^sub>E F B \<times> B x) sxF\<close>

  have \<open>has_sum (\<Sum>\<^sub>\<infinity>y\<in>B x. f x y) * (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Prod>x'\<in>F. f x' (p x'))\<close>

  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Sum>\<^sub>\<infinity>y\<in>B x. f x y * (\<Prod>x'\<in>F. f x' (p x')))\<close>
    then have \<open>has_sum (\<lambda>(p,y). f x y * (\<Prod>x'\<in>F. f x' (p x'))) (Pi\<^sub>E F B \<times> B x) sxF\<close>
      by -
  then have \<open>has_sum (\<lambda>(p,y). f x y * (\<Prod>x'\<in>F. f x' (p x'))) (Pi\<^sub>E F B \<times> B x) sxF\<close>
    by -
  then have \<open>has_sum (\<lambda>(p,y). f x y * (\<Prod>x'\<in>F. f x' ((p(x:=y)) x'))) (Pi\<^sub>E F B \<times> B x) sxF\<close>
    apply (subst prod) by simp
  then have \<open>has_sum (\<lambda>(p,y). \<Prod>x'\<in>insert x F. f x' ((p(x:=y)) x')) (Pi\<^sub>E F B \<times> B x) sxF\<close>
    apply (subst prod.insert)
    using insert by auto
  then show \<open>has_sum (\<lambda>g. \<Prod>x\<in>insert x F. f x (g x)) (Pi\<^sub>E (insert x F) B) sxF\<close>
    apply (subst pi)
    apply (subst has_sum_reindex)
    using inj by (auto simp: o_def case_prod_unfold)

  have \<open>(\<Sum>\<^sub>\<infinity>g\<in>Pi\<^sub>E (insert x F) B. \<Prod>x\<in>insert x F. f x (g x))
     = (\<Sum>\<^sub>\<infinity>(p,y)\<in>Pi\<^sub>E F B \<times> B x. \<Prod>x'\<in>insert x F. f x' ((p(x:=y)) x'))\<close>
    apply (subst pi)
    apply (subst infsum_reindex)
    using inj by (auto simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(p, y)\<in>Pi\<^sub>E F B \<times> B x. f x y * (\<Prod>x'\<in>F. f x' ((p(x:=y)) x')))\<close>
    apply (subst prod.insert)
    using insert by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(p, y)\<in>Pi\<^sub>E F B \<times> B x. f x y * (\<Prod>x'\<in>F. f x' (p x')))\<close>
    apply (subst prod) by rule (*  *)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Sum>\<^sub>\<infinity>y\<in>B x. f x y * (\<Prod>x'\<in>F. f x' (p x')))\<close>
    apply (subst infsum_Sigma)
       apply (auto simp: )
    apply (simp add: plus_cont)
    by -
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>y\<in>B x. f x y) * (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Prod>x'\<in>F. f x' (p x'))\<close>
    apply (subst infsum_cmult_left)
     defer
    apply (subst infsum_cmult_right)
      defer
      apply simp
    by -
  also have \<open>\<dots> = (\<Prod>x\<in>insert x F. infsum (f x) (B x))\<close>
    using insert by force
  finally show ?case
    by simp
qed
  oops
 *)

theorem infsum_prod_PiE:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {comm_monoid_mult, topological_semigroup_mult, division_ring, banach}"
  assumes finite: "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x summable_on B x"
  assumes "(\<lambda>g. \<Prod>x\<in>A. f x (g x)) summable_on (PiE A B)"
  shows   "infsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B) = (\<Prod>x\<in>A. infsum (f x) (B x))"
proof (use finite assms(2-) in induction)
  case empty
  then show ?case 
    by auto
next
  case (insert x F)
  have pi: \<open>Pi\<^sub>E (insert x F) B = (\<lambda>(g,y). g(x:=y)) ` (Pi\<^sub>E F B \<times> B x)\<close>
    apply (auto simp: case_prod_beta PiE_def)
    apply (auto simp: Pi_def extensional_def image_def)
    by (smt (verit, ccfv_threshold) Int_Collect fun_upd_def fun_upd_triv fun_upd_upd mem_Collect_eq)
  have prod: \<open>(\<Prod>x'\<in>F. f x' ((p(x:=y)) x')) = (\<Prod>x'\<in>F. f x' (p x'))\<close> for p y
    apply (rule prod.cong)
    using insert.hyps by auto

  have inj: \<open>inj_on (\<lambda>(g, y). g(x := y)) (Pi\<^sub>E F B \<times> B x)\<close>
    by (smt (verit, ccfv_threshold) PiE_ext SigmaE fun_upd_same fun_upd_triv fun_upd_twist inj_onI insert.hyps(2) old.prod.case)

  from insert.prems
  have summable1: \<open>(\<lambda>g. \<Prod>x\<in>insert x F. f x (g x)) summable_on Pi\<^sub>E (insert x F) B\<close>
    by -
  then have summable2: \<open>(\<lambda>(p, y). f x y * (\<Prod>x'\<in>F. f x' (p x'))) summable_on Pi\<^sub>E F B \<times> B x\<close>
    apply (subst (asm) pi)
    apply (subst (asm) summable_on_reindex)
    apply (simp add: inj)
    by (smt (verit, del_insts) SigmaE case_prod_conv comp_def fun_upd_def insert.hyps(1) insert.hyps(2) prod.cong prod.insert summable_on_cong)
  then have \<open>(\<lambda>p. \<Sum>\<^sub>\<infinity>y\<in>B x. f x y * (\<Prod>x'\<in>F. f x' (p x'))) summable_on Pi\<^sub>E F B\<close>
    by (rule summable_on_Sigma_banach)
  then have \<open>(\<lambda>p. (\<Sum>\<^sub>\<infinity>y\<in>B x. f x y) * (\<Prod>x'\<in>F. f x' (p x'))) summable_on Pi\<^sub>E F B\<close>
    apply (subst infsum_cmult_left[symmetric])
    using insert.prems(1) by blast
  then have summable3: \<open>(\<lambda>p. (\<Prod>x'\<in>F. f x' (p x'))) summable_on Pi\<^sub>E F B\<close> if \<open>(\<Sum>\<^sub>\<infinity>y\<in>B x. f x y) \<noteq> 0\<close>
    apply (subst (asm) summable_on_cmult_right')
    using that by auto

  have \<open>(\<Sum>\<^sub>\<infinity>g\<in>Pi\<^sub>E (insert x F) B. \<Prod>x\<in>insert x F. f x (g x))
     = (\<Sum>\<^sub>\<infinity>(p,y)\<in>Pi\<^sub>E F B \<times> B x. \<Prod>x'\<in>insert x F. f x' ((p(x:=y)) x'))\<close>
    apply (subst pi)
    apply (subst infsum_reindex)
    using inj by (auto simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(p, y)\<in>Pi\<^sub>E F B \<times> B x. f x y * (\<Prod>x'\<in>F. f x' ((p(x:=y)) x')))\<close>
    apply (subst prod.insert)
    using insert by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(p, y)\<in>Pi\<^sub>E F B \<times> B x. f x y * (\<Prod>x'\<in>F. f x' (p x')))\<close>
    apply (subst prod) by rule
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Sum>\<^sub>\<infinity>y\<in>B x. f x y * (\<Prod>x'\<in>F. f x' (p x')))\<close>
    apply (subst infsum_Sigma_banach[symmetric])
    using summable2 apply blast
    by fastforce
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>y\<in>B x. f x y) * (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Prod>x'\<in>F. f x' (p x'))\<close>
    apply (subst infsum_cmult_left')
    apply (subst infsum_cmult_right')
    by (rule refl)
  also have \<open>\<dots> = (\<Prod>x\<in>insert x F. infsum (f x) (B x))\<close>
    apply (subst prod.insert)
    using \<open>finite F\<close> \<open>x \<notin> F\<close> apply auto[2]
    apply (cases \<open>infsum (f x) (B x) = 0\<close>)
     apply simp
    apply (subst insert.IH)
      apply (simp add: insert.prems(1))
     apply (rule summable3)
    by auto
  finally show ?case
    by simp
qed

theorem infsum_prod_PiE_abs:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {banach, real_normed_div_algebra, comm_semiring_1}"
  assumes finite: "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x abs_summable_on B x"
  shows   "infsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B) = (\<Prod>x\<in>A. infsum (f x) (B x))"
proof (use finite assms(2) in induction)
  case empty
  then show ?case 
    by auto
next
  case (insert x F)

  have pi: \<open>Pi\<^sub>E (insert x F) B = (\<lambda>(g,y). g(x:=y)) ` (Pi\<^sub>E F B \<times> B x)\<close> for F and B :: \<open>'a \<Rightarrow> 'b set\<close> and x
    apply (auto simp: case_prod_beta PiE_def)
    apply (auto simp: Pi_def extensional_def image_def)
    by (smt (verit, ccfv_threshold) Int_Collect fun_upd_def fun_upd_triv fun_upd_upd mem_Collect_eq)
  have prod: \<open>(\<Prod>x'\<in>F. f x' ((p(x:=y)) x')) = (\<Prod>x'\<in>F. f x' (p x'))\<close> for p y
    apply (rule prod.cong)
    using insert.hyps by auto

  have inj: \<open>inj_on (\<lambda>(g, y). g(x := y)) (Pi\<^sub>E F B \<times> B x)\<close>
    by (smt (verit, ccfv_threshold) PiE_ext SigmaE fun_upd_same fun_upd_triv fun_upd_twist inj_onI insert.hyps(2) old.prod.case)

  define s where \<open>s x = infsum (\<lambda>y. norm (f x y)) (B x)\<close> for x

  have *: \<open>(\<Sum>p\<in>P. norm (\<Prod>x\<in>F. f x (p x))) \<le> prod s F\<close> 
    if P: \<open>P \<subseteq> Pi\<^sub>E F B\<close> and [simp]: \<open>finite P\<close> \<open>finite F\<close> 
      and sum: \<open>\<And>x. x \<in> F \<Longrightarrow> f x abs_summable_on B x\<close> for P F
  proof -
    define B' where \<open>B' x = {p x| p. p\<in>P}\<close> for x
    have [simp]: \<open>finite (B' x)\<close> for x
      using that by (auto simp: B'_def)
    have [simp]: \<open>finite (Pi\<^sub>E F B')\<close>
      by (simp add: finite_PiE)
    have [simp]: \<open>P \<subseteq> Pi\<^sub>E F B'\<close>
      using that by (auto simp: B'_def)
    have B'B: \<open>B' x \<subseteq> B x\<close> if \<open>x \<in> F\<close> for x
      unfolding B'_def using P that 
      by auto
    have s_bound: \<open>(\<Sum>y\<in>B' x. norm (f x y)) \<le> s x\<close> if \<open>x \<in> F\<close> for x
      apply (simp_all add: s_def flip: infsum_finite)
      apply (rule infsum_mono_neutral)
      using that sum B'B by auto
    have \<open>(\<Sum>p\<in>P. norm (\<Prod>x\<in>F. f x (p x))) \<le> (\<Sum>p\<in>Pi\<^sub>E F B'. norm (\<Prod>x\<in>F. f x (p x)))\<close>
      apply (rule sum_mono2)
      by auto
    also have \<open>\<dots> = (\<Sum>p\<in>Pi\<^sub>E F B'. \<Prod>x\<in>F. norm (f x (p x)))\<close>
      apply (subst prod_norm[symmetric])
      by simp
    also have \<open>\<dots> = (\<Prod>x\<in>F. \<Sum>y\<in>B' x. norm (f x y))\<close>
    proof (use \<open>finite F\<close> in induction)
      case empty
      then show ?case by simp
    next
      case (insert x F)
      have aux: \<open>a = b \<Longrightarrow> c * a = c * b\<close> for a b c :: real
        by auto
      have inj: \<open>inj_on (\<lambda>(g, y). g(x := y)) (Pi\<^sub>E F B' \<times> B' x)\<close>
        apply (rule inj_onI)
        apply auto
        apply (metis PiE_E fun_upd_triv fun_upd_upd insert.hyps(2))
        by (metis fun_upd_same)
      have \<open>(\<Sum>p\<in>Pi\<^sub>E (insert x F) B'. \<Prod>x\<in>insert x F. norm (f x (p x)))
         =  (\<Sum>(p,y)\<in>Pi\<^sub>E F B' \<times> B' x. \<Prod>x'\<in>insert x F. norm (f x' ((p(x := y)) x')))\<close>
        apply (subst pi)
        apply (subst sum.reindex)
        using inj by (auto simp: case_prod_unfold)
      also have \<open>\<dots> = (\<Sum>(p,y)\<in>Pi\<^sub>E F B' \<times> B' x. norm (f x y) * (\<Prod>x'\<in>F. norm (f x' ((p(x := y)) x'))))\<close>
        apply (subst prod.insert)
        using insert.hyps by (auto simp: case_prod_unfold)
      also have \<open>\<dots> = (\<Sum>(p, y)\<in>Pi\<^sub>E F B' \<times> B' x. norm (f x y) * (\<Prod>x'\<in>F. norm (f x' (p x'))))\<close>
        apply (rule sum.cong)
         apply blast
        unfolding case_prod_unfold
        apply (rule aux)
        apply (rule prod.cong)
        using insert.hyps(2) by auto
      also have \<open>\<dots> = (\<Sum>y\<in>B' x. norm (f x y)) * (\<Sum>p\<in>Pi\<^sub>E F B'. \<Prod>x'\<in>F. norm (f x' (p x')))\<close>
        apply (subst sum_product)
        apply (subst sum.swap)
        apply (subst sum.cartesian_product)
        by simp
      also have \<open>\<dots> = (\<Sum>y\<in>B' x. norm (f x y)) * (\<Prod>x\<in>F. \<Sum>y\<in>B' x. norm (f x y))\<close>
        by (simp add: insert.IH)
      also have \<open>\<dots> = (\<Prod>x\<in>insert x F. \<Sum>y\<in>B' x. norm (f x y))\<close>
        using insert.hyps(1) insert.hyps(2) by force
      finally show ?case
        by -
    qed
    also have \<open>\<dots> = (\<Prod>x\<in>F. \<Sum>\<^sub>\<infinity>y\<in>B' x. norm (f x y))\<close>
      by auto
    also have \<open>\<dots> \<le> (\<Prod>x\<in>F. s x)\<close>
      apply (rule prod_mono)
      apply auto
      apply (simp add: sum_nonneg)
      using s_bound by presburger
    finally show ?thesis
      by -
  qed
  have \<open>(\<lambda>g. \<Prod>x\<in>insert x F. f x (g x)) abs_summable_on Pi\<^sub>E (insert x F) B\<close>
    apply (rule pos_summable_on)
     apply simp
    apply (rule bdd_aboveI[where M=\<open>\<Prod>x'\<in>insert x F. s x'\<close>])
    using * insert.hyps insert.prems by blast
  then have summable2: \<open>(\<lambda>(p, y). f x y * (\<Prod>x'\<in>F. f x' (p x'))) abs_summable_on Pi\<^sub>E F B \<times> B x\<close>
    apply (subst (asm) pi)
    apply (subst (asm) summable_on_reindex)
    apply (simp add: inj)
    by (smt (verit, del_insts) SigmaE case_prod_conv comp_def fun_upd_def insert.hyps(1) insert.hyps(2) prod.cong prod.insert summable_on_cong)

  have \<open>(\<Sum>\<^sub>\<infinity>g\<in>Pi\<^sub>E (insert x F) B. \<Prod>x\<in>insert x F. f x (g x))
     = (\<Sum>\<^sub>\<infinity>(p,y)\<in>Pi\<^sub>E F B \<times> B x. \<Prod>x'\<in>insert x F. f x' ((p(x:=y)) x'))\<close>
    apply (subst pi)
    apply (subst infsum_reindex)
    using inj by (auto simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(p, y)\<in>Pi\<^sub>E F B \<times> B x. f x y * (\<Prod>x'\<in>F. f x' ((p(x:=y)) x')))\<close>
    apply (subst prod.insert)
    using insert by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(p, y)\<in>Pi\<^sub>E F B \<times> B x. f x y * (\<Prod>x'\<in>F. f x' (p x')))\<close>
    apply (subst prod) by rule
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Sum>\<^sub>\<infinity>y\<in>B x. f x y * (\<Prod>x'\<in>F. f x' (p x')))\<close>
    apply (subst infsum_Sigma_banach[symmetric])
    using summable2 abs_summable_summable apply blast
    by fastforce
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>y\<in>B x. f x y) * (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Prod>x'\<in>F. f x' (p x'))\<close>
    apply (subst infsum_cmult_left')
    apply (subst infsum_cmult_right')
    by (rule refl)
  also have \<open>\<dots> = (\<Prod>x\<in>insert x F. infsum (f x) (B x))\<close>
    apply (subst prod.insert)
    using \<open>finite F\<close> \<open>x \<notin> F\<close> apply auto[2]
    apply (cases \<open>infsum (f x) (B x) = 0\<close>)
     apply simp
    apply (subst insert.IH)
      apply (simp add: insert.prems(1))
    by auto
  finally show ?case
    by simp
qed

end
