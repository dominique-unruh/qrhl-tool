chapter \<open>Discrete (subprobability) distributions\<close>

theory Discrete_Distributions
  imports Complex_Main "HOL-Library.Rewrite" "HOL-Analysis.Infinite_Set_Sum" 
    Universe_Instances_Complex_Main
    Extended_Sorry "HOL-Library.Z2" Misc_Missing Multi_Transfer
    "Bounded_Operators-Extra.Extra_Ordered_Fields"
    Infinite_Sums.Infsetsum
begin

definition "is_distribution (f::'a\<Rightarrow>real) \<longleftrightarrow> (\<forall>x. f x \<ge> 0) \<and> f abs_summable_on UNIV \<and> infsetsum f UNIV \<le> 1"

(* typedef 'a distr = "{f::'a\<Rightarrow>real. (\<forall>x. f x \<ge> 0) \<and> (\<forall> M. finite M \<longrightarrow> sum f M \<le> 1)}"  *)
typedef 'a distr = "{f::'a\<Rightarrow>real. is_distribution f}"
  morphisms prob Abs_distr
  unfolding is_distribution_def
  apply (rule exI[of _ "\<lambda>x. 0"]) by auto
setup_lifting type_definition_distr
derive universe distr

lemma is_distribution_def': "is_distribution f \<longleftrightarrow> (\<forall>x. f x \<ge> 0) \<and> (\<forall> M. finite M \<longrightarrow> sum f M \<le> 1)"
proof
  assume f[unfolded is_distribution_def]: "is_distribution f"
  have "sum f M \<le> 1" if [simp]: "finite M" for M
  proof -
    have "sum f M = infsetsum f M"
      using f by simp
    also have "\<dots> \<le> infsetsum f UNIV"
      using f
      by (metis diff_ge_0_iff_ge infsetsum_Diff infsetsum_nonneg top_greatest)
    also have "\<dots> \<le> 1"
      using f by simp
    finally show ?thesis.
  qed
  with f show "(\<forall>x. 0 \<le> f x) \<and> (\<forall>M. finite M \<longrightarrow> sum f M \<le> 1)"
    unfolding is_distribution_def by simp
next
  assume assm: "(\<forall>x. 0 \<le> f x) \<and> (\<forall>M. finite M \<longrightarrow> sum f M \<le> 1)"
  then have "f abs_summable_on UNIV"
    by (rule_tac abs_summable_finite_sumsI[where B=1], simp)
  moreover from assm have "norm (infsetsum f UNIV) \<le> 1"
    by (rule_tac infsetsum_finite_sums_bound, simp_all)
  then have "infsetsum f UNIV \<le> 1"
    by auto
  ultimately show "is_distribution f"
    unfolding is_distribution_def using assm by simp
qed

(* TODO needed? *)
lemma distr_abs_summable_on:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<forall>x. f x \<ge> 0" and "\<forall> M. finite M \<longrightarrow> sum f M \<le> 1"
  shows "f abs_summable_on E"
  apply (rule abs_summable_finite_sumsI)
  using assms by auto

(* TODO needed? *)
lemma distr_infsetsum:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<forall>x. f x \<ge> 0" and "\<forall> M. finite M \<longrightarrow> sum f M \<le> 1"
  shows "infsetsum f UNIV \<le> 1"
proof -
  have \<open>norm (infsetsum f UNIV) \<le> 1\<close>
    apply (rule infsetsum_finite_sums_bound)
    using assms by auto
  then show ?thesis
    by auto
qed


instantiation distr :: (type)zero begin
lift_definition zero_distr :: "'a distr" is "(\<lambda>_. 0)" by (simp add: is_distribution_def)
instance .. 
end

instantiation distr :: (type) scaleR begin
lift_definition scaleR_distr :: "real \<Rightarrow> 'a distr \<Rightarrow> 'a distr"
  is "\<lambda>r \<mu> x. min 1 (max 0 r) * \<mu> x"
proof -
  fix r :: real and \<mu> :: "'a\<Rightarrow>real"
  assume \<mu>: "is_distribution \<mu>"
  define r' where "r' = min 1 (max 0 r)"
  then have r'pos: "r' \<ge> 0" and r'leq1: "r' \<le> 1"
    by auto
  have leq: "(\<Sum>x\<in>M. r' * \<mu> x) \<le> 1" if "finite M" for M :: "'a set"
  proof -
    have "(\<Sum>x\<in>M. r' * \<mu> x) = r' * (\<Sum>x\<in>M. \<mu> x)"
      by (simp add: sum_distrib_left)
    also have "\<dots> \<le> 1"
      using r'leq1 apply (rule mult_le_one)
      using \<mu> by (auto simp: that sum_nonneg is_distribution_def')
    finally show ?thesis by assumption
  qed
  show "is_distribution (\<lambda>x. r' * \<mu> x)"
    unfolding is_distribution_def' apply auto
    using r'pos \<mu> unfolding is_distribution_def' apply simp
    using leq by simp
qed
instance..
end


lift_definition supp :: "'a distr \<Rightarrow> 'a set" is "\<lambda>\<mu>. {x. \<mu> x > 0}" .

lemma "countable (supp \<mu>)"
proof (transfer, auto simp: is_distribution_def)
  fix \<mu> :: "'a => real"
  assume \<mu>pos: "\<forall>x. 0 \<le> \<mu> x" and \<mu>sum: "\<mu> abs_summable_on UNIV"
  from \<mu>sum have "countable {x\<in>UNIV. 0 \<noteq> \<mu> x}" (is "countable ?X")
    by (rule abs_summable_countable)
  also have "?X = {x. 0 < \<mu> x}"
    using less_eq_real_def \<mu>pos by auto 
  finally show "countable {x. 0 < \<mu> x}" 
    by simp 
qed

lift_definition uniform :: "'a set \<Rightarrow> 'a distr" is "\<lambda>M. (\<lambda>m. if m\<in>M then 1/card M else 0)"
proof (rename_tac M, auto simp: is_distribution_def)
  fix M :: "'a set" and x :: 'a
  (* show "0 \<le> (if x \<in> M then 1 / real (card M) else 0)" by auto *)
  have "(\<Sum>m\<in>F. if m \<in> M then 1 / real (card M) else 0) \<le> 1" if "finite F" for F
  proof (cases "finite M")
    case True
    show ?thesis
      apply (subst sum.inter_restrict[symmetric, OF that])
      apply simp
      by (metis Int_lower2 True card_mono divide_le_eq_1 neq0_conv of_nat_0_less_iff of_nat_eq_0_iff of_nat_le_iff)
  next
    case False
    show ?thesis
      apply (subst card.infinite[OF False])
      apply (rewrite asm_rl[of "1/real 0 = 0"]) apply auto[1]
      by auto
  qed
  then show "(\<lambda>m. if m \<in> M then 1 / real (card M) else 0) abs_summable_on UNIV"
    and "(\<Sum>\<^sub>am. if m \<in> M then 1 / real (card M) else 0) \<le> 1"
    by (simp_all add: distr_abs_summable_on distr_infsetsum)
qed


lemma supp_uniform [simp]: "M \<noteq> {} \<Longrightarrow> finite M \<Longrightarrow> supp (uniform M) = M" for M :: "'a set"
  apply transfer apply auto
  using card_gt_0_iff by blast

lemma uniform_infinite: "infinite M \<Longrightarrow> uniform M = 0"
  apply transfer by auto

lemma uniform_empty: "uniform {} = 0"
  apply transfer by simp

lift_definition Prob :: "'a distr \<Rightarrow> 'a set \<Rightarrow> real" is infsetsum .

abbreviation "weight \<mu> == Prob \<mu> UNIV"


lemma weight_supp: 
  assumes "supp \<mu> \<subseteq> S"
  shows "weight \<mu> = Prob \<mu> S"
  using assms apply transfer
  apply (rule infsetsum_cong_neutral)
  apply auto
  by (metis basic_trans_rules(18) is_distribution_def mem_Collect_eq subset_eq)


lemma Prob_empty[simp]: "Prob \<mu> {} = 0"
  apply transfer by simp

lemma Prob_0[simp]: "Prob 0 A = 0"
  apply transfer by simp

lemma Prob_is_0:
  "Prob \<mu> E = 0 \<longleftrightarrow> disjnt (supp \<mu>) E"
proof (transfer fixing: E, unfold is_distribution_def, rule)
  fix \<mu> :: "'a\<Rightarrow>real"
  assume distr: "(\<forall>x. 0 \<le> \<mu> x) \<and> \<mu> abs_summable_on UNIV \<and> infsetsum \<mu> UNIV \<le> 1"
  then have "0 \<le> \<mu> x" for x
      using distr by simp
    from distr have "\<mu> abs_summable_on E"
      using abs_summable_on_subset by blast
  assume sum0: "infsetsum \<mu> E = 0"
  have "\<mu> x = 0" if "x : E" for x
  proof -
    have "\<mu> x = infsetsum \<mu> {x}"
      by simp
    also have "\<dots> \<le> infsetsum \<mu> E"
      apply (rule infsetsum_mono_neutral_left)
      using \<open>\<mu> abs_summable_on E\<close> that distr by auto
    also have "\<dots> = 0"
      by (fact sum0)
    finally show "\<mu> x = 0"
      using \<open>0 \<le> \<mu> x\<close> by simp
  qed
  then show "disjnt {x. 0 < \<mu> x} E"
    using \<open>0 \<le> \<mu> _\<close> unfolding disjnt_def by auto
next
  fix \<mu> :: "'a\<Rightarrow>real"
  assume distr: "(\<forall>x. 0 \<le> \<mu> x) \<and> \<mu> abs_summable_on UNIV \<and> infsetsum \<mu> UNIV \<le> 1"
  assume "disjnt {x. 0 < \<mu> x} E"
  then have "\<mu> x = 0" if "x:E" for x
    unfolding disjnt_def distr
    using distr less_eq_real_def that by auto 
  then show "infsetsum \<mu> E = 0"
    by (rule infsetsum_all_0)
qed

lemma Prob_pos[simp]: "Prob \<mu> E \<ge> 0"
  apply transfer
  by (rule infsetsum_nonneg) (auto simp: is_distribution_def)

lemma Prob_mono:
  assumes "E \<subseteq> F"
  shows "Prob \<mu> E \<le> Prob \<mu> F"
proof (transfer fixing: E F, unfold is_distribution_def)
  fix \<mu> :: "'a \<Rightarrow> real"
  assume distr: "(\<forall>x. 0 \<le> \<mu> x) \<and> \<mu> abs_summable_on UNIV \<and> infsetsum \<mu> UNIV \<le> 1"
  then have "\<mu> abs_summable_on E" and "\<mu> abs_summable_on F"
    using abs_summable_on_subset by blast+
  then show "infsetsum \<mu> E \<le> infsetsum \<mu> F"
    apply (rule infsetsum_mono_neutral_left)
    using assms distr by auto
qed

lemma Prob_leq1[simp]: "Prob \<mu> E \<le> 1"
proof -
  have "Prob \<mu> UNIV \<le> 1"
    apply transfer apply (subst infsetsum_nonneg_is_SUPREMUM_real)
    unfolding is_distribution_def
    using distr_abs_summable_on apply blast
     apply simp
    using infsetsum_nonneg_is_SUPREMUM_real by fastforce
  then show ?thesis
    using Prob_mono[of E UNIV \<mu>] by auto
qed

lemma weight_uniform[simp]: "weight (uniform M) = (if M \<noteq> {} \<and> finite M then 1 else 0)"
proof -
  have "weight (uniform M) = 0" if "\<not> (M \<noteq> {} \<and> finite M)"
  proof -
    from that have "card M = 0"
      using card.empty card.infinite by blast
    then show ?thesis
      apply (transfer fixing: M)
      by (simp add: infsetsum_all_0)
  qed
  moreover have "weight (uniform M) = 1" if "M \<noteq> {}" and "finite M"
  proof (transfer fixing: M)
    from that have "(\<Sum>\<^sub>ax\<in>M. 1 / real (card M)) = 1"
      by (subst infsetsum_finite, auto)
    then show "(\<Sum>\<^sub>am. if m \<in> M then 1 / real (card M) else 0) = 1"
      by (subst infsetsum_cong_neutral[where B=M], auto)
  qed
  ultimately show ?thesis
    by auto
qed

lift_definition "map_distr" :: "('a\<Rightarrow>'b) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" 
  is "\<lambda>(f::'a\<Rightarrow>'b) \<mu> x. infsetsum \<mu> (f -` {x})"
proof (auto simp: is_distribution_def)
  fix f :: "'a \<Rightarrow> 'b" and \<mu> :: "'a \<Rightarrow> real" and x and M :: "'b set"
  assume "(\<forall>x. 0 \<le> \<mu> x)" and summable: "\<mu> abs_summable_on UNIV" and sum: "infsetsum \<mu> UNIV \<le> 1"
  then have \<mu>pos: "0 \<le> \<mu> x" for x by simp

  have reindex: "bij_betw snd (SIGMA x:M. f -` {x}) (f -` M)" for M
    by (rule bij_betwI, auto)

  have "0 = infsetsum (\<lambda>_. 0) (f -` {x})" by simp
  also have "\<dots> \<le> infsetsum \<mu> (f -` {x})"
    apply (rule infsetsum_mono_neutral_left)
    using abs_summable_on_subset[OF summable] \<mu>pos by auto
  finally show "0 \<le> infsetsum \<mu> (f -` {x})" .


  {fix M :: "'b set" assume "finite M"
  then have "(\<Sum>x\<in>M. infsetsum \<mu> (f -` {x})) = (\<Sum>\<^sub>ax\<in>M. infsetsum \<mu> (f -` {x}))" (is "?lhs = _")
    by simp
  also have "\<dots> = (\<Sum>\<^sub>a(x, y)\<in>(SIGMA x:M. f -` {x}). \<mu> y)"
    apply (rule infsetsum_Sigma')
    unfolding case_prod_beta
    apply (rule abs_summable_on_reindex_bij_betw[OF reindex, THEN iffD2])
    using abs_summable_on_subset[OF summable] by simp
  also have "\<dots> = infsetsum \<mu> (f -` M)"
    unfolding case_prod_beta
    by (rule infsetsum_reindex_bij_betw[OF reindex])
  also have "\<dots> \<le> infsetsum \<mu> UNIV"
    apply (rule infsetsum_mono_neutral_left)
    using abs_summable_on_subset[OF summable] \<mu>pos by auto
  also have "\<dots> \<le> 1"
    by (fact sum)
  finally have "?lhs \<le> 1" .}
  then show "(\<lambda>x. infsetsum \<mu> (f -` {x})) abs_summable_on UNIV"
    and "(\<Sum>\<^sub>ax. infsetsum \<mu> (f -` {x})) \<le> 1"
    using \<mu>pos by (auto intro!: infsetsum_nonneg distr_abs_summable_on distr_infsetsum)
qed

lemma Prob_map_distr:
  "Prob \<mu> S = prob (map_distr (\<lambda>x. x\<in>S) \<mu>) True"
  apply (transfer fixing: S)
  apply (rewrite asm_rl[of "((\<lambda>x. x \<in> S) -` {True}) = S"])
  by auto

lemma map_distr_0[simp]: "map_distr f 0 = 0"
  by (transfer, simp)

lemma weight_map_distr[simp]: "weight (map_distr f \<mu>) = weight \<mu>"
proof (transfer, auto simp: is_distribution_def)
  fix f :: "'b \<Rightarrow> 'a" and \<mu> :: "'b => real"
  assume \<mu>pos: "\<forall>x. 0 \<le> \<mu> x" and summable: "\<mu> abs_summable_on UNIV" and "infsetsum \<mu> UNIV \<le> 1"
  have reindex: "bij_betw snd (SIGMA x:UNIV. f -` {x}) UNIV"
    by (rule bij_betwI, auto)
  show "(\<Sum>\<^sub>ax. infsetsum \<mu> (f -` {x})) = infsetsum \<mu> UNIV"
    apply (subst infsetsum_Sigma')
    unfolding case_prod_beta
    using reindex summable apply (rule abs_summable_on_reindex_bij_betw[THEN iffD2])
    using reindex by (subst infsetsum_reindex_bij_betw, auto)
qed

lemma supp_map_distr[simp]: "supp (map_distr f \<mu>) = f ` (supp \<mu>)"
proof (transfer, auto simp: is_distribution_def)
  fix f :: "'b \<Rightarrow> 'a" and \<mu> :: "'b \<Rightarrow> real" and x :: 'a and y :: 'b
  assume \<mu>pos: "\<forall>x. 0 \<le> \<mu> x" and summable: "\<mu> abs_summable_on UNIV" and "infsetsum \<mu> UNIV \<le> 1"
  show "0 < infsetsum \<mu> (f -` {x}) \<Longrightarrow> x \<in> f ` {x. 0 < \<mu> x}"
    using \<mu>pos by (smt image_iff infsetsum_all_0 mem_Collect_eq vimage_singleton_eq)
  show "0 < infsetsum \<mu> (f -` {f y})" if "0 < \<mu> y"
  proof -
    from that have "0 < \<mu> y".
    also have "\<dots> = infsetsum \<mu> {y}"
      by simp
    also have "\<dots> \<le> infsetsum \<mu> (f -` {f y})"
      apply (rule infsetsum_mono_neutral_left)
      using abs_summable_on_subset[OF summable] \<mu>pos by auto
    finally show ?thesis .
  qed
qed

lemma map_distr_id[simp]: "map_distr (\<lambda>x. x) \<mu> = \<mu>"
  by (transfer, auto)

lemma map_distr_uniform[simp]: 
  fixes f::"'a\<Rightarrow>'b" 
  assumes bij: "bij_betw f A B"
  shows "map_distr f (uniform A) = uniform B"
proof (cases "finite A", transfer fixing: f A B, rule ext)
  fix x
  case True
  with bij have "finite B"
    using bij_betw_finite by blast
  from bij have cardAB[simp]: "card A = card B"
    using bij_betw_same_card by blast
  show "(\<Sum>\<^sub>am\<in>f -` {x}. if m \<in> A then 1 / real (card A) else 0) = (if x \<in> B then 1 / real (card B) else 0)" 
     (is "?lhs = ?rhs")
  proof (cases "x \<in> B")
    case True
    define R where "R = (f -` {x}) \<inter> -A"
    from True bij obtain y where inv_f: "f -` {x} = {y} \<union> R" and yA: "y \<in> A"
      apply atomize_elim unfolding R_def by (auto simp: bij_betw_def inj_on_def)
    have "?lhs = (\<Sum>\<^sub>am\<in>{y}. if m \<in> A then 1 / real (card A) else 0)"
      unfolding inv_f apply (rule infsetsum_cong_neutral)
      by (auto simp: R_def)
    also have "\<dots> = 1 / real (card A)"
      using yA by auto
    also have "\<dots> = ?rhs"
      using True by simp
    finally show ?thesis .
  next
    case False
    then have rhs: "?rhs = 0" by simp
    from False have yA: "y \<in> f -` {x} \<Longrightarrow> y \<notin> A" for y 
      using bij bij_betwE by blast
    have "?lhs = (\<Sum>\<^sub>am\<in>f -` {x}. 0)"
      apply (rule infsetsum_cong)
      using yA by auto
    also have "\<dots> = 0"
      by auto
    finally have "?lhs = 0" .
    with rhs show ?thesis by simp
  qed
next
  assume "infinite A"
  moreover with assms have "infinite B"
    using bij_betw_finite by auto
  ultimately have "uniform A = 0" and "uniform B = 0"
    by (simp_all add: uniform_infinite)
  then show ?thesis 
    by simp
qed


lemma compose_map_distr[simp]:
  fixes f::"'a\<Rightarrow>'b" and g::"'b\<Rightarrow>'c"
  shows "map_distr g (map_distr f \<mu>) = map_distr (\<lambda>x. g (f x)) \<mu>"  
proof (transfer fixing: f g, rule ext, unfold is_distribution_def)
  fix \<mu> :: "'a => real" and x
  assume "(\<forall>x. 0 \<le> \<mu> x) \<and> \<mu> abs_summable_on UNIV \<and> infsetsum \<mu> UNIV \<le> 1"
  then have \<mu>pos: "\<forall>x. 0 \<le> \<mu> x" and summable: "\<mu> abs_summable_on UNIV" and "infsetsum \<mu> UNIV \<le> 1"
    by auto
  have reindex0: "bij_betw snd (SIGMA x:UNIV. f -` {x}) UNIV"
    by (rule bij_betwI, auto)
  have reindex: "bij_betw snd (SIGMA y:g -` {x}. f -` {y}) (f -` g -` {x})"
    by (rule bij_betwI, auto)

  have summable1: "(\<lambda>(x, y). \<mu> y) abs_summable_on (SIGMA y:g -` {x}. f -` {y})"
    unfolding case_prod_beta
    apply (rule abs_summable_on_reindex_bij_betw[OF reindex, THEN iffD2])
    using summable abs_summable_on_subset by blast

  have "(\<Sum>\<^sub>ax\<in>g -` {x}. infsetsum \<mu> (f -` {x})) = infsetsum \<mu> (f -` g -` {x})" (is "?lhs = _")
    apply (subst infsetsum_Sigma')
     apply (rule summable1)
    unfolding case_prod_beta
    by (subst infsetsum_reindex_bij_betw[OF reindex], simp)

  also have "\<dots> = infsetsum \<mu> ((\<lambda>x. g (f x)) -` {x})" (is "_ = ?rhs")
    by (simp add: vimage_def) 
  finally show "?lhs = ?rhs" .
qed

functor map_distr: map_distr using map_distr_id compose_map_distr unfolding o_def id_def by auto


(* lift_definition expectation :: "'a distr \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> 'b::{banach, second_countable_topology}" is
  "\<lambda>\<mu> f. infsetsum (\<lambda>x. \<mu> x *\<^sub>R f x) UNIV" . *)
lift_definition expectation :: "'a distr \<Rightarrow> 'a::{banach, second_countable_topology}" is
  "\<lambda>\<mu>. infsetsum (\<lambda>x. \<mu> x *\<^sub>R x) UNIV" .

lift_definition expectation_exists :: "'b::{banach, second_countable_topology} distr \<Rightarrow> bool" is
  "\<lambda>\<mu>. (\<lambda>x. \<mu> x *\<^sub>R x) abs_summable_on UNIV" .


abbreviation "expectation' \<mu> f == expectation (map_distr f \<mu>)"
abbreviation "expectation_exists' \<mu> f == expectation_exists (map_distr f \<mu>)"



lemma expectation_exists_bounded:
  fixes a b :: real
  assumes "\<And>x. x\<in>supp \<mu> \<Longrightarrow> x \<ge> a"
  assumes "\<And>x. x\<in>supp \<mu> \<Longrightarrow> x \<le> b"
  shows "expectation_exists \<mu>"
proof (insert assms, transfer fixing: a b, unfold is_distribution_def)
  fix \<mu> :: "real \<Rightarrow> real"
  define \<mu>f where "\<mu>f x = \<mu> x *\<^sub>R x" for x
  obtain B where "B \<ge> -a" and "B \<ge> b" and "B \<ge> 0"
    by (meson linear order_trans)
  assume distr: "(\<forall>x. 0 \<le> \<mu> x) \<and> \<mu> abs_summable_on UNIV \<and> infsetsum \<mu> UNIV \<le> 1"
  then have \<mu>pos: "\<mu> x \<ge> 0" for x by auto
  from distr have sum: "sum \<mu> F \<le> 1" if "finite F" for F
    using is_distribution_def is_distribution_def' that by blast
  assume "(\<And>x. x \<in> {x. 0 < \<mu> x} \<Longrightarrow> a \<le> x)"
  then have fx1: "x \<ge> -B" if "0 < \<mu> x" for x
    using that \<open>- a \<le> B\<close> by force
  assume "(\<And>x. x \<in> {x. 0 < \<mu> x} \<Longrightarrow> x \<le> b)"
  then have fx2: "x \<le> B" if "0 < \<mu> x" for x
    using that \<open>b \<le> B\<close> order.trans by auto
  have B: "norm (\<mu>f x) \<le> B * \<mu> x" for x
    apply (cases "\<mu> x > 0", auto simp: \<mu>f_def intro!: abs_leI)
    using fx1[of x] fx2[of x] \<mu>pos[of x] apply auto
    using nice_ordered_field_class.pos_minus_divide_le_eq by fastforce
  have "(\<Sum>x\<in>F. norm (\<mu>f x)) \<le> B" if "finite F" for F
  proof -
    have "(\<Sum>x\<in>F. norm (\<mu>f x)) \<le> (\<Sum>x\<in>F. B * \<mu> x)"
      using B
      by (simp add: sum_mono)
    also have "\<dots> \<le> B * (\<Sum>x\<in>F. \<mu> x)"
      by (simp add: sum_distrib_left)
    also have "\<dots> \<le> B * 1"
      apply (rule mult_left_mono)
      using that sum \<open>B\<ge>0\<close> by simp_all
    finally show ?thesis by simp
  qed
  then show "\<mu>f abs_summable_on UNIV"
    by (rule abs_summable_finite_sumsI)
qed

lemma not_expectation_exists:
  assumes "\<not> expectation_exists \<mu>"
  shows "expectation \<mu> = 0"
  using assms apply transfer
  using not_summable_infsetsum_eq by blast

lemma expectation_exists_map_distr:
  "expectation_exists (map_distr f \<mu>) \<longleftrightarrow> (\<lambda>x. prob \<mu> x *\<^sub>R f x) abs_summable_on UNIV"
proof -
  have [simp]: "prob \<mu> abs_summable_on U" for U
    using abs_summable_on_subset is_distribution_def prob by fastforce
  have \<mu>_scaleR_summ: "(\<lambda>y. prob \<mu> y *\<^sub>R norm x) abs_summable_on f -` {x}" for x
    apply (rule abs_summable_on_scaleR_left) by auto

  have "expectation_exists (map_distr f \<mu>) \<longleftrightarrow> (\<lambda>x. (\<Sum>\<^sub>ay\<in>(f -` {x}). prob \<mu> y) *\<^sub>R x) abs_summable_on UNIV"
    apply transfer by simp
  also have "\<dots> \<longleftrightarrow> (\<lambda>x. norm ((\<Sum>\<^sub>ay\<in>(f -` {x}). prob \<mu> y) *\<^sub>R x)) abs_summable_on UNIV"
    using abs_summable_on_norm_iff by fastforce
  also have "\<dots> \<longleftrightarrow> (\<lambda>x. (\<Sum>\<^sub>ay\<in>(f -` {x}). prob \<mu> y) *\<^sub>R norm x) abs_summable_on UNIV"
    by (smt abs_summable_on_comparison_test norm_scaleR real_scaleR_def)
  also have "\<dots> \<longleftrightarrow> (\<lambda>x. (\<Sum>\<^sub>ay\<in>(f -` {x}). prob \<mu> y *\<^sub>R norm x)) abs_summable_on UNIV"
    apply (subst infsetsum_scaleR_left) by auto
  also have "\<dots> \<longleftrightarrow> (\<lambda>(x,y). prob \<mu> y *\<^sub>R norm x) abs_summable_on Sigma UNIV (\<lambda>x. f -` {x})"
    apply (subst abs_summable_on_Sigma_iff)
    using \<mu>_scaleR_summ apply simp
    apply (subst abs_pos) 
     apply (metis is_distribution_def mem_Collect_eq mult_nonneg_nonneg norm_ge_zero prob)
    by simp
  also have "\<dots> \<longleftrightarrow> (\<lambda>(x,y). prob \<mu> y *\<^sub>R norm (f y)) abs_summable_on Sigma UNIV (\<lambda>x. f -` {x})"
    apply (subst abs_summable_on_cong)
    by auto
  also have "\<dots> \<longleftrightarrow> (\<lambda>x. prob \<mu> x *\<^sub>R norm (f x)) abs_summable_on UNIV"
    apply (subst abs_summable_on_reindex_bij_betw[where A="Sigma UNIV (\<lambda>x. f -` {x})" and g=snd, symmetric])
     apply (rule bij_betwI')
    by (auto simp add: case_prod_beta)
  also have "\<dots> \<longleftrightarrow> (\<lambda>x. norm (prob \<mu> x *\<^sub>R f x)) abs_summable_on UNIV"
    apply (rule abs_summable_on_cong)
    apply auto
    by (metis abs_of_nonneg is_distribution_def mem_Collect_eq prob)
  thm abs_summable_on_cong
  also have "\<dots> \<longleftrightarrow> (\<lambda>x. prob \<mu> x *\<^sub>R f x) abs_summable_on UNIV"
    by (rule abs_summable_on_norm_iff)
  finally show ?thesis
    by -
qed


(* lemma expectation_exists_map_distr:
  assumes "expectation_exists (map_distr f \<mu>)"
  shows "(\<lambda>x. prob \<mu> x *\<^sub>R f x) abs_summable_on UNIV"
proof -
  have [simp]: "prob \<mu> abs_summable_on U" for U
    using abs_summable_on_subset is_distribution_def prob by fastforce
  have \<mu>_scaleR_summ: "(\<lambda>y. prob \<mu> y *\<^sub>R norm x) abs_summable_on f -` {x}" for x
    apply (rule abs_summable_on_scaleR_left) by auto

  from assms have "(\<lambda>x. (\<Sum>\<^sub>ay\<in>(f -` {x}). prob \<mu> y) *\<^sub>R x) abs_summable_on UNIV"
    apply transfer by simp
  then have "(\<lambda>x. norm ((\<Sum>\<^sub>ay\<in>(f -` {x}). prob \<mu> y) *\<^sub>R x)) abs_summable_on UNIV"
    using abs_summable_on_norm_iff by fastforce
  then have "(\<lambda>x. (\<Sum>\<^sub>ay\<in>(f -` {x}). prob \<mu> y) *\<^sub>R norm x) abs_summable_on UNIV"
    by (smt abs_summable_on_comparison_test norm_scaleR real_scaleR_def)
  then have "(\<lambda>x. (\<Sum>\<^sub>ay\<in>(f -` {x}). prob \<mu> y *\<^sub>R norm x)) abs_summable_on UNIV"
    apply (subst infsetsum_scaleR_left) by auto
  then have "(\<lambda>(x,y). prob \<mu> y *\<^sub>R norm x) abs_summable_on Sigma UNIV (\<lambda>x. f -` {x})"
    apply (subst abs_summable_on_Sigma_iff)
    using \<mu>_scaleR_summ apply auto
    apply (subst abs_pos) apply auto
    by (metis is_distribution_def mem_Collect_eq mult_nonneg_nonneg norm_ge_zero prob)
  then have "(\<lambda>(x,y). prob \<mu> y *\<^sub>R norm (f y)) abs_summable_on Sigma UNIV (\<lambda>x. f -` {x})"
    apply (rule abs_summable_on_cong[THEN iffD1, rotated -1])
    by auto
  then have "(\<lambda>x. prob \<mu> x *\<^sub>R norm (f x)) abs_summable_on UNIV"
    apply (subst abs_summable_on_reindex_bij_betw[where A="Sigma UNIV (\<lambda>x. f -` {x})" and g=snd, symmetric])
     apply (rule bij_betwI')
    by (auto simp add: case_prod_beta)
  then have "(\<lambda>x. norm (prob \<mu> x *\<^sub>R f x)) abs_summable_on UNIV"
    by (simp add: abs_summable_on_comparison_test)
  then show "(\<lambda>x. prob \<mu> x *\<^sub>R f x) abs_summable_on UNIV"
    by (simp add: abs_summable_on_comparison_test')
qed*)

lemma expectation_map_distr:
  (* assumes "(\<lambda>x. prob \<mu> x *\<^sub>R f x) abs_summable_on UNIV" *)
  shows "expectation (map_distr f \<mu>) = infsetsum (\<lambda>x. prob \<mu> x *\<^sub>R f x) UNIV"
proof (cases "expectation_exists (map_distr f \<mu>)")
  case False
  then have "expectation (map_distr f \<mu>) = 0"
    by (rule not_expectation_exists)
  moreover
  from False have "\<not> (\<lambda>x. prob \<mu> x *\<^sub>R f x) abs_summable_on UNIV"
    by (subst expectation_exists_map_distr[symmetric], metis)
  then have "infsetsum (\<lambda>x. prob \<mu> x *\<^sub>R f x) UNIV = 0"
    by (simp add: not_summable_infsetsum_eq)
  ultimately show ?thesis 
    by simp
next
  case True
  from expectation_exists_map_distr[THEN iffD1, OF True] show ?thesis
  proof (transfer fixing: f)
    fix \<mu> :: "'b \<Rightarrow> real"
    assume "is_distribution \<mu>"
    then have [simp]: "\<mu> abs_summable_on U" for U
      unfolding is_distribution_def
      using abs_summable_on_subset by blast
    assume \<mu>f_summable: "(\<lambda>x. \<mu> x *\<^sub>R f x) abs_summable_on UNIV"

    have "(\<Sum>\<^sub>ax. (\<Sum>\<^sub>ay\<in>f -` {x}. \<mu> y) *\<^sub>R x) = (\<Sum>\<^sub>ax. (\<Sum>\<^sub>ay\<in>f -` {x}. \<mu> y *\<^sub>R x))"
      (is "_ = ?rhs")
      apply (rule infsetsum_cong, simp_all)
      apply (rule infsetsum_scaleR_left[symmetric])
      by simp
    also 
    have bij: "bij_betw (\<lambda>x. (f x, x)) UNIV (SIGMA x:UNIV. f -` {x})"
      by (rule bij_betwI', auto)
    have "(\<lambda>(x, y). \<mu> y *\<^sub>R x) abs_summable_on (SIGMA x:UNIV. f -` {x})"
      apply (rule abs_summable_on_reindex_bij_betw[where A=UNIV and g="\<lambda>x. (f x, x)", THEN iffD1])
      using bij \<mu>f_summable by auto
    then have "?rhs = (\<Sum>\<^sub>a(x, y)\<in>(SIGMA x:UNIV. f -` {x}). \<mu> y *\<^sub>R x)"
      by (rule infsetsum_Sigma')
    also have "\<dots> = (\<Sum>\<^sub>ax. \<mu> x *\<^sub>R f x)"
      apply (subst infsetsum_reindex_bij_betw[where A=UNIV and g="\<lambda>x. (f x, x)", symmetric])
      using bij by auto
    finally show "(\<Sum>\<^sub>ax. (\<Sum>\<^sub>ay\<in>f -` {x}. \<mu> y) *\<^sub>R x) = (\<Sum>\<^sub>ax. \<mu> x *\<^sub>R f x)"
      by -
  qed
qed

lemma expectation_mono:
  fixes f :: "'a\<Rightarrow>real"
  assumes ee_f: "expectation_exists (map_distr f \<mu>)"
  assumes ee_g: "expectation_exists (map_distr g \<mu>)"
  assumes leq: "\<And>x. x\<in>supp \<mu> \<Longrightarrow> f x \<le> g x"
  shows "expectation (map_distr f \<mu>) \<le> expectation (map_distr g \<mu>)"
proof -
(*   assume \<mu>pos: "\<forall>x. 0 \<le> \<mu> x" and summable: "\<mu> abs_summable_on UNIV" and "infsetsum \<mu> UNIV \<le> 1"
  then have pos: "\<mu> x \<ge> 0" for x by simp
  assume leq: "(\<And>x. 0 < \<mu> x \<Longrightarrow> f x \<le> g x)" *)
  have leq': "prob \<mu> x * f x \<le> prob \<mu> x * g x" for x
    apply (cases "prob \<mu> x = 0")
     apply simp
    using leq[of x]
    by (metis is_distribution_def less_eq_real_def mem_Collect_eq mult.commute mult_right_mono prob supp.rep_eq)
  from ee_f have sumf: "(\<lambda>x. prob \<mu> x * f x) abs_summable_on UNIV"
    apply (subst (asm) expectation_exists_map_distr) by fastforce
  from ee_g have sumg: "(\<lambda>x. prob \<mu> x * g x) abs_summable_on UNIV"
    apply (subst (asm) expectation_exists_map_distr) by fastforce
  from sumf sumg leq' 
  show ?thesis
    unfolding expectation_map_distr
    apply (rule_tac infsetsum_mono)
    by auto
qed


lemma prob_uniform[simp]: "prob (uniform M) m = (if m\<in>M then 1/card M else 0)"
  apply transfer by simp

abbreviation "point_distr x \<equiv> uniform {x}"
lemma expectation_point_distr[simp]: "expectation (point_distr x) = x"
  apply (transfer fixing: x)
  apply (subst infsetsum_cong_neutral[where B="{x}"])
  by auto


lift_definition "bind_distr" :: "'a distr \<Rightarrow> ('a \<Rightarrow> 'b distr) \<Rightarrow> 'b distr" 
  is "\<lambda>(\<mu>::'a\<Rightarrow>real) (f::'a\<Rightarrow>'b\<Rightarrow>real) x. \<Sum>\<^sub>a y\<in>UNIV. \<mu> y * f y x"
  by (cheat bind_distr)

abbreviation "product_distr \<mu> \<nu> \<equiv> bind_distr \<mu> (\<lambda>z. map_distr (Pair z) \<nu>)"

lemma product_distr_0_left[simp]: "product_distr 0 \<nu> = 0"
  apply transfer by simp
lemma product_distr_0_right: "product_distr \<mu> 0 = 0"
  apply transfer by simp
lemmas product_distr_0_right'[simp] = product_distr_0_right[simplified]

lemma distr_eqI:
  assumes "\<And>x. prob \<mu> x = prob \<nu> x"
  shows "\<mu> = \<nu>"
  using assms apply transfer by auto

lemma prob_product[simp]: "prob (product_distr \<mu> \<nu>) (x,y) = prob \<mu> x * prob \<nu> y"
proof (transfer fixing: x y)
  fix \<mu> :: "'a\<Rightarrow>real" and \<nu> :: "'b\<Rightarrow>real"
  have nonx: "(Pair x' -` {(x, y)}) = {}" if "x'\<noteq>x" for x'
    using that by blast
  have isx: "(Pair x -` {(x, y)}) = {y}"
    by blast
  have "(\<Sum>\<^sub>a x'. \<mu> x' * infsetsum \<nu> (Pair x' -` {(x, y)})) = (\<Sum>\<^sub>a x'\<in>{x}. \<mu> x' * infsetsum \<nu> (Pair x' -` {(x, y)}))" (is "?lhs = _")
    apply (rule infsetsum_cong_neutral) using nonx by auto
  also have "\<dots> = \<mu> x * infsetsum \<nu> (Pair x -` {(x, y)})"
    by simp
  also have "\<dots> = \<mu> x * \<nu> y"
    by (simp add: isx)
  finally show "?lhs = \<mu> x * \<nu> y"
    by simp
qed

lemma product_distr_uniform[simp]:
  shows "product_distr (uniform A) (uniform B) = uniform (A\<times>B)"
proof -
  have "prob (uniform A) a * prob (uniform B) b = prob (uniform (A \<times> B)) (a, b)" for a b
    by (simp add: card_cartesian_product)
  then show ?thesis
    by (auto intro: distr_eqI)
qed

lemma expectation_uminus: "expectation (map_distr (\<lambda>x. -f x) \<mu>) = - expectation (map_distr f \<mu>)"
  unfolding expectation_map_distr
  apply (transfer fixing: f)
  apply auto
  by (simp add: infsetsum_uminus)

lemma expectation_upper_bound:
  fixes \<mu> :: "real distr"
  assumes "weight \<mu> = 1 \<or> B \<ge> 0"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> x \<ge> C"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> x \<le> B"
  shows "expectation \<mu> \<le> B"
  using assms 
proof (transfer fixing: B C, unfold is_distribution_def)
  fix \<mu> :: "real\<Rightarrow>real"
  assume \<mu>1_or_Bpos: "infsetsum \<mu> UNIV = 1 \<or> 0 \<le> B"
  assume \<mu>: "(\<forall>x. 0 \<le> \<mu> x) \<and> \<mu> abs_summable_on UNIV \<and> infsetsum \<mu> UNIV \<le> 1"
  then have \<mu>sum: "\<mu> abs_summable_on UNIV" and \<mu>sum1: "infsetsum \<mu> UNIV \<le> 1" and \<mu>pos: "\<mu> x \<ge> 0" for x
    by simp_all
  obtain BC where "BC\<ge>B" and "BC\<ge>-C" and "BC\<ge>0" 
    apply atomize_elim
    by (meson linorder_linear order_trans_rules(23))
  assume "(\<And>x. x \<in> {x. 0 < \<mu> x} \<Longrightarrow> C \<le> x)" 
    and B0: "(\<And>x. x \<in> {x. 0 < \<mu> x} \<Longrightarrow> x \<le> B)"
  then have abs_fx: "abs x \<le> BC" if "\<mu> x \<noteq> 0" for x
    by (smt \<mu>pos \<open>- C \<le> BC\<close> \<open>B \<le> BC\<close> mem_Collect_eq that)
  then have abs_f\<mu>x: "abs (\<mu> x * x) \<le> \<mu> x * BC" for x
    by (metis \<mu>pos abs_mult abs_pos mult.commute mult_eq_0_iff mult_left_mono)
  from B0 have fxB: "x \<le> B" if "\<mu> x \<noteq> 0" for x
    using \<mu>pos less_eq_real_def that by auto
  with \<mu>pos have \<mu>FB: "\<mu> x * x \<le> \<mu> x * B" for x
    by (metis ordered_comm_semiring_class.comm_mult_left_mono vector_space_over_itself.scale_cancel_left)
  have "(\<lambda>x. \<mu> x * BC) abs_summable_on UNIV"
    using \<mu>sum by (rule abs_summable_on_cmult_left)
  then have sum\<mu>f: "(\<lambda>x. \<mu> x * x) abs_summable_on UNIV"
    apply (rule abs_summable_on_comparison_test')
    using abs_f\<mu>x by simp
  have sum\<mu>B: "(\<lambda>x. \<mu> x * B) abs_summable_on UNIV"
    using \<mu>sum by (rule abs_summable_on_cmult_left)

  have "(\<Sum>\<^sub>ax. \<mu> x *\<^sub>R x) = (\<Sum>\<^sub>ax. \<mu> x * x)" 
    by simp
  also have "\<dots> \<le> (\<Sum>\<^sub>ax. \<mu> x * B)"
    using sum\<mu>f sum\<mu>B \<mu>FB by (rule infsetsum_mono)
  also have "\<dots> = (\<Sum>\<^sub>ax. \<mu> x) * B"
    using \<mu>sum infsetsum_cmult_left by blast
  also from \<mu>sum1 \<mu>1_or_Bpos have "\<dots> \<le> B"
    by (auto simp: mult_left_le ordered_field_class.sign_simps(5))
  finally show "(\<Sum>\<^sub>ax. \<mu> x *\<^sub>R x) \<le> B" by simp
qed


lemma expectation_lower_bound:
  fixes \<mu> :: "real distr"
  assumes "weight \<mu> = 1 \<or> B \<le> 0"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> x \<le> C"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> x \<ge> B"
  shows "expectation \<mu> \<ge> B"
proof -
  have "expectation (map_distr uminus \<mu>) \<le> -B"
    apply (rule expectation_upper_bound[where C="-C"])
    using assms by auto
  then show ?thesis
    unfolding expectation_uminus by simp
qed

lemma prob_bind_distr: "prob (bind_distr \<mu> f) x = (\<Sum>\<^sub>a y\<in>UNIV. prob \<mu> y * prob (f y) x)"
  apply transfer by simp

lemma Prob_singleton[simp]: "Prob D {x} = prob D x"
  apply transfer by simp

lemma prob_leq1[simp]: "prob \<mu> x \<le> 1"
  by (simp flip: Prob_singleton)


(* TODO move to missing *)
lemma local_defE: "(\<And>x. x=y \<Longrightarrow> P) \<Longrightarrow> P" by metis


lemma bind_distr_summable: "(\<lambda>y. prob \<mu> y * prob (f y) x) abs_summable_on UNIV"
  apply (rule local_defE[of "bind_distr \<mu> f"], rename_tac \<mu>f)
  apply (subgoal_tac "\<And>x y. prob (f y) x \<le> 1")
  apply transfer
  apply (rule abs_summable_on_comparison_test')
  unfolding is_distribution_def by (auto simp: mult_left_le)

lemma prob_geq_0[simp]: "prob \<mu> f \<ge> 0"
  apply transfer by (auto simp: is_distribution_def)

lemma prob_abs_summable: "prob \<mu> abs_summable_on UNIV"
  apply transfer unfolding is_distribution_def
  using distr_abs_summable_on by blast

lemma supp_prob: "x \<in> supp \<mu> \<longleftrightarrow> prob \<mu> x > 0"
  apply transfer by auto
lemma supp_prob': "x \<in> supp \<mu> \<longleftrightarrow> prob \<mu> x \<noteq> 0"
  apply (subst supp_prob)
  by (smt prob_geq_0)



lemma supp_bind_distr[simp]: 
  shows "supp (bind_distr \<mu> f) = (\<Union>x\<in>supp \<mu>. supp (f x))"
proof (rule; rule)
  show "y \<in> (\<Union>x\<in>supp \<mu>. supp (f x))"
    if "y \<in> supp (bind_distr \<mu> f)"
    for y :: 'a
  proof -
    from that have "prob (bind_distr \<mu> f) y > 0"
      by (simp add: supp.rep_eq)
    also have "prob (bind_distr \<mu> f) y = (\<Sum>\<^sub>a x\<in>UNIV. prob \<mu> x * prob (f x) y)"
      unfolding prob_bind_distr by simp
    finally obtain x where "prob \<mu> x * prob (f x) y \<noteq> 0"
      by (smt infsetsum_all_0)
    then have "prob \<mu> x > 0" and "prob (f x) y > 0"
      using prob_geq_0 less_eq_real_def by fastforce+
    then have "x \<in> supp \<mu>" and "y \<in> supp (f x)"
      by (simp_all add: supp.rep_eq)
    then show ?thesis
      by auto
  qed
  show "y \<in> supp (bind_distr \<mu> f)"
    if "y \<in> (\<Union>x\<in>supp \<mu>. supp (f x))"
    for y :: 'a
  proof -
    have [trans]: "a \<ge> b \<Longrightarrow> b > c \<Longrightarrow> a > c" for a b c :: real by auto

    from that obtain x where x_supp: "x\<in>supp \<mu>" and y_supp: "y \<in> supp (f x)"
      by auto
    have "(\<Sum>\<^sub>a x\<in>UNIV. prob \<mu> x * prob (f x) y) \<ge> (\<Sum>\<^sub>a x\<in>{x}. prob \<mu> x * prob (f x) y)" (is "_ \<ge> \<dots>")
      apply (rule infsetsum_mono_neutral)
      using bind_distr_summable[where x=y] by auto
    also have "\<dots> = prob \<mu> x * prob (f x) y"
      by auto
    also have "\<dots> > 0"
      using x_supp y_supp by (simp_all add: supp.rep_eq)
    finally have "prob (bind_distr \<mu> f) y > 0"
      unfolding prob_bind_distr by auto
    then show "y \<in> supp (bind_distr \<mu> f)"
      by (simp add: supp.rep_eq)
  qed
qed

lemma supp_product_distr[simp]: "supp (product_distr \<mu> \<nu>) = supp \<mu> \<times> supp \<nu>"
  by auto


lift_definition bernoulli :: "real \<Rightarrow> bit distr" is
  "\<lambda>p::real. let p' = min (max p 0) 1 in (\<lambda>b::bit. if b=0 then 1-p' else p')"
proof (rename_tac p)
  fix p :: real
  define D where "D = (let p' = min (max p 0) 1 in (\<lambda>b::bit. if b = 0 then 1 - p' else p'))"
  define p' where "p' = min (max p 0) 1"
  then have p': "p' \<ge> 0" "p' \<le> 1" by auto
  from p'_def D_def have D: "D = (\<lambda>b. if b = 0 then 1 - p' else p')" unfolding Let_def by auto
  have Dpos: "\<forall>x. 0 \<le> D x"
    unfolding D using p' by auto
  moreover have "D abs_summable_on UNIV"
    by simp
  moreover have "infsetsum D UNIV \<le> 1"
    by (simp add: D UNIV_bit)
  ultimately show "is_distribution D"
    unfolding is_distribution_def by simp
qed

lemma bernoulli1:
  assumes "p\<ge>0" and "p\<le>1"
  shows "prob (bernoulli p) 1 = p"
  apply (transfer fixing: p)
  using assms by (auto simp: Let_def)

lemma bernoulli0:
  assumes "p\<ge>0" and "p\<le>1"
  shows "prob (bernoulli p) 0 = 1-p"
  apply (transfer fixing: p)
  using assms by (auto simp: Let_def)

lemma bernoulli_fix:
  shows "bernoulli p = bernoulli (max 0 (min 1 p))"
  apply (transfer fixing: p)
  by (auto intro!: ext simp: Let_def)

lemma weight_bernoulli[simp]: "weight (bernoulli p) = 1"
  using [[transfer_del_const pcr_bit]]
  apply (transfer fixing: p)
  by (simp add: UNIV_bit Let_def)

lemma map_distr_const[simp]: 
  shows "map_distr (\<lambda>x. c) D = weight D *\<^sub>R point_distr c"
  apply (transfer fixing: c, rule ext) apply auto
  by (metis infsetsum_nonneg is_distribution_def max_def min.commute min.orderE)

lemma bind_distr_const[simp]:
  shows "bind_distr \<mu> (\<lambda>x. \<nu>) = weight \<mu> *\<^sub>R \<nu>"
  apply (transfer, rule ext) apply auto
  apply (subst max_absorb2)
   apply (simp add: infsetsum_nonneg is_distribution_def')
  apply (subst min_absorb2)
  using is_distribution_def apply blast
  using infsetsum_cmult_left is_distribution_def by fastforce

lemma prob_map_distr_bij:
  assumes "bij f"
  shows "prob (map_distr f \<mu>) x = prob \<mu> (Hilbert_Choice.inv f x)"
  apply (transfer fixing: f) 
  apply (subst bij_vimage_eq_inv_image)
  using assms by auto


lemma prob_True_prob_1:
  "prob \<mu> True = prob (map_distr (\<lambda>b. if b then 1 else 0) \<mu>) (1::bit)"
proof -
  define f :: "bool\<Rightarrow>bit" where "f = (\<lambda>b. if b then 1 else 0)"
  have "bij f"
    apply (rule bijI') unfolding f_def
    (* Sledgehammer *)
    using bit.distinct(2) apply presburger by (meson bit.exhaust)
  moreover have "Hilbert_Choice.inv f 1 = True"
    apply (rule inv_f_eq)
    using \<open>bij f\<close> bij_betw_imp_inj_on apply blast 
    unfolding f_def by simp
  ultimately show "prob \<mu> True = prob (map_distr f \<mu>) 1"
    apply (subst prob_map_distr_bij) by auto
qed


lemma swap_product_distr: "map_distr prod.swap (product_distr \<mu> \<nu>) = (product_distr \<nu> \<mu>)"
proof (rule prob_inject[THEN iffD1], rule ext, rename_tac xy)
  fix xy :: "'a*'b" obtain x y where xy: "xy = (x,y)" 
    apply atomize_elim by auto
  have "prob (map_distr prod.swap (product_distr \<mu> \<nu>)) xy = prob (product_distr \<mu> \<nu>) (Hilbert_Choice.inv prod.swap xy)"
    apply (subst prob_map_distr_bij)
    using bij_swap by auto
  also have "\<dots> = prob (product_distr \<mu> \<nu>) (y,x)"
    unfolding xy
    by (metis inv_equality swap_simp swap_swap) 
  also have "\<dots> = prob \<mu> y * prob \<nu> x"
    by simp
  also have "\<dots> = prob (product_distr \<nu> \<mu>) xy"
    unfolding xy by simp
  finally show "prob (map_distr prod.swap (product_distr \<mu> \<nu>)) xy = prob (product_distr \<nu> \<mu>) xy"
    by simp
qed

lemma map_distr_fst_product_distr[simp]:
  "map_distr fst (product_distr \<mu> \<nu>) = weight \<nu> *\<^sub>R \<mu>"
proof (transfer, rule ext)
  fix \<mu> :: "'a \<Rightarrow> real"
    and \<nu> :: "'b \<Rightarrow> real"
    and x :: 'a
  assume "is_distribution (\<mu>)" and \<nu>: "is_distribution (\<nu>)"

  have \<mu>sumgeq0: "infsetsum \<nu> UNIV \<ge> 0"
    using \<nu> unfolding is_distribution_def
    by (simp add: infsetsum_nonneg)
  have maxmin: "min 1 (max 0 (infsetsum \<nu> (UNIV))) = infsetsum \<nu> UNIV"
    apply (subst min_absorb2)
    using \<nu> unfolding is_distribution_def apply simp
    using \<mu>sumgeq0 by simp

  have "(\<Sum>\<^sub>axy\<in>fst -` {x}. \<Sum>\<^sub>ax. \<mu> x * infsetsum \<nu> (Pair x -` {xy})) = (\<Sum>\<^sub>axy\<in>range (Pair x). \<Sum>\<^sub>ax. \<mu> x * infsetsum \<nu> (Pair x -` {xy}))"
    by (rewrite at _ asm_rl[of "fst -` {x} = Pair x ` UNIV"], auto)
  also have "\<dots> = (\<Sum>\<^sub>ay. \<Sum>\<^sub>ax'. \<mu> x' * infsetsum \<nu> (Pair x' -` {(x, y)}))"
    by (subst infsetsum_reindex, auto simp add: inj_on_def)
  also have "\<dots> = (\<Sum>\<^sub>ay. \<Sum>\<^sub>ax'\<in>{x}. \<mu> x' * infsetsum \<nu> (Pair x' -` {(x, y)}))"
    apply (rule infsetsum_cong)
     apply (rule infsetsum_cong_neutral)
       apply auto
    by (meson Pair_inject infsetsum_all_0 vimage_singleton_eq)
  also have "\<dots> = (\<Sum>\<^sub>ay. \<mu> x * infsetsum \<nu> (Pair x -` {(x, y)}))"
    by auto
  also have "\<dots> = (\<Sum>\<^sub>ay. \<mu> x * infsetsum \<nu> {y})"
    by (subgoal_tac "\<And>y::'b. Pair x -` {(x, y)} = {y}", auto)
  also have "\<dots> = (\<Sum>\<^sub>ay. \<mu> x * \<nu> y)"
    by simp
  also have "\<dots> = \<mu> x * (\<Sum>\<^sub>ay. \<nu> y)"
    using \<open>is_distribution \<nu>\<close> infsetsum_cmult_right is_distribution_def by blast
  also have "\<dots> = (\<Sum>\<^sub>ay. \<nu> y) * \<mu> x"
    by simp
  also have "\<dots> = (min 1 (max 0 (infsetsum \<nu> (UNIV::'b set))) * \<mu> x)"
    unfolding maxmin by simp

  finally show "(\<Sum>\<^sub>ax\<in>fst -` {x}. \<Sum>\<^sub>ay. \<mu> (y::'a) * infsetsum \<nu> (Pair y -` {x}))
                  = (min 1 (max 0 (infsetsum \<nu> (UNIV::'b set))) * \<mu> x)"
    by assumption
qed


lemma map_distr_snd_product_distr[simp]: 
  "map_distr snd (product_distr \<mu> \<nu>) = weight \<mu> *\<^sub>R \<nu>"
proof -
  have "map_distr snd (product_distr \<mu> \<nu>) = map_distr fst (map_distr prod.swap (product_distr \<mu> \<nu>))"
    by (simp add: case_prod_beta)
  also have "\<dots> = map_distr fst (product_distr \<nu> \<mu>)"
    by (subst swap_product_distr, simp)
  also have "\<dots> = weight \<mu> *\<^sub>R \<nu>"
    by (rule map_distr_fst_product_distr)
  finally show ?thesis
    by simp
qed

lemma distr_scaleR1[simp]: "1 *\<^sub>R \<mu> = \<mu>" for \<mu> :: "_ distr"
  apply transfer by simp


lemma Prob_union: "Prob \<mu> (A\<union>B) = Prob \<mu> A + Prob \<mu> B - Prob \<mu> (A\<inter>B)"
  apply (transfer fixing: A B)
  apply (rule infsetsum_Un_Int)
  using is_distribution_def abs_summable_on_subset by blast

lemma Prob_setdiff: "Prob \<mu> (A-B) = Prob \<mu> A - Prob \<mu> B + Prob \<mu> (B-A)"
proof (transfer fixing: A B)
  fix \<mu> :: "'a \<Rightarrow> real"
  assume \<mu>: "is_distribution \<mu>"

  have Bsplit: "B = (B-A) \<union> (B\<inter>A)"
    by (simp add: Un_Diff_Int)
  have 1: "infsetsum \<mu> B = infsetsum \<mu> (B-A) + infsetsum \<mu> (B\<inter>A)"
    apply (rewrite at "infsetsum _ \<hole>" Bsplit)
    apply (rule infsetsum_Un_disjoint)
    using \<mu> is_distribution_def abs_summable_on_subset by blast+

  have "infsetsum \<mu> (A - B) = infsetsum \<mu> (A - (B\<inter>A))"
    by (metis Diff_Compl Diff_Diff_Int Diff_eq Int_commute)
  also have "\<dots> = infsetsum \<mu> A - infsetsum \<mu> (B\<inter>A)"
    apply (rule infsetsum_Diff)
    using \<mu> is_distribution_def abs_summable_on_subset apply blast by simp
  also have "\<dots> = infsetsum \<mu> A - (infsetsum \<mu> B - infsetsum \<mu> (B-A))"
    using 1 by linarith
  finally show "infsetsum \<mu> (A - B) = infsetsum \<mu> A - infsetsum \<mu> B + infsetsum \<mu> (B - A)"
    by linarith
qed

lift_definition product_distr' :: "('a::finite \<Rightarrow> 'b distr) \<Rightarrow> ('a \<Rightarrow> 'b) distr" is
  "\<lambda>F f. \<Prod>x\<in>UNIV. F x (f x)"
proof -
  fix F :: "'a \<Rightarrow> 'b \<Rightarrow> real"
  assume distr_F: "is_distribution (F x)" for x
  then have [simp]: "F x y \<ge> 0" for x y
    unfolding is_distribution_def by simp
  have prod_pos: "0 \<le> (\<Prod>x\<in>UNIV. F x (f x))" for f
    by (rule prod_nonneg, simp)
  moreover have "(\<Sum>f\<in>M. \<Prod>x\<in>UNIV. F x (f x)) \<le> 1"
    if [simp]: "finite M" for M
  proof -
    define R and M' :: "('a\<Rightarrow>'b) set" where "R = (\<Union>f\<in>M. range f)" and "M' = UNIV \<rightarrow>\<^sub>E R"
    have [simp]: "M \<subseteq> M'"
      unfolding M'_def R_def by auto
    have [simp]: "finite R"
      unfolding R_def 
      by (rule finite_UN_I, simp_all)
    then have [simp]: "finite M'"
      unfolding M'_def by (simp add: finite_PiE)
    have "(\<Sum>f\<in>M. \<Prod>x\<in>UNIV. F x (f x)) \<le>
          (\<Sum>f\<in>M'. \<Prod>x\<in>UNIV. F x (f x))"
      by (rule sum_mono2, simp_all add: prod_pos)
    also have "\<dots> = (\<Prod>x\<in>UNIV. \<Sum>y\<in>R. F x y)"
      unfolding M'_def apply (rule sum_prod_swap) by auto
    also have "\<dots> \<le> (\<Prod>(x::'a)\<in>UNIV. 1)"
    proof -
      have "0 \<le> sum (F x) R" for x
        by (simp add: sum_nonneg)
      moreover have "sum (F x) R \<le> 1" for x
        using distr_F \<open>finite R\<close> is_distribution_def' by blast
      ultimately show ?thesis
        by (rule_tac prod_mono, simp)
    qed
    also have "\<dots> = 1"
      by (rule prod.neutral_const)
    finally show ?thesis
      by -
  qed
  ultimately show "is_distribution (\<lambda>f. \<Prod>x\<in>UNIV. F x (f x))"
    unfolding is_distribution_def' by simp
qed


lemma product_distr'_onepoint:
  assumes "\<And>i. i\<noteq>x \<Longrightarrow> weight (D i) = 1"
  shows "map_distr (\<lambda>f. f x) (product_distr' D) = D x"
  using assms
proof transfer
  thm infsetsum_prod_PiE
  fix x :: 'a
    and D :: "'a \<Rightarrow> 'b \<Rightarrow> real"
  assume "pred_fun top is_distribution D"
  then have distr: "is_distribution (D i)" for i
    by simp
  assume sum1: "infsetsum (D i) UNIV = 1" if "i \<noteq> x" for i
  define PIE :: "_ \<Rightarrow> _ \<Rightarrow> ('a\<Rightarrow>'b) set" where "PIE F y = PiE F (\<lambda>z. if z=x then {y} else UNIV)" for F y
  have PiE: "(\<lambda>f. f x) -` {y} = PiE UNIV (\<lambda>z. if z=x then {y} else UNIV)" for y :: 'b
    apply auto
    by (smt PiE_iff UNIV_I singletonD)
  have "(\<Sum>\<^sub>af\<in>(\<lambda>f. f x) -` {y}. \<Prod>x'\<in>UNIV. D x' (f x')) = (\<Prod>x'\<in>UNIV. infsetsum (D x') (if x' = x then {y} else UNIV))" for y
    apply (subst PiE)
    apply (subst infsetsum_prod_PiE)
    using distr is_distribution_def by auto
  also have "\<dots>y = (\<Prod>x'\<in>{x}. infsetsum (D x') (if x' = x then {y} else UNIV))" for y
    apply (rule prod.mono_neutral_right)
    using sum1 by auto
  also have "\<dots>y = D x y" for y
    by simp
  finally
  show "(\<lambda>y. \<Sum>\<^sub>af\<in>(\<lambda>f. f x) -` {y}. \<Prod>x\<in>UNIV. D x (f x)) = D x"
    by auto
qed

lemma map_distr_product_distr'_onepoint:
  assumes "\<And>i. i\<noteq>x \<Longrightarrow> weight (D i) = 1"
  shows "map_distr (\<lambda>f. F (f x)) (product_distr' D) = map_distr F (D x)"
  apply (subst product_distr'_onepoint[symmetric, where D=D])
  using assms by auto

lemma bind_distr_twice_indep:
  "bind_distr A (\<lambda>a. bind_distr B (\<lambda>b. F a b)) 
 = bind_distr B (\<lambda>b. bind_distr A (\<lambda>a. F a b))"
  by (cheat bind_distr_twice_indep)

lemma bind_distr_point_distr[simp]: "bind_distr D point_distr = D"
proof (transfer, rule ext)
  fix D :: "'a \<Rightarrow> real" and x :: 'a
  assume "is_distribution D"
  have "(\<Sum>\<^sub>ay. D y * (if x \<in> {y} then 1 / real (card {y}) else 0)) = (\<Sum>\<^sub>ay\<in>{x}. D y)"
    apply (rule infsetsum_cong_neutral) by auto
  also have "\<dots> = D x"
    by auto
  finally show "(\<Sum>\<^sub>ay. D y * (if x \<in> {y} then 1 / real (card {y}) else 0)) = D x"
    by simp
qed

lemma distribution_leq1: assumes "is_distribution \<mu>" shows "\<mu> x \<le> 1"
proof -
  have "\<mu> x = infsetsum \<mu> {x}"
    by auto
  also have "\<dots> \<le> infsetsum \<mu> UNIV"
    apply (rule infsetsum_mono_neutral_left)
    using assms unfolding is_distribution_def by auto
  also have "\<dots> \<le> 1"
    using assms unfolding is_distribution_def by auto
  finally show ?thesis.
qed

lemma bind_distr_map_distr: "bind_distr \<mu> (\<lambda>x. map_distr g (f x)) = map_distr g (bind_distr \<mu> f)"
proof (rule local_defE[of "bind_distr \<mu> f"], rename_tac \<mu>f, transfer, rule ext)
  fix \<mu> :: "'b \<Rightarrow> real"
    and g :: "'c \<Rightarrow> 'a"
    and f :: "'b \<Rightarrow> 'c \<Rightarrow> real"
    and x :: 'a
    and \<mu>f :: "'c \<Rightarrow> real"
  assume \<mu>: "is_distribution \<mu>"
  assume f: "pred_fun top is_distribution f"
  then have fpos: "(0 \<le> f y x)" and fy_sum: "f y abs_summable_on UNIV" and fy_sum1: "infsetsum (f y) UNIV \<le> 1" for y x
    by (auto simp: is_distribution_def)
  from f have fyx1: "f y x \<le> 1" for y x
    by (auto simp: is_distribution_def intro: distribution_leq1)
  assume \<mu>f_def: "\<mu>f = (\<lambda>x. \<Sum>\<^sub>ay. \<mu> y * f y x)"
  assume \<mu>f: "is_distribution \<mu>f"
  then have summable1: "(\<lambda>x. \<Sum>\<^sub>ay. \<mu> y * f y x) abs_summable_on UNIV"
    unfolding \<mu>f_def is_distribution_def by simp
  have summable2: "(\<lambda>y. \<mu> y * f y x) abs_summable_on UNIV" for x
    apply (rule abs_summable_on_comparison_test'[where g="\<mu>"])
    using \<mu>[unfolded is_distribution_def] apply simp_all
    using fyx1 fpos by (simp add: mult_left_le)
  have prod_summable: "(\<lambda>(x, y). \<mu> y * f y x) abs_summable_on UNIV \<times> UNIV"
    apply (rule abs_summable_product)
    by (simp_all add: fpos is_distribution_def summable1 summable2 \<mu>[unfolded is_distribution_def])
  have "(\<Sum>\<^sub>ay. \<mu> y * (\<Sum>\<^sub>ax\<in>g -` {x}. f y x)) = (\<Sum>\<^sub>ay. \<Sum>\<^sub>ax\<in>g -` {x}. \<mu> y * f y x)"
    apply (subst infsetsum_cmult_right)
    using fy_sum abs_summable_on_subset apply blast by auto
  also have "\<dots> = (\<Sum>\<^sub>ax\<in>g -` {x}. \<Sum>\<^sub>ay. \<mu> y * f y x)"
    apply (rule infsetsum_swap[symmetric])
    apply (rule abs_summable_on_subset[where B=UNIV])
    using prod_summable by simp_all
  finally show "(\<Sum>\<^sub>ay. (\<mu> y) * (\<Sum>\<^sub>ax\<in>g -` {x}. f y x)) 
      = (\<Sum>\<^sub>ax\<in>g -` {x}. \<Sum>\<^sub>ay. \<mu> y * f y x)" .
qed


\<comment> \<open>\<^term>\<open>\<mu> = below_bernoulli D E p\<close> is a distribution such that: the first marginal is \<^term>\<open>D\<close>,
    the second marginal is \<^term>\<open>p\<close>-Bernoulli distributed, and if the first output is in \<^term>\<open>E\<close>,
    then the second output is \<^term>\<open>1\<close>\<close>
definition below_bernoulli :: "'a distr \<Rightarrow> ('a set) \<Rightarrow> real \<Rightarrow> ('a*bit) distr" where
  "below_bernoulli D E p = (let pE = Prob D E in bind_distr D (\<lambda>x. map_distr (Pair x) 
       (bernoulli (if x\<in>E then 1 else (p-pE)/(1-pE)))))"

  
lemma below_bernoulli_fst[simp]: "map_distr fst (below_bernoulli D E p) = D"
  unfolding below_bernoulli_def by (simp add: Let_def bind_distr_map_distr[symmetric])


lift_definition restrict_distr :: "'a distr \<Rightarrow> 'a set \<Rightarrow> 'a distr" is
  "\<lambda>\<mu> S x. if x\<in>S then \<mu> x else 0"
  unfolding is_distribution_def apply auto
  apply (simp add: abs_summable_on_comparison_test')
  by (smt infsetsum_mono not_summable_infsetsum_eq)

lemma bind_distr_cong:
  assumes "\<And>x. x\<in>supp \<mu> \<Longrightarrow> f x = g x"
  shows "bind_distr \<mu> f = bind_distr \<mu> g"
  using assms apply transfer apply (rule ext)
  apply (rule infsetsum_cong_neutral)
  apply (auto simp: is_distribution_def)
  by (metis order_trans_rules(17))

lemma supp_restrict_distr[simp]:
  "supp (restrict_distr \<mu> S) = S \<inter> supp \<mu>"
  apply transfer by auto

lemma Prob_restrict_distr[simp]:
  "Prob (restrict_distr \<mu> S) T = Prob \<mu> (S\<inter>T)"
  apply transfer
  apply (rule infsetsum_cong_neutral)
  by auto

lemma prob_scaleR[simp]:
  "prob (r *\<^sub>R \<mu>) x = min 1 (max 0 r) * prob \<mu> x"
  apply transfer by simp

lemma max0Prob[simp]: "max 0 (Prob \<mu> E) = Prob \<mu> E"
  by (metis (no_types) Prob_pos max_def_raw)

lemma min1Prob[simp]: "min 1 (Prob \<mu> E) = Prob \<mu> E"
  by (simp add: min_absorb2)


lemma bind_distr_split: "prob (bind_distr \<mu> f) x = 
  prob (bind_distr (restrict_distr \<mu> E) f) x +
  prob (bind_distr (restrict_distr \<mu> (-E)) f) x"
  apply transfer
  apply (subst infsetsum_add[symmetric], auto simp: is_distribution_def)
  apply (smt Rings.mult_sign_intros(1) abs_summable_on_comparison_test' distribution_leq1 is_distribution_def mult_left_le real_norm_def)
  apply (smt Rings.mult_sign_intros(1) abs_summable_on_comparison_test' distribution_leq1 is_distribution_def mult_left_le real_norm_def)
  by (smt infsetsum_cong mult_cancel_left2)

lemma weight1_bind_distr[simp]:
  shows "weight (bind_distr \<mu> f) = 1 \<longleftrightarrow> weight \<mu> = 1 \<and> (\<forall>x\<in>supp \<mu>. weight (f x) = 1)"
proof (rule local_defE[of "bind_distr \<mu> f"], rename_tac \<mu>f, transfer)
  fix \<mu>f :: "'a \<Rightarrow> real"
    and \<mu> :: "'b \<Rightarrow> real"
    and f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assume \<mu>: "is_distribution \<mu>"
  then have \<mu>pos: "\<mu> x \<ge> 0" for x by (simp add: is_distribution_def)
  assume f: "pred_fun top is_distribution f"
  then have fpos[simp]: "0 \<le> f y x" and fy_sum: "f y abs_summable_on UNIV"
    and fy_sum1: "infsetsum (f y) UNIV \<le> 1" 
    for y x
    by (auto simp: is_distribution_def)
  from f have fyx1: "f y x \<le> 1" for y x 
    by (auto simp: distribution_leq1)
(*   from fy_sum1 fy_sum fpos have fyx1: "f y x \<le> 1" for y x
  proof -
    have "f y x = infsetsum (f y) {x}"
      by auto
    also have "\<dots> \<le> infsetsum (f y) UNIV"
      apply (rule infsetsum_mono_neutral_left)
      using fy_sum by auto
    also have "\<dots> \<le> 1"
      using fy_sum1 by simp
    finally show ?thesis.
  qed *)
  assume \<mu>f_def: "\<mu>f = (\<lambda>x. \<Sum>\<^sub>ay. \<mu> y * f y x)"
  assume \<mu>f: "is_distribution \<mu>f"
  then have summable1: "(\<lambda>x. \<Sum>\<^sub>ay. \<mu> y * f y x) abs_summable_on UNIV"
    unfolding \<mu>f_def is_distribution_def by simp
  have summable2: "(\<lambda>y. \<mu> y * f y x) abs_summable_on UNIV" for x
    apply (rule abs_summable_on_comparison_test'[where g="\<mu>"])
    using \<mu>[unfolded is_distribution_def] apply simp_all
    using fyx1 mult_left_le by blast
  have prod_summable: "(\<lambda>(x, y). \<mu> y * f y x) abs_summable_on UNIV \<times> UNIV"
    apply (rule abs_summable_product)
    by (simp_all add: is_distribution_def summable1 summable2 \<mu>[unfolded is_distribution_def])
  show "((\<Sum>\<^sub>ax. \<Sum>\<^sub>ay. \<mu> y * f y x) = 1) \<longleftrightarrow>
       (infsetsum \<mu> UNIV = 1 \<and> (\<forall>x\<in>{x. 0 < \<mu> x}. infsetsum (f x) UNIV = 1))"
  proof
    assume assm[symmetric]: "(\<Sum>\<^sub>ax. \<Sum>\<^sub>ay. \<mu> y * f y x) = 1" (is "\<dots> = _")
    also have "\<dots> = (\<Sum>\<^sub>ay. \<Sum>\<^sub>ax. \<mu> y * f y x)"
      by (rule infsetsum_swap, fact prod_summable)
    also have "\<dots> = (\<Sum>\<^sub>ay. \<mu> y * (\<Sum>\<^sub>ax. f y x))"
      apply (rule infsetsum_cong)
      using fy_sum apply (rule infsetsum_cmult_right)
      by simp
    also 
    note calc_start = calculation
    have "\<dots> \<le> (\<Sum>\<^sub>ay. \<mu> y)"
      apply (rule infsetsum_mono)
      using calculation not_summable_infsetsum_eq apply fastforce
      using \<mu>[unfolded is_distribution_def] apply blast
      using \<mu>[unfolded is_distribution_def] fy_sum1 mult_left_le by blast
    finally have "infsetsum \<mu> UNIV = 1"
      using \<mu>[unfolded is_distribution_def] by linarith

    moreover have "infsetsum (f y) UNIV = 1" if "0 < \<mu> y" for y
    proof (rule ccontr)
      assume "infsetsum (f y) UNIV \<noteq> 1"
      then have less1: "infsetsum (f y) UNIV < 1"
        using fy_sum1 le_less by blast
      from calc_start have "1 = (\<Sum>\<^sub>ay. \<mu> y * infsetsum (f y) UNIV)".
      also have "\<dots> = (\<Sum>\<^sub>ay\<in>-{y}. \<mu> y * infsetsum (f y) UNIV) + \<mu> y * infsetsum (f y) UNIV"
        apply (subst Compl_partition2[symmetric, where A="{y}"], subst infsetsum_Un_disjoint)
           apply (metis (full_types) abs_summable_on_subset calculation not_summable_infsetsum_eq semiring_norm(160) subset_UNIV)
        by simp_all
      also have "\<dots> < (\<Sum>\<^sub>ay\<in>-{y}. \<mu> y * infsetsum (f y) UNIV) + \<mu> y"
        apply (rule add_strict_left_mono)
        using less1 that by simp
      also have "\<dots> \<le> (\<Sum>\<^sub>ay\<in>-{y}. \<mu> y) + \<mu> y"
        apply (rule add_right_mono)
        apply (rule infsetsum_mono)
          apply (metis (full_types) calc_start abs_summable_on_subset not_summable_infsetsum_eq semiring_norm(160) subset_UNIV)
        using \<mu>[unfolded is_distribution_def] abs_summable_on_subset apply blast
        using \<mu>[unfolded is_distribution_def] fy_sum1 mult_left_le by blast
      also have "\<dots> = (\<Sum>\<^sub>ay. \<mu> y)"
        apply (subst Compl_partition2[symmetric, where A="{y}"], subst infsetsum_Un_disjoint)
        using \<mu>[unfolded is_distribution_def] abs_summable_on_subset apply blast
        by simp_all
      also have "\<dots> \<le> 1"
        using \<mu>[unfolded is_distribution_def] by blast
      finally have "1 < 1" by simp
      then show False by auto
    qed
    ultimately show "infsetsum \<mu> UNIV = 1 \<and> (\<forall>x\<in>{x. 0 < \<mu> x}. infsetsum (f x) UNIV = 1)"
      by auto
  next
    assume assm: "infsetsum \<mu> UNIV = 1 \<and> (\<forall>x\<in>{x. 0 < \<mu> x}. infsetsum (f x) UNIV = 1)"
    have "(\<Sum>\<^sub>ax. \<Sum>\<^sub>ay. \<mu> y * f y x) = (\<Sum>\<^sub>ay. \<Sum>\<^sub>ax. \<mu> y * f y x)"
      by (rule infsetsum_swap, fact prod_summable)
    also have "\<dots> = (\<Sum>\<^sub>ay. \<mu> y * (\<Sum>\<^sub>ax. f y x))"
      apply (rule infsetsum_cong)
      using fy_sum apply (rule infsetsum_cmult_right)
      by simp
    also have "\<dots> = (\<Sum>\<^sub>ay. \<mu> y)"
      using assm apply auto
      by (smt \<mu>[unfolded is_distribution_def] infsetsum_cong mult_cancel_left2)
    also have "\<dots> = 1"
      using assm by simp
    finally show "(\<Sum>\<^sub>ax. \<Sum>\<^sub>ay. \<mu> y * f y x) = 1".
  qed
qed

lemma Prob_complement: "Prob \<mu> (-E) = weight \<mu> - Prob \<mu> E"
  apply (transfer fixing: E)
  apply (rewrite at UNIV asm_rl[of "UNIV = -E \<union> E"], simp)
  apply (rule add_implies_diff)
  apply (rule infsetsum_Un_disjoint[symmetric])
  by (simp_all add: distr_abs_summable_on is_distribution_def')

lemma below_bernoulli_snd[simp]: 
  assumes [simp]: "weight D = 1"
  shows "map_distr snd (below_bernoulli D E p) = bernoulli (max (min p 1) (Prob D E))"
proof -
  define pE p' p'' where "pE = Prob D E" and "p' = (p - pE) / (1 - pE)" and "p'' = max 0 (min 1 p')"
  then have [simp]: "p'' \<ge> 0" and [simp]: "p'' \<le> 1" by auto
  have pEpos[simp]: "pE \<ge> 0" and pEleq1[simp]: "pE \<le> 1"
    unfolding pE_def apply (metis Prob_pos) by (metis Prob_leq1)
  have "map_distr snd (below_bernoulli D E p) = bind_distr D (\<lambda>x. bernoulli (if x \<in> E then 1 else p'))"
    apply (simp add: below_bernoulli_def Let_def bind_distr_map_distr[symmetric])
    unfolding p'_def pE_def by simp
  also have "\<dots> = bind_distr D (\<lambda>x. bernoulli (if x \<in> E then 1 else p''))"
  proof -
    have "bernoulli (if x \<in> E then 1 else p') = bernoulli (if x \<in> E then 1 else p'')" for x
      apply (cases "x\<in>E", simp_all)
      unfolding p''_def by (rule bernoulli_fix)
    then show ?thesis by auto
  qed
  also have "\<dots> = bernoulli (pE + (1-pE) * p'')" (is "_ = bernoulli ?p")
  proof (rule prob_inject[THEN iffD1], rule ext)
    fix x :: bit
    have [simp]: "(pE + (1 - pE) * p'') \<ge> 0"
      by simp
    have [simp]: "(pE + (1 - pE) * p'') \<le> 1"
      using \<open>p'' \<le> 1\<close>
      by (smt mult_left_le pEleq1)

    have "prob (bind_distr D (\<lambda>x. bernoulli (if x \<in> E then 1 else p''))) x = 
          prob (bind_distr (restrict_distr D E) (\<lambda>x. bernoulli 1)) x +
          prob (bind_distr (restrict_distr D (- E)) (\<lambda>x. bernoulli p'')) x"
      apply (subst bind_distr_split[where E=E])
      apply (subst bind_distr_cong[where g="%x. bernoulli 1"], simp)
      by (subst (2) bind_distr_cong[where g="%x. bernoulli p''"], simp_all)
    also have "\<dots> = Prob D E * prob (bernoulli 1) x + Prob D (- E) * prob (bernoulli p'') x"
      by simp
    also have "\<dots> = pE * prob (bernoulli 1) x + (1-pE) * prob (bernoulli p'') x"
      by (simp add: pE_def Prob_complement)
    also have "\<dots> = prob (bernoulli (pE + (1 - pE) * p'')) x"
      apply (cases x)
       apply (auto simp: bernoulli1 bernoulli0)
      by (simp add: right_diff_distrib')
    finally show "prob (bind_distr D (\<lambda>x. bernoulli (if x \<in> E then 1 else p''))) x = prob (bernoulli (pE + (1 - pE) * p'')) x"
      by assumption
  qed
  also
  consider (leqPE) "p \<le> pE" "p \<ge> 0" "p \<le> 1" | (geqPE) "p \<ge> pE" "p \<ge> 0" "p \<le> 1" | (less0) "p \<le> 0" | (gr1) "p \<ge> 1" "pE\<noteq>1" | (pE1) "pE=1"
    apply atomize_elim by auto
  then have "?p = max (min p 1) pE"
  proof cases
    case leqPE
    then have "p' \<le> 0"
      unfolding p'_def
      by (simp add: linordered_field_class.divide_nonpos_nonneg)
    then have "p'' = 0"
      unfolding p''_def
      by linarith
    then show ?thesis
      by (simp add: leqPE min_absorb1 max_absorb2)
  next
    case geqPE
    then have "p' \<ge> 0" and "p' \<le> 1"
      unfolding p'_def apply auto
      by (metis diff_right_mono divide_eq_0_iff ge_iff_diff_ge_0 geqPE(3) le_numeral_extra(1) less_eq_real_def nice_ordered_field_class.divide_le_eq_1_pos p'_def pEleq1)
    then have "p'' = p'"
      unfolding p''_def
      by linarith
    then show ?thesis
      apply (simp add: p'_def)
      using geqPE(1) geqPE(3) by linarith
  next
    case less0
    then have "p' \<le> 0"
      unfolding p'_def
      using pEpos pEleq1
      by (meson basic_trans_rules(23) diff_ge_0_iff_ge diff_le_0_iff_le divide_le_0_iff)
    then have "p'' = 0"
      unfolding p''_def by simp
    then show ?thesis
      apply (simp add: p'_def)
      using less0 pEpos by linarith
  next
    case gr1
    then have "p' \<ge> 1"
      unfolding p'_def
      using less_eq_real_def pEleq1 by auto
    then have "p'' = 1"
      unfolding p''_def by simp
    then show ?thesis 
      apply (simp add: p'_def)
      using gr1 
      by (simp add: min_absorb2 max_absorb1)
  next
    case pE1
    then show ?thesis
      by simp
  qed
  finally show ?thesis
    unfolding pE_def by simp
qed

lemma below_bernoulli_supp:
  assumes "x \<in> supp (below_bernoulli D E p)"
  shows "fst x : E \<Longrightarrow> snd x = 1"
  using assms apply (simp add: below_bernoulli_def Let_def)
  apply (transfer fixing: x E D p)
  using divide_less_cancel by fastforce 


lemma map_distr_uniform_regular[simp]: 
  fixes f::"'a\<Rightarrow>'b" 
  assumes reg: "regular_betw f A B"
  shows "map_distr f (uniform A) = uniform B"
proof (cases "finite A")
  case True
  show ?thesis
  proof (transfer fixing: f A B, rule ext)
    from reg obtain n where reg_n: "regular_betw_n f A B n" 
      unfolding regular_betw_def by auto
        (* then have "finite " *)
    from True reg have "finite B"
      using regular_betw_finite by blast
    from reg_n have cardAB[simp]: "card A = n * card B"
      using regular_betw_n_card by blast
    show "(\<Sum>\<^sub>am\<in>f -` {y}. if m \<in> A then 1 / real (card A) else 0) = (if y \<in> B then 1 / real (card B) else 0)" 
      (is "?lhs = ?rhs") for y
    proof (cases "y \<in> B")
      case True
      define R where "R = (f -` {y}) \<inter> -A"
      from reg_n have card_y: "card (f -` {y} \<inter> A) = n" and "n\<noteq>0"
        unfolding regular_betw_n_def apply auto
        using True by blast
      then have fin_y: "finite (f -` {y} \<inter> A)"
        by (meson card_eq_0_iff)
      have "?lhs = (\<Sum>\<^sub>am\<in>f-`{y} \<inter> A. 1 / real (card A))"
        apply (rule infsetsum_cong_neutral)
        by auto
      also have "\<dots> = (\<Sum>m\<in>f-`{y} \<inter> A. 1 / real (card A))"
        using fin_y by (rule infsetsum_finite)
      also have "\<dots> = n / real (card A)"
        apply (subst sum_constant_scale) unfolding card_y by auto
      also have "\<dots> = 1 / real (card B)"
        using \<open>n\<noteq>0\<close> by simp
      also have "\<dots> = ?rhs"
        using True by auto
      finally show ?thesis .
    next
      case False
      then have rhs: "?rhs = 0" by simp
      from reg_n have "n\<noteq>0"
        unfolding regular_betw_n_def by auto
      from False have yA: "x \<in> f -` {y} \<Longrightarrow> x \<notin> A" for x
        using reg_n unfolding regular_betw_n_def 
        by (metis image_eqI vimage_singleton_eq) 
      have "?lhs = (\<Sum>\<^sub>am\<in>f -` {y}. 0)"
        apply (rule infsetsum_cong)
        using yA by auto
      also have "\<dots> = 0"
        by auto
      finally have "?lhs = 0" .
      with rhs show ?thesis by simp
    qed
  qed  
next
  assume "infinite A"
  moreover with assms have "infinite B"
    using regular_betw_finite by auto
  ultimately have "uniform A = 0" and "uniform B = 0"
    by (simp_all add: uniform_infinite)
  then show ?thesis 
    by simp
qed

lemma bind_product_distr':
  fixes G :: "'i::finite \<Rightarrow> 'g distr"
    and F :: "'g \<Rightarrow> 'i \<Rightarrow> 'f distr"
  shows "bind_distr (product_distr' G) (\<lambda>D. product_distr' (\<lambda>i. F (D i) i))
         = product_distr' (\<lambda>i. bind_distr (G i) (\<lambda>d. F d i))"
  by (cheat bind_product_distr')

lemma product_distr'_uniform[simp]:
  "product_distr' (\<lambda>m. uniform (S m)) = uniform {f. \<forall>m. f m \<in> S m}"
  by (cheat product_distr'_uniform)

lemma product_distr'_point_distr[simp]:
  "product_distr' (\<lambda>i. point_distr (f i)) = point_distr f"
  apply simp
  apply (rewrite asm_rl[of "{fa. \<forall>i. fa i = f i} = {f}"])
  by auto

lemma bind_point_distr[simp]: "bind_distr D (\<lambda>d. point_distr (f d)) = map_distr f D"
  by (cheat bind_point_distr)

lemma point_distr_bind[simp]: "bind_distr (point_distr x) f = f x"
  apply transfer apply auto
  by (cheat point_distr_bind)

lemma map_product_distr':
  shows "map_distr (\<lambda>D i. F (D i) i) (product_distr' G)
         = product_distr' (\<lambda>i. map_distr (\<lambda>d. F d i) (G i))"
  unfolding bind_point_distr[symmetric] product_distr'_point_distr[symmetric]
  by (subst bind_product_distr', rule)

lemma total_product_distr'I:
  assumes "\<And>x. weight (f x) = 1"
  shows "weight (product_distr' f) = 1"
  by (cheat total_product_distr'I)

lemma bernoulli_combine_uniform:
  assumes "disjnt A B"
  assumes [simp]: "finite A"
  assumes [simp]: "finite B"
  assumes [simp]: "A \<noteq> {}"
  assumes [simp]: "B \<noteq> {}"
  assumes p_def: "p = card B / card (A\<union>B)"
  shows "bind_distr (uniform A) (\<lambda>a. bind_distr (uniform B) (\<lambda>b.
    map_distr (\<lambda>c. if c = 1 then b else a) (bernoulli p)))
  = uniform (A\<union>B)"
proof (rule distr_eqI)
  fix x :: 'a
  define select where "select a b c = (if c = 1 then b else a)" for a b :: 'a and c :: bit
  define UA UB Ber where "UA = uniform A" and "UB = uniform B" and "Ber = bernoulli p" 
  have [simp]: "p \<ge> 0" and [simp]: "p \<le> 1"
    unfolding p_def by (auto simp: card_gt_0_iff card_mono)
  have [simp]: "prob Ber 0 = 1-p" and [simp]: "prob Ber 1 = p"
    unfolding Ber_def 
     apply (subst bernoulli0, auto)
    by (subst bernoulli1, auto)
  have [simp]: "select a b 0 = a" and [simp]: "select a b 1 = b" for a b
    unfolding select_def by auto
  have [simp]: "weight UA = 1" and [simp]: "weight UB = 1"
    unfolding UA_def UB_def by auto
  from \<open>disjnt A B\<close> have [simp]: "A \<inter> B = {}"
    by (simp add: disjnt_def)

  have "prob (bind_distr UA (\<lambda>a. bind_distr UB (\<lambda>b. map_distr (select a b) Ber))) x = 
        prob (bind_distr Ber (\<lambda>c. bind_distr UA (\<lambda>a. bind_distr UB (\<lambda>b. point_distr (select a b c))))) x"
    (is "?lhs = _")
    apply (subst bind_distr_twice_indep[where A=Ber])
    apply (subst bind_distr_twice_indep[where A=Ber])
    by simp
  also have "\<dots> = (1 - p) * prob UA x + p * prob UB x"
    apply (subst prob_bind_distr)
    by (auto simp: UNIV_bit)
  also
  consider (A) "x\<in>A" and "x\<notin>B" | (B) "x\<in>B" and "x\<notin>A" | (none) "x\<notin>A" and "x\<notin>B"
    using \<open>disjnt A B\<close>
    by (meson disjnt_iff)
  then have "(1 - p) * prob UA x + p * prob UB x = prob (uniform (A \<union> B)) x"
  proof cases
    case A
    have [simp]: "real (card A) + real (card B) \<noteq> 0"
      apply (rule order.strict_implies_not_eq[symmetric])
      apply (rule add_pos_nonneg)
       apply (subst of_nat_0_less_iff)
       apply (simp add: card_gt_0_iff)
      by simp
    have "1 - real (card B) / real (card (A \<union> B)) = real (card A) / real (card (A \<union> B))"
      apply (subst card_Un_disjoint; simp)
      apply (subst card_Un_disjoint; simp)
      apply (subst diff_divide_eq_iff)
      by auto
    with A show ?thesis
      unfolding UA_def UB_def p_def by simp
  next
    case B
    then show ?thesis
      unfolding UA_def UB_def p_def by simp
  next
    case none
    then show ?thesis       
      unfolding UA_def UB_def p_def by simp
  qed
  finally show "?lhs = prob (uniform (A\<union>B)) x"
    by -
qed

lemma bernoulli_p0: "bernoulli 0 = point_distr 0"
  apply (rule distr_eqI)
  by (auto simp: bernoulli0 bernoulli1)

lemma bernoulli_p1: "bernoulli 1 = point_distr 1"
  apply (rule distr_eqI)
  by (auto simp: bernoulli0 bernoulli1)

lemma bind_distr_map_distr': "bind_distr (map_distr f A) G = bind_distr A (\<lambda>x. G (f x))"
  by (cheat bind_distr_map_distr')

lemma map_distr_product_distr: 
  "map_distr (\<lambda>(x,y). (f x, g y)) (product_distr A B) = product_distr (map_distr f A) (map_distr g B)"
  by (auto simp: bind_distr_map_distr[symmetric] bind_distr_map_distr')

lemma bin_distr_eqI:
  assumes "supp \<mu> \<subseteq> {x,y}"
  assumes "supp \<nu> \<subseteq> {x,y}"
  assumes "weight \<mu> = weight \<nu>"
  assumes "prob \<mu> x = prob \<nu> x"
  shows "\<mu> = \<nu>"
proof (rule distr_eqI)
  fix z
  consider (x) "z=x" | (y) "z=y" and "x\<noteq>y" | (none) "z\<notin>{x,y}"
    by auto
  then show "prob \<mu> z = prob \<nu> z"
  proof cases
    case x
    with assms show ?thesis by simp
  next
    case y
    then have "prob \<mu> z = Prob \<mu> {y}"
      by auto
    also have "\<dots> = Prob \<mu> {x,y} - Prob \<mu> {x}"
      using Prob_setdiff[where A="{x,y}" and B="{x}" and \<mu>=\<mu>] y
      by auto
    also have "\<dots> = weight \<mu> - Prob \<mu> {x}"
      apply (subst weight_supp[where S="{x,y}"])
      using assms by auto
    also have "\<dots> = weight \<mu> - prob \<mu> x"
      by auto
    also have "\<dots> = weight \<nu> - prob \<nu> x"
      using assms by auto
    also have "\<dots> = weight \<nu> - Prob \<nu> {x}"
      by auto
    also have "\<dots> = Prob \<nu> {x,y} - Prob \<nu> {x}"
      apply (subst weight_supp[where S="{x,y}"])
      using assms by auto
    also have "\<dots> = Prob \<nu> {y}"
      using Prob_setdiff[where A="{x,y}" and B="{x}" and \<mu>=\<nu>] y
      by auto
    also have "\<dots> = prob \<nu> z"
      using y by auto
    finally show ?thesis
      by -
  next
    case none
    with assms have "z \<notin> supp \<mu>"
      by auto
    then have 1: "prob \<mu> z = 0"
      using supp_prob' by metis
    from none assms have "z \<notin> supp \<nu>"
      by auto
    then have 2: "prob \<nu> z = 0"
      using supp_prob' by metis
    from 1 2
    show ?thesis by simp
  qed
qed

lemma prob_bind_distr_bernoulli:
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> 0 \<le> x \<and> x \<le> 1"
  shows "prob (bind_distr \<mu> bernoulli) 1 = expectation \<mu>"
proof -
  have "prob (bind_distr \<mu> bernoulli) 1 
    = (\<Sum>\<^sub>ay. prob \<mu> y * (let p' = min (max y 0) 1 in (\<lambda>b::bit. if b = 0 then 1 - p' else p')) 1)"
    apply transfer by rule
  also have "\<dots> = (\<Sum>\<^sub>ay. prob \<mu> y * y)"
  proof (rule infsetsum_cong)
    fix x
    show "prob \<mu> x * (let p' = min (max x 0) 1 in (\<lambda>b::bit. if b = 0 then 1 - p' else p')) 1 =
         prob \<mu> x * x"
    proof (cases "0 \<le> x \<and> x \<le> 1")
      case True
      then show ?thesis 
        by (simp add: max_absorb1 min_absorb1)
    next
      case False
      then show ?thesis
        using assms
        by (metis less_eq_real_def mem_Collect_eq mult_zero_left prob_geq_0 supp.rep_eq) 
    qed
  qed simp
  also have "\<dots> = expectation \<mu>"
    apply transfer by simp
  finally show ?thesis
    by -
qed


lemma map_distr_point_distr[simp]:
  "map_distr f (point_distr x) = point_distr (f x)"
proof (transfer fixing: f, rule ext, rename_tac x y)
  fix x y
  have "(\<Sum>\<^sub>am\<in>f -` {y}. if m \<in> {x} then 1 / real (card {x}) else 0)
      = (\<Sum>\<^sub>am\<in>{m. m=x \<and> f m = y}. if m=x then 1 else 0)"
    by (rule infsetsum_cong_neutral, auto)
  also have "\<dots> = (if f x = y then 1 else 0)"
    apply (cases "f x = y")
     apply auto
    apply (subst asm_rl[of \<open>{m. m = x \<and> f m = f x} = {x}\<close>])
    by auto
  also have "\<dots> = (if y \<in> {f x} then 1 / real (card {f x}) else 0)"
    by auto
  finally show "(\<Sum>\<^sub>am\<in>f -` {y}. if m \<in> {x} then 1 / real (card {x}) else 0) = (if y \<in> {f x} then 1 / real (card {f x}) else 0)"
    by -
qed

lemma Prob_map_distr':
  "Prob (map_distr f \<mu>) A = Prob \<mu> (f -` A)"
  by (simp add: Prob_map_distr)


lemma Prob_uniform: 
  "Prob (uniform A) B = real (card (A\<inter>B)) / real (card A)"
proof (cases "finite A")
  case True
  then have "finite (A\<inter>B)"
    by simp
  have "Prob (uniform A) B = (\<Sum>\<^sub>am\<in>A\<inter>B. 1 / real (card A))"
    apply transfer
    apply (rule infsetsum_cong_neutral)
    by auto
  also have "\<dots> = (\<Sum>m\<in>A\<inter>B. 1 / real (card A))"
    using \<open>finite (A\<inter>B)\<close> by simp
  also have "\<dots> = real (card (A\<inter>B)) / real (card A)"
    apply (subst sum_constant)
    by simp
  finally show ?thesis
    by simp
next
  case False
  then show ?thesis
    by (simp add: uniform_infinite)
qed


lemma prob_map_distr: "prob (map_distr f \<mu>) x = infsetsum (prob \<mu>) (f -` {x})"
  apply transfer by simp


lemma markov_inequality:
  assumes exp_ex: "expectation_exists \<mu>"
  assumes supp: "supp \<mu> \<subseteq> {0..}"
  assumes "a > 0"
  shows "Prob \<mu> {a..} \<le> expectation \<mu> / a"
proof -
  have [simp]: "(\<lambda>x. prob \<mu> x) abs_summable_on A" for A
    using prob_abs_summable abs_summable_on_subset by fastforce
  then have [simp]: "(\<lambda>x. prob \<mu> x * a) abs_summable_on A" for A
    by auto
  from exp_ex have exp_ex[simp]: "(\<lambda>x. prob \<mu> x * x) abs_summable_on A" for A
    unfolding expectation_exists.rep_eq
    apply auto
    using abs_summable_on_subset by blast
  have pos: "prob \<mu> x = 0" if "x < 0" for x
    using supp supp_prob' that by fastforce

  have "expectation \<mu> = (\<Sum>\<^sub>ax. prob \<mu> x * x)"
    apply transfer by simp
  also have "\<dots> = (\<Sum>\<^sub>ax\<in>{a..}. prob \<mu> x * x) + (\<Sum>\<^sub>ax\<in>{..<a}. prob \<mu> x * x)"
    apply (subst infsetsum_Un_disjoint[symmetric]) apply auto
    apply (rewrite asm_rl[of "UNIV={a..}\<union>{..<a}"])
    by auto
  also have "\<dots> \<ge> (\<Sum>\<^sub>ax\<in>{a..}. prob \<mu> x * x)" (is "_ \<ge> \<dots>")
    apply (rule add_increasing2)
     apply (rule infsetsum_nonneg)
    using pos apply auto
    by (metis (full_types) mult_less_0_iff not_less prob_geq_0)
  also have "\<dots> \<ge> (\<Sum>\<^sub>ax\<in>{a..}. prob \<mu> x * a)" (is "_ \<ge> \<dots>")
    apply (rule infsetsum_mono, simp, simp)
    apply (rule mult_left_mono)
    by auto
  moreover have "\<dots> = (\<Sum>\<^sub>ax\<in>{a..}. prob \<mu> x) * a"
    by (rule infsetsum_cmult_left, simp)
  moreover have "\<dots> = Prob \<mu> {a..} * a"
    apply transfer by simp
  ultimately have "expectation \<mu> \<ge> \<dots>"
    by auto
  with \<open>a>0\<close> show ?thesis
    using linordered_field_class.pos_le_divide_eq by blast
qed


lemma full_Prob:
  assumes "weight \<mu> = w"
  assumes "supp \<mu> = UNIV"
  assumes "Prob \<mu> A = w"
  shows "A = UNIV"
  using assms
  apply transfer
  apply (rule ccontr)
proof -
  fix \<mu> :: "'a \<Rightarrow> real" and w :: real and A :: "'a set"
  assume "is_distribution \<mu>"
  then have "\<mu> abs_summable_on UNIV" and nneg: "\<mu> x \<ge> 0" for x
    unfolding is_distribution_def by auto
  then have \<mu>_abs_sum: "\<mu> abs_summable_on M" for M
    using abs_summable_on_subset by blast
  assume sum_UNIV: "infsetsum \<mu> UNIV = w"
      and pos: "{x. \<mu> x > 0} = UNIV"
      and sum_A: "infsetsum \<mu> A = w"

  have 0: "infsetsum \<mu> (- A) = 0"
    unfolding Compl_eq_Diff_UNIV
    apply (subst infsetsum_Diff)
    unfolding sum_UNIV sum_A 
    using \<mu>_abs_sum by auto

  assume "A \<noteq> UNIV"
  then obtain x where "x \<in> - A"
    by auto
  have "\<mu> x = 0"
    using 0 \<mu>_abs_sum nneg \<open>x \<in> - A\<close> by (rule infsetsum_0D_real)
  with pos show False
    unfolding Collect_UNIV
    by (metis rel_simps(70))
qed


lemma supp_0[simp]: "supp 0 = {}"
  apply transfer by simp

lemma abs_summable_on_Sigma_project1:
  assumes "(\<lambda>(x,y). f x y) abs_summable_on Sigma A B"
  shows   "(\<lambda>x. infsetsum (\<lambda>y. norm (f x y)) (B x)) abs_summable_on A"
  using assms by (subst (asm) abs_summable_on_Sigma_iff) auto

lemma abs_summable_on_Sigma_project1':
  assumes "(\<lambda>(x,y). f x y) abs_summable_on Sigma A B"
  shows   "(\<lambda>x. infsetsum (\<lambda>y. f x y) (B x)) abs_summable_on A"
  by (intro abs_summable_on_comparison_test' [OF abs_summable_on_Sigma_project1[OF assms]]
        norm_infsetsum_bound)


lemma expectation_exists'_bounded:
  fixes a b :: real
  assumes "\<And>x. x\<in>supp \<mu> \<Longrightarrow> f x \<ge> a"
  assumes "\<And>x. x\<in>supp \<mu> \<Longrightarrow> f x \<le> b"
  shows "expectation_exists' \<mu> f"
  apply (rule expectation_exists_bounded)
  using assms by auto

lemma prob_expectation: "prob (bind_distr \<mu> f) a = expectation' \<mu> (\<lambda>x. prob (f x) a)"
  and prob_expectation_exists: "expectation_exists' \<mu> (\<lambda>x. prob (f x) a)"
  using bind_distr_summable[of \<mu> f a] apply -
   apply (transfer fixing: a) defer apply (transfer fixing: a)
proof -
  fix \<mu> :: "'b\<Rightarrow>real" and f :: "'b\<Rightarrow>'a\<Rightarrow>real"
  assume "is_distribution \<mu>"
  (* assume summ: "(\<lambda>y. \<mu> y * f y a) abs_summable_on UNIV" *)

  have y_preimage: "(\<lambda>x. f x a) -` {y} = {x. f x a = y}" for y
    by blast
  have Sigma: "(SIGMA y:UNIV. {x. f x a = y}) = (\<lambda>x. (f x a, x)) ` UNIV"
    unfolding image_def unfolding Sigma_def by auto

  (* We can make this assumption because of the "using bind_distr_summable[of \<mu> f a] apply -" step before the proof command *)
  assume "(\<lambda>x. \<mu> x * f x a) abs_summable_on UNIV"
  then have "(\<lambda>(x, y). \<mu> y * x) abs_summable_on (\<lambda>x. (f x a, x)) ` UNIV"
    apply (subst abs_summable_on_reindex_iff[symmetric])
     apply (rule injI)
    by auto
  then have summ1: "(\<lambda>(x, y). \<mu> y * x) abs_summable_on (SIGMA y:UNIV. {x. f x a = y})"
    unfolding Sigma by -
  then have "(\<lambda>y. \<Sum>\<^sub>ax|f x a = y. \<mu> x * y) abs_summable_on UNIV"
    by (rule abs_summable_on_Sigma_project1')
  then show "(\<lambda>y. infsetsum \<mu> ((\<lambda>x. f x a) -` {y}) *\<^sub>R y) abs_summable_on UNIV"
    apply simp apply (subst infsetsum_cmult_left[symmetric])
    unfolding y_preimage
    using \<open>is_distribution \<mu>\<close> abs_summable_on_subset is_distribution_def by auto

  have "(\<Sum>\<^sub>ax. \<mu> x * f x a) = (\<Sum>\<^sub>a(x, y)\<in>(\<lambda>x. (f x a, x)) ` UNIV. \<mu> y * x)"
    apply (subst infsetsum_reindex)
     apply (rule injI, simp)
    by (simp add: case_prod_beta)
  also have "\<dots> = (\<Sum>\<^sub>a(x, y)\<in>(SIGMA y:UNIV. {x. f x a = y}). \<mu> y * x)"
    unfolding Sigma by rule
  also have "\<dots> = (\<Sum>\<^sub>ay. \<Sum>\<^sub>ax|f x a = y. \<mu> x * y)"
    apply (subst infsetsum_Sigma')
    using summ1
    by simp_all
  also have "\<dots> = (\<Sum>\<^sub>ay. infsetsum \<mu> ((\<lambda>x. f x a) -` {y}) *\<^sub>R y)"
    apply simp apply (subst infsetsum_cmult_left[symmetric])
    unfolding y_preimage
    using \<open>is_distribution \<mu>\<close> abs_summable_on_subset is_distribution_def by auto
  finally show "(\<Sum>\<^sub>ay. \<mu> y * f y a) = (\<Sum>\<^sub>ax. infsetsum \<mu> ((\<lambda>x. f x a) -` {x}) *\<^sub>R x)"
    by -
qed


lemma Prob_expectation: "Prob (bind_distr \<mu> f) S = expectation' \<mu> (\<lambda>x. Prob (f x) S)"
  unfolding Prob_map_distr bind_distr_map_distr[symmetric]
  by (rule prob_expectation)


lemma Prob_point_distr[simp]: "Prob (point_distr x) S = indicator S x"
  apply (subst Prob_map_distr)
  by simp


lemma expectation'_product_distr1:
  assumes "expectation_exists' \<mu> f"
  shows "expectation' (product_distr \<mu> \<nu>) (\<lambda>(x,y). f x) = weight \<nu> * expectation' \<mu> f"
proof -
  have "expectation' (product_distr \<mu> \<nu>) (\<lambda>(x,y). f x) = (\<Sum>\<^sub>a(x,y). prob \<mu> x * prob \<nu> y * f x)"
    by (simp add: case_prod_beta expectation_map_distr flip: prob_product)
  also have "\<dots> = (\<Sum>\<^sub>ax. prob \<mu> x * f x) * (\<Sum>\<^sub>ay. prob \<nu> y)"
    apply (subst infsetsum_times_product[symmetric])
    (* using True *) using assms
      apply (metis (no_types, lifting) abs_summable_on_cong expectation_exists_map_distr real_scaleR_def)
    using prob_abs_summable apply blast
    by (smt UNIV_Times_UNIV infsetsum_cong mult.commute prod.case_eq_if semiring_normalization_rules(18))
  also have "\<dots> = weight \<nu> * expectation' \<mu> f"
    unfolding expectation_map_distr Prob.rep_eq by simp
  finally show ?thesis
    by -
qed

lemma expectation'_product_distr1'':
  assumes "expectation_exists' \<mu> f"
  shows "expectation' (product_distr \<mu> \<nu>) (\<lambda>x. f (fst x)) = weight \<nu> * expectation' \<mu> f"
  using expectation'_product_distr1 assms unfolding case_prod_beta by auto

lemma expectation'_lower_bound:
  fixes f :: "_\<Rightarrow>real"
  assumes "weight \<mu> = 1 \<or> B \<le> 0"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> f x \<le> C"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> f x \<ge> B"
  shows "expectation' \<mu> f \<ge> B"
  apply (rule expectation_lower_bound)
  using assms by auto

lemma expectation'_upper_bound:
  fixes f :: "_\<Rightarrow>real"
  assumes "weight \<mu> = 1 \<or> B \<ge> 0"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> f x \<ge> C"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> f x \<le> B"
  shows "expectation' \<mu> f \<le> B"
  apply (rule expectation_upper_bound)
  using assms by auto

ML_file "discrete_distributions.ML"

end
