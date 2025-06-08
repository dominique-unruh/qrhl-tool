chapter \<open>Discrete (subprobability) distributions\<close>

theory Discrete_Distributions
  imports Complex_Main "HOL-Library.Rewrite"
    "HOL-Library.Z2" Registers2.Misc_Missing Multi_Transfer
    "Complex_Bounded_Operators.Extra_Ordered_Fields"
    "HOL-Analysis.Infinite_Sum"
    Registers.Misc
begin

declare More_List.no_leading_Cons[rule del, simp del]

definition "is_distribution (f::'a\<Rightarrow>real) \<longleftrightarrow> (\<forall>x. f x \<ge> 0) \<and> f summable_on UNIV \<and> infsum f UNIV \<le> 1"

typedef 'a distr = "{f::'a\<Rightarrow>real. is_distribution f}"
  morphisms prob Abs_distr
  unfolding is_distribution_def
  apply (rule exI[of _ "\<lambda>x. 0"]) by auto
setup_lifting type_definition_distr
(* derive universe distr *)


lemma is_distribution_def': "is_distribution f \<longleftrightarrow> (\<forall>x. f x \<ge> 0) \<and> (\<forall> M. finite M \<longrightarrow> sum f M \<le> 1)"
proof
  assume f[unfolded is_distribution_def]: "is_distribution f"
  have "sum f M \<le> 1" if [simp]: "finite M" for M
  proof -
    have "sum f M = infsum f M"
      using f by simp
    also have "\<dots> \<le> infsum f UNIV"
      using f
      by (smt (verit, del_insts) Diff_iff in_mono infsum_mono_neutral subset_UNIV summable_on_finite that)
    also have "\<dots> \<le> 1"
      using f by simp
    finally show ?thesis.
  qed
  with f show "(\<forall>x. 0 \<le> f x) \<and> (\<forall>M. finite M \<longrightarrow> sum f M \<le> 1)"
    unfolding is_distribution_def by simp
next
  assume assm: "(\<forall>x. 0 \<le> f x) \<and> (\<forall>M. finite M \<longrightarrow> sum f M \<le> 1)"
  then have summable: "f summable_on UNIV"
    apply (rule_tac nonneg_bdd_above_summable_on)
    by auto
  then have "infsum f UNIV \<le> 1"
    apply (rule Infinite_Sum.infsum_le_finite_sums)
    using assm by auto
  with summable show "is_distribution f"
    unfolding is_distribution_def using assm by simp
qed

lemma distr_summable_on:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<forall>x. f x \<ge> 0" and "\<forall> M. finite M \<longrightarrow> sum f M \<le> 1"
  shows "f summable_on E"
  by (meson assms(1) assms(2) is_distribution_def is_distribution_def' summable_on_subset_banach top_greatest)

(* TODO needed? *)
lemma distr_infsum:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<forall>x. f x \<ge> 0" and "\<forall> M. finite M \<longrightarrow> sum f M \<le> 1"
  shows "infsum f UNIV \<le> 1"
proof -
  have summable: "f summable_on UNIV"
    apply (rule nonneg_bdd_above_summable_on)
    using assms by auto
  then show "infsum f UNIV \<le> 1"
    apply (rule Infinite_Sum.infsum_le_finite_sums)
    using assms by auto
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

lemma countable_supp[simp]: "countable (supp \<mu>)"
proof (transfer, auto simp: is_distribution_def)
  fix \<mu> :: "'a => real"
  assume \<mu>pos: "\<forall>x. 0 \<le> \<mu> x" and \<mu>sum: "\<mu> summable_on UNIV"
  then have \<open>\<mu> abs_summable_on UNIV\<close>
    by auto
  then have "countable {x\<in>UNIV. \<mu> x \<noteq> 0}" (is "countable ?X")
    by (rule abs_summable_countable)
  also have "?X = {x. 0 < \<mu> x}"
    using less_eq_real_def \<mu>pos
    by (simp add: dual_order.strict_iff_order)
  finally show "countable {x. 0 < \<mu> x}"
    by simp 
qed

lift_definition uniform :: "'a set \<Rightarrow> 'a distr" is "\<lambda>M. (\<lambda>m. of_bool (m\<in>M) / card M)"
proof (rename_tac M, auto simp: is_distribution_def)
  fix M :: "'a set" and x :: 'a
  have "(\<Sum>m\<in>F. of_bool (m \<in> M) / real (card M)) \<le> 1" if "finite F" for F
  proof (cases "finite M")
    case True
    show ?thesis
      apply (subst sum.mono_neutral_cong_right[where S=\<open>F \<inter> M\<close>])
      by (auto simp: that True card_mono divide_le_eq_1 less_le)
  next
    case False
    show ?thesis
      apply (subst card.infinite[OF False])
      apply (rewrite asm_rl[of "_/real 0 = 0"])
      by auto
  qed 
  then show "(\<lambda>m. of_bool (m \<in> M) / real (card M)) summable_on UNIV"
    and "(\<Sum>\<^sub>\<infinity>m. of_bool (m \<in> M) / real (card M)) \<le> 1"
    by (simp_all add: distr_summable_on distr_infsum)
qed


lemma supp_uniform [simp]: "M \<noteq> {} \<Longrightarrow> finite M \<Longrightarrow> supp (uniform M) = M" for M :: "'a set"
  apply transfer by (auto simp: card_gt_0_iff)

lemma uniform_infinite: "infinite M \<Longrightarrow> uniform M = 0"
  apply transfer by auto

lemma uniform_empty: "uniform {} = 0"
  apply transfer by simp

lift_definition Prob :: "'a distr \<Rightarrow> 'a set \<Rightarrow> real" is infsum .

abbreviation "weight \<mu> == Prob \<mu> UNIV"


lemma weight_supp: 
  assumes "supp \<mu> \<subseteq> S"
  shows "weight \<mu> = Prob \<mu> S"
  using assms apply transfer
  apply (rule infsum_cong_neutral)
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
  assume distr: "(\<forall>x. 0 \<le> \<mu> x) \<and> \<mu> summable_on UNIV \<and> infsum \<mu> UNIV \<le> 1"
  then have "0 \<le> \<mu> x" for x
      using distr by simp
    from distr have "\<mu> summable_on E"
      using summable_on_subset_banach by blast
  assume sum0: "infsum \<mu> E = 0"
  have "\<mu> x = 0" if "x : E" for x
  proof -
    have "\<mu> x = infsum \<mu> {x}"
      by simp
    also have "\<dots> \<le> infsum \<mu> E"
      apply (rule infsum_mono_neutral)
      using \<open>\<mu> summable_on E\<close> that distr by auto
    also have "\<dots> = 0"
      by (fact sum0)
    finally show "\<mu> x = 0"
      using \<open>0 \<le> \<mu> x\<close> by simp
  qed
  then show "disjnt {x. 0 < \<mu> x} E"
    using \<open>0 \<le> \<mu> _\<close> unfolding disjnt_def by auto
next
  fix \<mu> :: "'a\<Rightarrow>real"
  assume distr: "(\<forall>x. 0 \<le> \<mu> x) \<and> \<mu> summable_on UNIV \<and> infsum \<mu> UNIV \<le> 1"
  assume "disjnt {x. 0 < \<mu> x} E"
  then have "\<mu> x = 0" if "x:E" for x
    unfolding disjnt_def distr
    using distr less_eq_real_def that by auto 
  then show "infsum \<mu> E = 0"
    using infsum_0 by blast
qed

lemma Prob_pos[simp]: "Prob \<mu> E \<ge> 0"
  apply transfer
  by (meson infsum_nonneg is_distribution_def summable_on_subset_banach top_greatest)

lemma Prob_mono:
  assumes "E \<subseteq> F"
  shows "Prob \<mu> E \<le> Prob \<mu> F"
proof (transfer fixing: E F, unfold is_distribution_def)
  fix \<mu> :: "'a \<Rightarrow> real"
  assume distr: "(\<forall>x. 0 \<le> \<mu> x) \<and> \<mu> summable_on UNIV \<and> infsum \<mu> UNIV \<le> 1"
  then have "\<mu> summable_on E" and "\<mu> summable_on F"
    using summable_on_subset_banach distr by blast+
  then show "infsum \<mu> E \<le> infsum \<mu> F"
    apply (rule infsum_mono_neutral)
    using assms distr by auto
qed

lemma Prob_leq1[simp]: "Prob \<mu> E \<le> 1"
proof -
  have "Prob \<mu> UNIV \<le> 1"
    apply transfer using is_distribution_def by blast
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
      by (simp add: infsum_0)
  qed
  moreover have "weight (uniform M) = 1" if "M \<noteq> {}" and "finite M"
  proof (transfer fixing: M)
    from that have "(\<Sum>\<^sub>\<infinity>x\<in>M. 1 / real (card M)) = 1"
      by simp
    then show "(\<Sum>\<^sub>\<infinity>m. of_bool (m \<in> M) / real (card M)) = 1"
      by (subst infsum_cong_neutral[where T=M], auto)
  qed
  ultimately show ?thesis
    by auto
qed


lift_definition "map_distr" :: "('a\<Rightarrow>'b) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" 
  is "\<lambda>(f::'a\<Rightarrow>'b) \<mu> x. infsum \<mu> (f -` {x})"
proof (auto simp: is_distribution_def)
  fix f :: "'a \<Rightarrow> 'b" and \<mu> :: "'a \<Rightarrow> real" and x and M :: "'b set"
  assume "(\<forall>x. 0 \<le> \<mu> x)" and summable: "\<mu> summable_on UNIV" and sum: "infsum \<mu> UNIV \<le> 1"
  then have \<mu>pos: "0 \<le> \<mu> x" for x by simp

   have reindex: "bij_betw snd (SIGMA x:M. f -` {x}) (f -` M)" for M
    by (rule bij_betwI, auto)

  have "0 = infsum (\<lambda>_. 0) (f -` {x})" by simp
  also have "\<dots> \<le> infsum \<mu> (f -` {x})"
    apply (rule infsum_mono_neutral)
    using summable summable_on_subset_banach \<mu>pos by auto
  finally show "0 \<le> infsum \<mu> (f -` {x})" .


  {fix M :: "'b set" assume "finite M"
  then have "(\<Sum>x\<in>M. infsum \<mu> (f -` {x})) = (\<Sum>\<^sub>\<infinity>x\<in>M. infsum \<mu> (f -` {x}))" (is "?lhs = _")
    by simp
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>(x, y)\<in>(SIGMA x:M. f -` {x}). \<mu> y)"
    apply (rule infsum_Sigma'_banach)
    unfolding case_prod_beta
    apply (rule summable_on_reindex_bij_betw[OF reindex, THEN iffD2])
    using local.summable summable_on_subset_banach by blast
  also have "\<dots> = infsum \<mu> (f -` M)"
    unfolding case_prod_beta
    by (rule infsum_reindex_bij_betw[OF reindex])
  also have "\<dots> \<le> infsum \<mu> UNIV"
    apply (rule infsum_mono_neutral)
    using \<mu>pos summable apply auto
    by (meson Diff_UNIV Diff_eq_empty_iff local.summable summable_on_subset_banach)
  also have "\<dots> \<le> 1"
    by (fact sum)
  finally have "?lhs \<le> 1" .}
  then show "(\<lambda>x. infsum \<mu> (f -` {x})) summable_on UNIV"
    and "(\<Sum>\<^sub>\<infinity>x. infsum \<mu> (f -` {x})) \<le> 1"
    using \<mu>pos
    by (simp_all add: distr_summable_on distr_infsum infsum_nonneg)
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
  assume \<mu>pos: "\<forall>x. 0 \<le> \<mu> x" and summable: "\<mu> summable_on UNIV" and "infsum \<mu> UNIV \<le> 1"
  have reindex: "bij_betw snd (SIGMA x:UNIV. f -` {x}) UNIV"
    by (rule bij_betwI, auto)
  show "(\<Sum>\<^sub>\<infinity>x. infsum \<mu> (f -` {x})) = infsum \<mu> UNIV"
    apply (subst infsum_Sigma'_banach)
    unfolding case_prod_beta
    using reindex summable apply (rule summable_on_reindex_bij_betw[THEN iffD2])
    using reindex by (subst infsum_reindex_bij_betw, auto)
qed

lemma supp_map_distr[simp]: "supp (map_distr f \<mu>) = f ` (supp \<mu>)"
proof (transfer, auto simp: is_distribution_def)
  fix f :: "'b \<Rightarrow> 'a" and \<mu> :: "'b \<Rightarrow> real" and x :: 'a and y :: 'b
  assume \<mu>pos: "\<forall>x. 0 \<le> \<mu> x" and summable: "\<mu> summable_on UNIV" and "infsum \<mu> UNIV \<le> 1"
  show "0 < infsum \<mu> (f -` {x}) \<Longrightarrow> x \<in> f ` {x. 0 < \<mu> x}"
    using \<mu>pos by (smt image_iff infsum_0 mem_Collect_eq vimage_singleton_eq)
  show "0 < infsum \<mu> (f -` {f y})" if "0 < \<mu> y"
  proof -
    from that have "0 < \<mu> y".
    also have "\<dots> = infsum \<mu> {y}"
      by simp
    also have "\<dots> \<le> infsum \<mu> (f -` {f y})"
      apply (rule infsum_mono_neutral)
      using \<mu>pos apply auto
      using summable summable_on_subset_banach by blast
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
  show "(\<Sum>\<^sub>\<infinity>m\<in>f -` {x}. of_bool (m \<in> A) / real (card A)) = (of_bool (x \<in> B) / real (card B))" 
     (is "?lhs = ?rhs")
  proof (cases "x \<in> B")
    case True
    define R where "R = (f -` {x}) \<inter> -A"
    from True bij obtain y where inv_f: "f -` {x} = {y} \<union> R" and yA: "y \<in> A"
      apply atomize_elim unfolding R_def by (auto simp: bij_betw_def inj_on_def)
    have "?lhs = (\<Sum>\<^sub>\<infinity>m\<in>{y}. if m \<in> A then 1 / real (card A) else 0)"
      unfolding inv_f apply (rule infsum_cong_neutral)
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
    have "?lhs = (\<Sum>\<^sub>\<infinity>m\<in>f -` {x}. 0)"
      apply (rule infsum_cong)
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
  assume "(\<forall>x. 0 \<le> \<mu> x) \<and> \<mu> summable_on UNIV \<and> infsum \<mu> UNIV \<le> 1"
  then have \<mu>pos: "\<forall>x. 0 \<le> \<mu> x" and summable: "\<mu> summable_on UNIV" and "infsum \<mu> UNIV \<le> 1"
    by auto
  have reindex0: "bij_betw snd (SIGMA x:UNIV. f -` {x}) UNIV"
    by (rule bij_betwI, auto)
  have reindex: "bij_betw snd (SIGMA y:g -` {x}. f -` {y}) (f -` g -` {x})"
    by (rule bij_betwI, auto)

  have summable1: "(\<lambda>(x, y). \<mu> y) summable_on (SIGMA y:g -` {x}. f -` {y})"
    unfolding case_prod_beta
    apply (rule summable_on_reindex_bij_betw[OF reindex, THEN iffD2])
    using local.summable summable_on_iff_abs_summable_on_real summable_on_subset_banach by blast

  have "(\<Sum>\<^sub>\<infinity>x\<in>g -` {x}. infsum \<mu> (f -` {x})) = infsum \<mu> (f -` g -` {x})" (is "?lhs = _")
    apply (subst infsum_Sigma'_banach)
     apply (rule summable1)
    unfolding case_prod_beta
    by (subst infsum_reindex_bij_betw[OF reindex], simp)

  also have "\<dots> = infsum \<mu> ((\<lambda>x. g (f x)) -` {x})" (is "_ = ?rhs")
    by (simp add: vimage_def) 
  finally show "?lhs = ?rhs" .
qed

functor map_distr: map_distr using map_distr_id compose_map_distr unfolding o_def id_def by auto


lift_definition expectation_exists :: "'b::real_normed_vector distr \<Rightarrow> bool" is
  "\<lambda>\<mu>::'b\<Rightarrow>real. (\<lambda>x. \<mu> x *\<^sub>R x) abs_summable_on UNIV" .
(* We require absolute summability, otherwise expectation_exists_map_distr and dependent lemmas
  (expectation_mono) become problematic (even if we replace abs_summable_on \<rightarrow> summable_on there, too) *)

lift_definition expectation :: "'a distr \<Rightarrow> 'a::real_normed_vector" is
  "\<lambda>\<mu>::'a\<Rightarrow>real. infsum (\<lambda>x. \<mu> x *\<^sub>R x) UNIV" .
  (* "\<lambda>\<mu>::'a\<Rightarrow>real. if (\<lambda>x. \<mu> x *\<^sub>R x) abs_summable_on UNIV then infsum (\<lambda>x. \<mu> x *\<^sub>R x) UNIV else 0" . *)


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
  assume distr: "(\<forall>x. 0 \<le> \<mu> x) \<and> \<mu> summable_on UNIV \<and> infsum \<mu> UNIV \<le> 1"
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
    apply (rule_tac nonneg_bdd_above_summable_on)
    apply auto by fastforce
qed

(* lemma not_expectation_exists:
  assumes "\<not> expectation_exists \<mu>"
  shows "expectation \<mu> = 0"
  using assms apply transfer by auto *)

lemma expectation_exists_map_distr:
  fixes f :: \<open>'a \<Rightarrow> 'b::real_normed_vector\<close>
  shows "expectation_exists (map_distr f \<mu>) \<longleftrightarrow> (\<lambda>x. prob \<mu> x *\<^sub>R f x) abs_summable_on UNIV"
proof -
  have [simp]: "prob \<mu> summable_on U" for U
    by (metis is_distribution_def mem_Collect_eq prob summable_on_subset_banach top_greatest)
  have \<mu>_scaleR_summ: "(\<lambda>y. prob \<mu> y *\<^sub>R norm x) summable_on f -` {x}" for x
    apply (rule summable_on_scaleR_left) by auto

  have "expectation_exists (map_distr f \<mu>) \<longleftrightarrow> (\<lambda>x. (\<Sum>\<^sub>\<infinity>y\<in>(f -` {x}). prob \<mu> y) *\<^sub>R x) abs_summable_on UNIV"
    apply transfer by simp
  also have "\<dots> \<longleftrightarrow> (\<lambda>x. norm ((\<Sum>\<^sub>\<infinity>y\<in>(f -` {x}). prob \<mu> y) *\<^sub>R x)) abs_summable_on UNIV"
    by fastforce
  also have "\<dots> \<longleftrightarrow> (\<lambda>x. (\<Sum>\<^sub>\<infinity>y\<in>(f -` {x}). prob \<mu> y) *\<^sub>R norm x) abs_summable_on UNIV"
    by (smt (verit, best) norm_ge_zero norm_scaleR real_norm_def summable_on_cong)
  also have "\<dots> \<longleftrightarrow> (\<lambda>x. (\<Sum>\<^sub>\<infinity>y\<in>(f -` {x}). prob \<mu> y *\<^sub>R norm x)) abs_summable_on UNIV"
    apply (subst infsum_scaleR_left) by auto
  also have "\<dots> \<longleftrightarrow> (\<lambda>(x,y). prob \<mu> y *\<^sub>R norm x) abs_summable_on Sigma UNIV (\<lambda>x. f -` {x})"
    apply (subst abs_summable_on_Sigma_iff)
    using \<mu>_scaleR_summ apply simp
    apply (subst (4) abs_pos)
     apply (metis is_distribution_def mem_Collect_eq mult_nonneg_nonneg norm_ge_zero prob)
    apply (subst (2) abs_pos)
     apply (metis is_distribution_def mem_Collect_eq mult_nonneg_nonneg norm_ge_zero prob)
    by auto
  also have "\<dots> \<longleftrightarrow> (\<lambda>(x,y). prob \<mu> y *\<^sub>R norm (f y)) abs_summable_on Sigma UNIV (\<lambda>x. f -` {x})"
    by (smt (verit) SigmaE prod.simps(2) singletonD summable_on_cong vimageE)
  also have "\<dots> \<longleftrightarrow> (\<lambda>x. prob \<mu> x *\<^sub>R norm (f x)) abs_summable_on UNIV"
    apply (subst summable_on_reindex_bij_betw[where A="Sigma UNIV (\<lambda>x. f -` {x})" and g=snd, symmetric])
     apply (rule bij_betwI')
    by (auto simp add: case_prod_beta)
  also have "\<dots> \<longleftrightarrow> (\<lambda>x. norm (prob \<mu> x *\<^sub>R f x)) abs_summable_on UNIV"
    apply (rule summable_on_cong)
    apply auto
    by (simp add: abs_mult_pos)
  also have "\<dots> \<longleftrightarrow> (\<lambda>x. prob \<mu> x *\<^sub>R f x) abs_summable_on UNIV"
    by force
  finally show ?thesis
    by -
qed

lemma expectation_map_distr:
  fixes f :: \<open>'b \<Rightarrow> 'a::banach\<close>
  assumes \<open>expectation_exists (map_distr f \<mu>)\<close>
  shows "expectation (map_distr f \<mu>) = infsum (\<lambda>x. prob \<mu> x *\<^sub>R f x) UNIV"
proof -
  from expectation_exists_map_distr[THEN iffD1, OF assms] and assms show ?thesis
  proof (transfer fixing: f)
    fix \<mu> :: "'b \<Rightarrow> real"
    assume "is_distribution \<mu>"
    then have [simp]: "\<mu> summable_on U" for U
      unfolding is_distribution_def
      using \<open>is_distribution \<mu>\<close> distr_summable_on is_distribution_def' by blast
    assume \<mu>f_summable: "(\<lambda>x. \<mu> x *\<^sub>R f x) abs_summable_on UNIV"

    have "(\<Sum>\<^sub>\<infinity>x. (\<Sum>\<^sub>\<infinity>y\<in>f -` {x}. \<mu> y) *\<^sub>R x) = (\<Sum>\<^sub>\<infinity>x. (\<Sum>\<^sub>\<infinity>y\<in>f -` {x}. \<mu> y *\<^sub>R x))"
      (is "_ = ?rhs")
      apply (rule infsum_cong, simp_all)
      by (rule infsum_scaleR_left[symmetric])
    also 
    have bij: "bij_betw (\<lambda>x. (f x, x)) UNIV (SIGMA x:UNIV. f -` {x})"
      by (rule bij_betwI', auto)
    have "(\<lambda>(x, y). \<mu> y *\<^sub>R x) abs_summable_on (SIGMA x:UNIV. f -` {x})"
      apply (rule summable_on_reindex_bij_betw[where A=UNIV and g="\<lambda>x. (f x, x)", THEN iffD1])
      using bij \<mu>f_summable by auto
    then have "?rhs = (\<Sum>\<^sub>\<infinity>(x, y)\<in>(SIGMA x:UNIV. f -` {x}). \<mu> y *\<^sub>R x)"
      using abs_summable_summable infsum_Sigma'_banach by blast
    also have "\<dots> = (\<Sum>\<^sub>\<infinity>x. \<mu> x *\<^sub>R f x)"
      apply (subst infsum_reindex_bij_betw[where A=UNIV and g="\<lambda>x. (f x, x)", symmetric])
      using bij by auto
    finally show \<open>(\<Sum>\<^sub>\<infinity>x. infsum \<mu> (f -` {x}) *\<^sub>R x) = (\<Sum>\<^sub>\<infinity>x. \<mu> x *\<^sub>R f x)\<close>
      by auto
  qed
qed

lemma expectation_mono:
  fixes f :: "'a\<Rightarrow>real"
  assumes ee_f: "expectation_exists (map_distr f \<mu>)"
  assumes ee_g: "expectation_exists (map_distr g \<mu>)"
  assumes leq: "\<And>x. x\<in>supp \<mu> \<Longrightarrow> f x \<le> g x"
  shows "expectation (map_distr f \<mu>) \<le> expectation (map_distr g \<mu>)"
proof -
  have leq': "prob \<mu> x * f x \<le> prob \<mu> x * g x" for x
    apply (cases "prob \<mu> x = 0")
     apply simp
    using leq[of x]
    by (metis is_distribution_def less_eq_real_def mem_Collect_eq mult.commute mult_right_mono prob supp.rep_eq)
  from ee_f have sumf: "(\<lambda>x. prob \<mu> x * f x) abs_summable_on UNIV"
    apply (subst (asm) expectation_exists_map_distr) by fastforce
  from ee_g have sumg: "(\<lambda>x. prob \<mu> x * g x) abs_summable_on UNIV"
    apply (subst (asm) expectation_exists_map_distr) by fastforce
  show ?thesis
    unfolding expectation_map_distr[OF ee_f] expectation_map_distr[OF ee_g]
    apply (rule infsum_mono)
    using sumf sumg leq' summable_on_iff_abs_summable_on_real by auto
qed

lemma prob_uniform[simp]: "prob (uniform M) m = of_bool (m \<in> M) / card M"
  apply transfer by simp

abbreviation "point_distr x \<equiv> uniform {x}"
lemma expectation_point_distr[simp]: "expectation (point_distr x) = x"
proof -
  have \<open>expectation_exists (point_distr x)\<close>
    apply (transfer fixing: x)
    apply (rule summable_on_cong_neutral[where S=\<open>{x}\<close>, THEN iffD1])
    by auto
  then show ?thesis
    apply (transfer fixing: x)
    apply simp
    apply (subst infsum_cong_neutral[where T=\<open>{x}\<close>])
    by auto
qed

lift_definition "bind_distr" :: "'a distr \<Rightarrow> ('a \<Rightarrow> 'b distr) \<Rightarrow> 'b distr" 
  is "\<lambda>(\<mu>::'a\<Rightarrow>real) (f::'a\<Rightarrow>'b\<Rightarrow>real) x. \<Sum>\<^sub>\<infinity> y\<in>UNIV. \<mu> y * f y x"
  sorry

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
  have "(\<Sum>\<^sub>\<infinity> x'. \<mu> x' * infsum \<nu> (Pair x' -` {(x, y)})) = (\<Sum>\<^sub>\<infinity> x'\<in>{x}. \<mu> x' * infsum \<nu> (Pair x' -` {(x, y)}))" (is "?lhs = _")
    apply (rule infsum_cong_neutral) using nonx by auto
  also have "\<dots> = \<mu> x * infsum \<nu> (Pair x -` {(x, y)})"
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

lemma expectation_uminus: "expectation (map_distr (\<lambda>x. - f x) \<mu>) = - expectation (map_distr f \<mu>)"
proof -
  have [simp]: \<open>inv uminus = (uminus :: 'a\<Rightarrow>_)\<close>
    by (simp add: inv_unique_comp)
  define f\<mu> where \<open>f\<mu> = map_distr f \<mu>\<close>
  have \<open>expectation (map_distr (\<lambda>x. - f x) \<mu>) = expectation (map_distr uminus f\<mu>)\<close>
    unfolding f\<mu>_def by auto
  also have \<open>\<dots> = - expectation f\<mu>\<close>
    apply transfer
    apply (auto simp: bij_uminus bij_vimage_eq_inv_image)
    apply (subst infsum_reindex_bij_betw[symmetric, where g=uminus])
    by (auto intro!: bij_uminus infsum_uminus)
  finally show \<open>expectation' \<mu> (\<lambda>x. - f x) = - expectation f\<mu>\<close>
    by -
qed

lemma expectation_upper_bound:
  fixes \<mu> :: "real distr"
  assumes "weight \<mu> = 1 \<or> B \<ge> 0"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> x \<ge> C"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> x \<le> B"
  shows "expectation \<mu> \<le> B"
  using assms 
proof (transfer fixing: B C, unfold is_distribution_def)
  fix \<mu> :: "real\<Rightarrow>real"
  assume \<mu>1_or_Bpos: "infsum \<mu> UNIV = 1 \<or> 0 \<le> B"
  assume \<mu>: "(\<forall>x. 0 \<le> \<mu> x) \<and> \<mu> summable_on UNIV \<and> infsum \<mu> UNIV \<le> 1"
  then have \<mu>sum: "\<mu> summable_on UNIV" and \<mu>sum1: "infsum \<mu> UNIV \<le> 1" and \<mu>pos: "\<mu> x \<ge> 0" for x
    by auto
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
    by (metis mult.commute mult_right_mono mult_zero_right)
  have "(\<lambda>x. \<mu> x * BC) abs_summable_on UNIV"
    by (metis \<mu> summable_on_cmult_left summable_on_iff_abs_summable_on_real)
  then have sum\<mu>f: "(\<lambda>x. \<mu> x * x) abs_summable_on UNIV"
    apply (rule abs_summable_on_comparison_test)
    by (smt (verit, best) abs_f\<mu>x real_norm_def)
  have sum\<mu>B: "(\<lambda>x. \<mu> x * B) abs_summable_on UNIV"
    by (metis \<mu> summable_on_cmult_left summable_on_iff_abs_summable_on_real)

  have "(\<Sum>\<^sub>\<infinity>x. \<mu> x *\<^sub>R x) = (\<Sum>\<^sub>\<infinity>x. \<mu> x * x)" 
    by simp
  also have "\<dots> \<le> (\<Sum>\<^sub>\<infinity>x. \<mu> x * B)"
    apply (rule infsum_mono)
    using sum\<mu>f sum\<mu>B \<mu>FB
    using summable_on_iff_abs_summable_on_real by auto
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>x. \<mu> x) * B"
    using infsum_cmult_left' by blast
  also from \<mu>sum1 \<mu>1_or_Bpos have "\<dots> \<le> B"
    by (auto simp: mult_left_le ordered_field_class.sign_simps(5))
  finally show "(\<Sum>\<^sub>\<infinity>x. \<mu> x *\<^sub>R x) \<le> B" by simp
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

lemma prob_bind_distr: "prob (bind_distr \<mu> f) x = (\<Sum>\<^sub>\<infinity> y\<in>UNIV. prob \<mu> y * prob (f y) x)"
  apply transfer by simp

lemma Prob_singleton[simp]: "Prob D {x} = prob D x"
  apply transfer by simp

lemma prob_leq1[simp]: "prob \<mu> x \<le> 1"
  by (simp flip: Prob_singleton)


lemma bind_distr_summable: "(\<lambda>y. prob \<mu> y * prob (f y) x) summable_on UNIV"
  apply (rule local_defE[of "bind_distr \<mu> f"], rename_tac \<mu>f)
  apply (rule abs_summable_summable)
  apply (subgoal_tac "\<And>x y. prob (f y) x \<le> 1")
   apply transfer
   apply (rule_tac g=\<mu> in abs_summable_on_comparison_test)
  using is_distribution_def summable_on_iff_abs_summable_on_real apply auto
  by (simp_all add: is_distribution_def mult_left_le)

lemma prob_geq_0[simp]: "prob \<mu> f \<ge> 0"
  apply transfer by (auto simp: is_distribution_def)

lemma prob_summable: "prob \<mu> summable_on UNIV"
  apply transfer unfolding is_distribution_def
  using distr_summable_on by blast

lemma prob_abs_summable[simp]: \<open>prob \<mu> abs_summable_on UNIV\<close>
  apply transfer
  by (auto simp: is_distribution_def)

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
    also have "prob (bind_distr \<mu> f) y = (\<Sum>\<^sub>\<infinity> x\<in>UNIV. prob \<mu> x * prob (f x) y)"
      unfolding prob_bind_distr by simp
    finally obtain x where "prob \<mu> x * prob (f x) y \<noteq> 0"
      by (smt infsum_0)
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
    have "(\<Sum>\<^sub>\<infinity> x\<in>UNIV. prob \<mu> x * prob (f x) y) \<ge> (\<Sum>\<^sub>\<infinity> x\<in>{x}. prob \<mu> x * prob (f x) y)" (is "_ \<ge> \<dots>")
      apply (rule infsum_mono_neutral)
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
  moreover have "infsum D UNIV \<le> 1"
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
  by (metis infsum_nonneg is_distribution_def max_def min.commute min.orderE)

lemma bind_distr_const[simp]:
  shows "bind_distr \<mu> (\<lambda>x. \<nu>) = weight \<mu> *\<^sub>R \<nu>"
  apply (transfer, rule ext)
  apply (subst max_absorb2)
   apply (meson infsum_nonneg is_distribution_def)
  apply (subst min_absorb2)
  using is_distribution_def apply blast
  using infsum_cmult_left is_distribution_def by fastforce

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

  have \<mu>sumgeq0: "infsum \<nu> UNIV \<ge> 0"
    using \<nu> unfolding is_distribution_def
    by (simp add: infsum_nonneg)
  have maxmin: "min 1 (max 0 (infsum \<nu> (UNIV))) = infsum \<nu> UNIV"
    apply (subst min_absorb2)
    using \<nu> unfolding is_distribution_def apply simp
    using \<mu>sumgeq0 by simp

  have "(\<Sum>\<^sub>\<infinity>xy\<in>fst -` {x}. \<Sum>\<^sub>\<infinity>x. \<mu> x * infsum \<nu> (Pair x -` {xy})) = (\<Sum>\<^sub>\<infinity>xy\<in>range (Pair x). \<Sum>\<^sub>\<infinity>x. \<mu> x * infsum \<nu> (Pair x -` {xy}))"
    by (rewrite at _ asm_rl[of "fst -` {x} = Pair x ` UNIV"], auto)
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. \<Sum>\<^sub>\<infinity>x'. \<mu> x' * infsum \<nu> (Pair x' -` {(x, y)}))"
    apply (subst infsum_reindex)
    by (auto simp add: inj_on_def o_def)
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. \<Sum>\<^sub>\<infinity>x'\<in>{x}. \<mu> x' * infsum \<nu> (Pair x' -` {(x, y)}))"
    apply (rule infsum_cong)
     apply (rule infsum_cong_neutral)
       apply auto
    by (meson Pair_inject infsum_0 vimage_singleton_eq)
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. \<mu> x * infsum \<nu> (Pair x -` {(x, y)}))"
    by auto
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. \<mu> x * infsum \<nu> {y})"
    by (subgoal_tac "\<And>y::'b. Pair x -` {(x, y)} = {y}", auto)
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. \<mu> x * \<nu> y)"
    by simp
  also have "\<dots> = \<mu> x * (\<Sum>\<^sub>\<infinity>y. \<nu> y)"
    using \<open>is_distribution \<nu>\<close> infsum_cmult_right is_distribution_def by blast
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. \<nu> y) * \<mu> x"
    by simp
  also have "\<dots> = (min 1 (max 0 (infsum \<nu> (UNIV::'b set))) * \<mu> x)"
    unfolding maxmin by simp

  finally show "(\<Sum>\<^sub>\<infinity>x\<in>fst -` {x}. \<Sum>\<^sub>\<infinity>y. \<mu> (y::'a) * infsum \<nu> (Pair y -` {x}))
                  = (min 1 (max 0 (infsum \<nu> (UNIV::'b set))) * \<mu> x)"
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
  apply (rule infsum_Un_Int)
  by (simp_all add: distr_summable_on is_distribution_def')

lemma Prob_setdiff: "Prob \<mu> (A-B) = Prob \<mu> A - Prob \<mu> B + Prob \<mu> (B-A)"
proof (transfer fixing: A B)
  fix \<mu> :: "'a \<Rightarrow> real"
  assume \<mu>: "is_distribution \<mu>"

  have Bsplit: "B = (B-A) \<union> (B\<inter>A)"
    by (simp add: Un_Diff_Int)
  have 1: "infsum \<mu> B = infsum \<mu> (B-A) + infsum \<mu> (B\<inter>A)"
    apply (rewrite at "infsum _ \<hole>" Bsplit)
    apply (rule infsum_Un_disjoint)
    apply auto
    by (meson \<mu> distr_summable_on is_distribution_def')+

  have "infsum \<mu> (A - B) = infsum \<mu> (A - (B\<inter>A))"
    by (metis Diff_Compl Diff_Diff_Int Diff_eq Int_commute)
  also have "\<dots> = infsum \<mu> A - infsum \<mu> (B\<inter>A)"
    apply (rule infsum_Diff)
    apply auto
    by (meson \<mu> distr_summable_on is_distribution_def')+
  also have "\<dots> = infsum \<mu> A - (infsum \<mu> B - infsum \<mu> (B-A))"
    using 1 by linarith
  finally show "infsum \<mu> (A - B) = infsum \<mu> A - infsum \<mu> B + infsum \<mu> (B - A)"
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
  fix x :: 'a
    and D :: "'a \<Rightarrow> 'b \<Rightarrow> real"
  assume "pred_fun \<top> is_distribution D"
  then have distr: "is_distribution (D i)" for i
    by simp
  assume sum1: "infsum (D i) UNIV = 1" if "i \<noteq> x" for i
  define PIE :: "_ \<Rightarrow> _ \<Rightarrow> ('a\<Rightarrow>'b) set" where "PIE F y = PiE F (\<lambda>z. if z=x then {y} else UNIV)" for F y
  have PiE: "(\<lambda>f. f x) -` {y} = PiE UNIV (\<lambda>z. if z=x then {y} else UNIV)" for y :: 'b
    apply auto
    by (smt PiE_iff UNIV_I singletonD)
  have "(\<Sum>\<^sub>\<infinity>f\<in>(\<lambda>f. f x) -` {y}. \<Prod>x'\<in>UNIV. D x' (f x')) = (\<Prod>x'\<in>UNIV. infsum (D x') (if x' = x then {y} else UNIV))" for y
    apply (subst PiE)
    apply (subst infsum_prod_PiE_abs)
      apply auto
    by (smt (verit, ccfv_threshold) distr is_distribution_def summable_on_cong)
  also have "\<dots>y = (\<Prod>x'\<in>{x}. infsum (D x') (if x' = x then {y} else UNIV))" for y
    apply (rule prod.mono_neutral_right)
    using sum1 by auto
  also have "\<dots>y = D x y" for y
    by simp
  finally
  show "(\<lambda>y. \<Sum>\<^sub>\<infinity>f\<in>(\<lambda>f. f x) -` {y}. \<Prod>x\<in>UNIV. D x (f x)) = D x"
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
  sorry

lemma bind_distr_point_distr[simp]: "bind_distr D point_distr = D"
proof (transfer, rule ext)
  fix D :: "'a \<Rightarrow> real" and x :: 'a
  assume "is_distribution D"
  have "(\<Sum>\<^sub>\<infinity>y. D y * (of_bool (x \<in> {y}) / real (card {y}))) = (\<Sum>\<^sub>\<infinity>y\<in>{x}. D y)"
    apply (rule infsum_cong_neutral) by auto
  also have "\<dots> = D x"
    by auto
  finally show "(\<Sum>\<^sub>\<infinity>y. D y * (of_bool (x \<in> {y}) / real (card {y}))) = D x"
    by simp
qed

lemma distribution_leq1: assumes "is_distribution \<mu>" shows "\<mu> x \<le> 1"
proof -
  have "\<mu> x = infsum \<mu> {x}"
    by auto
  also have "\<dots> \<le> infsum \<mu> UNIV"
    apply (rule infsum_mono_neutral)
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
  assume f: "pred_fun \<top> is_distribution f"
  then have fpos: "(0 \<le> f y x)" and fy_sum: "f y abs_summable_on UNIV" and fy_sum1: "infsum (f y) UNIV \<le> 1" for y x
    by (auto simp: is_distribution_def)
  from f have fyx1: "f y x \<le> 1" for y x
    by (auto simp: is_distribution_def intro: distribution_leq1)
  assume \<mu>f_def: "\<mu>f = (\<lambda>x. \<Sum>\<^sub>\<infinity>y. \<mu> y * f y x)"
  assume \<mu>f: "is_distribution \<mu>f"
  then have summable1: "(\<lambda>x. \<Sum>\<^sub>\<infinity>y. \<mu> y * f y x) abs_summable_on UNIV"
    unfolding \<mu>f_def is_distribution_def by simp
  have summable2: "(\<lambda>y. \<mu> y * f y x) abs_summable_on UNIV" for x
    apply (rule abs_summable_on_comparison_test[where g="\<mu>"])
    using \<mu>[unfolded is_distribution_def] apply simp_all
    using fyx1 fpos by (simp add: mult_left_le)
  have prod_summable: "(\<lambda>(x, y). \<mu> y * f y x) abs_summable_on UNIV \<times> UNIV"
    apply (rule abs_summable_on_Sigma_iff[THEN iffD2])
    using summable2 apply auto
    by (smt (verit, ccfv_SIG) \<mu> \<mu>f \<mu>f_def fpos infsum_cong is_distribution_def mult_nonneg_nonneg summable_on_cong)
  have "(\<Sum>\<^sub>\<infinity>y. \<mu> y * (\<Sum>\<^sub>\<infinity>x\<in>g -` {x}. f y x)) = (\<Sum>\<^sub>\<infinity>y. \<Sum>\<^sub>\<infinity>x\<in>g -` {x}. \<mu> y * f y x)"
    apply (subst infsum_cmult_right)
     apply (rule abs_summable_summable)
     apply (metis fy_sum subset_UNIV summable_on_subset_banach)
    by blast
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>g -` {x}. \<Sum>\<^sub>\<infinity>y. \<mu> y * f y x)"
    apply (rule infsum_swap_banach[symmetric])
    apply (rule summable_on_subset_banach[where A=UNIV])
    using prod_summable summable_on_iff_abs_summable_on_real by auto
  finally show "(\<Sum>\<^sub>\<infinity>y. (\<mu> y) * (\<Sum>\<^sub>\<infinity>x\<in>g -` {x}. f y x)) 
      = (\<Sum>\<^sub>\<infinity>x\<in>g -` {x}. \<Sum>\<^sub>\<infinity>y. \<mu> y * f y x)" .
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
  unfolding is_distribution_def 
  apply auto
   apply (rule summable_on_iff_abs_summable_on_real[THEN iffD2])
   apply (rule_tac g="fun" in abs_summable_on_comparison_test)
  apply auto
  by (smt (verit, best) infsum_mono infsum_not_exists)

lemma bind_distr_cong:
  assumes "\<And>x. x\<in>supp \<mu> \<Longrightarrow> f x = g x"
  shows "bind_distr \<mu> f = bind_distr \<mu> g"
  using assms apply transfer apply (rule ext)
  apply (rule infsum_cong_neutral)
  apply (auto simp: is_distribution_def)
  by (metis order_trans_rules(17))

lemma supp_restrict_distr[simp]:
  "supp (restrict_distr \<mu> S) = S \<inter> supp \<mu>"
  apply transfer by auto

lemma Prob_restrict_distr[simp]:
  "Prob (restrict_distr \<mu> S) T = Prob \<mu> (S\<inter>T)"
  apply transfer
  apply (rule infsum_cong_neutral)
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
  apply (rule local_defE[where y=\<open>bind_distr (restrict_distr \<mu> E) f\<close>], rename_tac b1) (* Makes transfer add some additional facts about the result of bind_distr *)
  apply (rule local_defE[where y=\<open>bind_distr (restrict_distr \<mu> (-E)) f\<close>], rename_tac b2)
proof (transfer fixing: E x, simp)
  fix f :: \<open>'b \<Rightarrow> 'a \<Rightarrow> real\<close> and \<mu> :: \<open>'b \<Rightarrow> real\<close>
  assume assms: \<open>is_distribution \<mu>\<close> \<open>\<forall>x. is_distribution (f x)\<close>

  have \<open>f y x \<le> 1\<close> for y
    by (simp add: assms distribution_leq1)

  have *: \<open>(\<lambda>y. if y \<in> E then \<mu> y else 0) abs_summable_on UNIV\<close>
    by (smt (verit, ccfv_threshold) \<open>is_distribution \<mu>\<close> distr_summable_on is_distribution_def' real_norm_def sum_mono)
  have summable1: \<open>(\<lambda>y. (if y \<in> E then \<mu> y else 0) * f y x) summable_on UNIV\<close>
    apply (rule summable_on_iff_abs_summable_on_real[THEN iffD2])
    using * apply (rule abs_summable_on_comparison_test)
    by (metis \<open>\<And>y. f y x \<le> 1\<close> abs_of_nonneg assms(2) is_distribution_def mult_left_le norm_ge_zero norm_mult real_norm_def)
    
  have *: \<open>(\<lambda>y. if y \<in> - E then \<mu> y else 0) abs_summable_on UNIV\<close>
    by (smt (verit, ccfv_threshold) \<open>is_distribution \<mu>\<close> distr_summable_on is_distribution_def' real_norm_def sum_mono)
  have summable2: \<open>(\<lambda>y. (if y \<notin> E then \<mu> y else 0) * f y x) summable_on UNIV\<close>
    apply (rule summable_on_iff_abs_summable_on_real[THEN iffD2])
    using * apply (rule abs_summable_on_comparison_test)
    by (smt (z3) Compl_iff \<open>\<And>y. f y x \<le> 1\<close> assms(1) assms(2) is_distribution_def mult_left_le mult_nonneg_nonneg real_norm_def)

  show \<open>(\<Sum>\<^sub>\<infinity>y. \<mu> y * f y x) = (\<Sum>\<^sub>\<infinity>y. (if y \<in> E then \<mu> y else 0) * f y x) + (\<Sum>\<^sub>\<infinity>y. (if y \<notin> E then \<mu> y else 0) * f y x)\<close>
    apply (subst infsum_add[symmetric])
    using summable1 summable2 by (auto intro!: infsum_cong)
qed

lemma weight1_bind_distr[simp]:
  shows "weight (bind_distr \<mu> f) = 1 \<longleftrightarrow> weight \<mu> = 1 \<and> (\<forall>x\<in>supp \<mu>. weight (f x) = 1)"
proof (rule local_defE[of "bind_distr \<mu> f"], rename_tac \<mu>f, transfer)
  fix \<mu>f :: "'a \<Rightarrow> real"
    and \<mu> :: "'b \<Rightarrow> real"
    and f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assume \<mu>: "is_distribution \<mu>"
  then have \<mu>pos: "\<mu> x \<ge> 0" for x by (simp add: is_distribution_def)
  assume f: "pred_fun \<top> is_distribution f"
  then have fpos[simp]: "0 \<le> f y x" and fy_sum: "f y abs_summable_on UNIV"
    and fy_sum1: "infsum (f y) UNIV \<le> 1" 
    for y x
    by (auto simp: is_distribution_def)
  from f have fyx1: "f y x \<le> 1" for y x 
    by (auto simp: distribution_leq1)
(*   from fy_sum1 fy_sum fpos have fyx1: "f y x \<le> 1" for y x
  proof -
    have "f y x = infsum (f y) {x}"
      by auto
    also have "\<dots> \<le> infsum (f y) UNIV"
      apply (rule infsum_mono_neutral_left)
      using fy_sum by auto
    also have "\<dots> \<le> 1"
      using fy_sum1 by simp
    finally show ?thesis.
  qed *)
  assume \<mu>f_def: "\<mu>f = (\<lambda>x. \<Sum>\<^sub>\<infinity>y. \<mu> y * f y x)"
  assume \<mu>f: "is_distribution \<mu>f"
  then have summable1: "(\<lambda>x. \<Sum>\<^sub>\<infinity>y. \<mu> y * f y x) abs_summable_on UNIV"
    unfolding \<mu>f_def is_distribution_def by simp
  have summable2: "(\<lambda>y. \<mu> y * f y x) abs_summable_on UNIV" for x
    apply (rule abs_summable_on_comparison_test[where g="\<mu>"])
    using \<mu>[unfolded is_distribution_def] apply simp_all
    using fyx1 mult_left_le by blast
  have prod_summable: "(\<lambda>(x, y). \<mu> y * f y x) abs_summable_on UNIV \<times> UNIV"
    apply (rule abs_summable_on_Sigma_iff[THEN iffD2])
    using summable2 apply auto
    by (smt (verit, ccfv_SIG) \<mu>f \<mu>f_def \<mu>pos fpos infsum_cong is_distribution_def mult_nonneg_nonneg summable_on_cong)
  show "((\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. \<mu> y * f y x) = 1) \<longleftrightarrow>
       (infsum \<mu> UNIV = 1 \<and> (\<forall>x\<in>{x. 0 < \<mu> x}. infsum (f x) UNIV = 1))"
  proof
    assume assm[symmetric]: "(\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. \<mu> y * f y x) = 1" (is "\<dots> = _")
    also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. \<Sum>\<^sub>\<infinity>x. \<mu> y * f y x)"
      apply (rule infsum_swap_banach)
      using prod_summable summable_on_iff_abs_summable_on_real by blast
    also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. \<mu> y * (\<Sum>\<^sub>\<infinity>x. f y x))"
      apply (rule infsum_cong)
      using infsum_cmult_right' by blast
    also 
    note calc_start = calculation
    have "\<dots> \<le> (\<Sum>\<^sub>\<infinity>y. \<mu> y)"
      apply (rule infsum_mono)
      using calculation infsum_not_exists apply force
      using \<mu> is_distribution_def apply blast
      using \<mu>pos fy_sum1 mult_left_le by blast
    finally have "infsum \<mu> UNIV = 1"
      using \<mu>[unfolded is_distribution_def] by linarith

    moreover have "infsum (f y) UNIV = 1" if "0 < \<mu> y" for y
    proof (rule ccontr)
      assume "infsum (f y) UNIV \<noteq> 1"
      then have less1: "infsum (f y) UNIV < 1"
        using fy_sum1 le_less by blast
      from calc_start have "1 = (\<Sum>\<^sub>\<infinity>y. \<mu> y * infsum (f y) UNIV)".
      also have "\<dots> = (\<Sum>\<^sub>\<infinity>y\<in>-{y}. \<mu> y * infsum (f y) UNIV) + \<mu> y * infsum (f y) UNIV"
        apply (subst Compl_partition2[symmetric, where A="{y}"], subst infsum_Un_disjoint)
           apply (metis (full_types) add.inverse_neutral calc_start infsum_not_exists less_minus_one_simps(2) less_numeral_extra(4) subset_UNIV summable_on_subset_banach)
        by auto
      also have "\<dots> < (\<Sum>\<^sub>\<infinity>y\<in>-{y}. \<mu> y * infsum (f y) UNIV) + \<mu> y"
        apply (rule add_strict_left_mono)
        using less1 that by simp
      also have "\<dots> \<le> (\<Sum>\<^sub>\<infinity>y\<in>-{y}. \<mu> y) + \<mu> y"
        apply (rule add_right_mono)
        apply (rule infsum_mono)
        apply (metis (full_types) calc_start infsum_not_exists summable_on_subset_banach top_greatest zero_neq_one)
        apply (meson \<mu> distr_summable_on is_distribution_def')
        using \<mu>pos fy_sum1 mult_left_le by blast
      also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. \<mu> y)"
        apply (subst Compl_partition2[symmetric, where A="{y}"], subst infsum_Un_disjoint)
        apply (meson \<mu> distr_summable_on is_distribution_def')
        by auto
      also have "\<dots> \<le> 1"
        using \<mu>[unfolded is_distribution_def] by blast
      finally have "1 < 1" by simp
      then show False by auto
    qed
    ultimately show "infsum \<mu> UNIV = 1 \<and> (\<forall>x\<in>{x. 0 < \<mu> x}. infsum (f x) UNIV = 1)"
      by auto
  next
    assume assm: "infsum \<mu> UNIV = 1 \<and> (\<forall>x\<in>{x. 0 < \<mu> x}. infsum (f x) UNIV = 1)"
    have "(\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. \<mu> y * f y x) = (\<Sum>\<^sub>\<infinity>y. \<Sum>\<^sub>\<infinity>x. \<mu> y * f y x)"
      apply (rule infsum_swap_banach)
      using prod_summable summable_on_iff_abs_summable_on_real by blast
    also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. \<mu> y * (\<Sum>\<^sub>\<infinity>x. f y x))"
      apply (rule infsum_cong)
      apply (rule infsum_cmult_right)
      using fy_sum by simp
    also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. \<mu> y)"
      using assm apply auto
      by (smt \<mu>[unfolded is_distribution_def] infsum_cong mult_cancel_left2)
    also have "\<dots> = 1"
      using assm by simp
    finally show "(\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. \<mu> y * f y x) = 1".
  qed
qed

lemma Prob_complement: "Prob \<mu> (-E) = weight \<mu> - Prob \<mu> E"
  apply (transfer fixing: E)
  apply (rewrite at UNIV asm_rl[of "UNIV = -E \<union> E"], simp)
  apply (rule add_implies_diff)
  apply (rule infsum_Un_disjoint[symmetric])
  by (auto simp add: distr_summable_on is_distribution_def')

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
      using divide_le_eq_1 by fastforce
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
  using divide_less_cancel by force

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
    show "(\<Sum>\<^sub>\<infinity>m\<in>f -` {y}. of_bool (m \<in> A) / real (card A)) = of_bool (y \<in> B) / real (card B)" 
      (is "?lhs = ?rhs") for y
    proof (cases "y \<in> B")
      case True
      define R where "R = (f -` {y}) \<inter> -A"
      from reg_n have card_y: "card (f -` {y} \<inter> A) = n" and "n\<noteq>0"
        unfolding regular_betw_n_def apply auto
        using True by blast
      then have fin_y: "finite (f -` {y} \<inter> A)"
        by (meson card_eq_0_iff)
      have "?lhs = (\<Sum>\<^sub>\<infinity>m\<in>f-`{y} \<inter> A. 1 / real (card A))"
        apply (rule infsum_cong_neutral)
        by auto
      also have "\<dots> = (\<Sum>m\<in>f-`{y} \<inter> A. 1 / real (card A))"
        using fin_y by (rule infsum_finite)
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
      have "?lhs = (\<Sum>\<^sub>\<infinity>m\<in>f -` {y}. 0)"
        apply (rule infsum_cong)
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
  sorry

lemma product_distr'_uniform[simp]:
  "product_distr' (\<lambda>m. uniform (S m)) = uniform {f. \<forall>m. f m \<in> S m}"
  sorry

lemma product_distr'_point_distr[simp]:
  "product_distr' (\<lambda>i. point_distr (f i)) = point_distr f"
  apply simp
  apply (rewrite asm_rl[of "{fa. \<forall>i. fa i = f i} = {f}"])
  by auto

lemma bind_point_distr[simp]: "bind_distr D (\<lambda>d. point_distr (f d)) = map_distr f D"
  sorry

lemma point_distr_bind[simp]: "bind_distr (point_distr x) f = f x"
  apply transfer apply auto
  sorry

lemma map_product_distr':
  shows "map_distr (\<lambda>D i. F (D i) i) (product_distr' G)
         = product_distr' (\<lambda>i. map_distr (\<lambda>d. F d i) (G i))"
  unfolding bind_point_distr[symmetric] product_distr'_point_distr[symmetric]
  by (subst bind_product_distr', rule)

lemma total_product_distr'I:
  assumes "\<And>x. weight (f x) = 1"
  shows "weight (product_distr' f) = 1"
  sorry

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
  sorry

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
    = (\<Sum>\<^sub>\<infinity>y. prob \<mu> y * (let p' = min (max y 0) 1 in (\<lambda>b::bit. if b = 0 then 1 - p' else p')) 1)"
    apply transfer by rule
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. prob \<mu> y * y)"
  proof (rule infsum_cong)
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
  qed
  also have "\<dots> = expectation \<mu>"
    apply transfer by simp
  finally show ?thesis
    by -
qed


lemma map_distr_point_distr[simp]:
  "map_distr f (point_distr x) = point_distr (f x)"
proof (transfer fixing: f, rule ext, rename_tac x y)
  fix x y
  have "(\<Sum>\<^sub>\<infinity>m\<in>f -` {y}. of_bool (m \<in> {x}) / real (card {x}))
      = (\<Sum>\<^sub>\<infinity>m\<in>{m. m=x \<and> f m = y}. if m=x then 1 else 0)"
    by (rule infsum_cong_neutral, auto)
  also have "\<dots> = (if f x = y then 1 else 0)"
    apply (cases "f x = y")
     apply auto
    apply (subst asm_rl[of \<open>{m. m = x \<and> f m = f x} = {x}\<close>])
    by auto
  also have "\<dots> = of_bool (y \<in> {f x}) / real (card {f x})"
    by auto
  finally show "(\<Sum>\<^sub>\<infinity>m\<in>f -` {y}. of_bool (m \<in> {x}) / real (card {x})) = of_bool (y \<in> {f x}) / real (card {f x})"
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
  have "Prob (uniform A) B = (\<Sum>\<^sub>\<infinity>m\<in>A\<inter>B. 1 / real (card A))"
    apply transfer
    apply (rule infsum_cong_neutral)
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


lemma prob_map_distr: "prob (map_distr f \<mu>) x = infsum (prob \<mu>) (f -` {x})"
  apply transfer by simp


lemma markov_inequality:
  assumes exp_ex: "expectation_exists \<mu>"
  assumes supp: "supp \<mu> \<subseteq> {0..}"
  assumes "a > 0"
  shows "Prob \<mu> {a..} \<le> expectation \<mu> / a"
proof -
  have [simp]: "(\<lambda>x. prob \<mu> x * a) abs_summable_on A" for A
    by (metis prob_summable UNIV_I subsetI summable_on_cmult_left summable_on_iff_abs_summable_on_real summable_on_subset_banach)
  from exp_ex have exp_ex[simp]: "(\<lambda>x. prob \<mu> x * x) abs_summable_on A" for A
    unfolding expectation_exists.rep_eq
    apply auto
    using summable_on_subset_banach by blast
  have pos: "prob \<mu> x = 0" if "x < 0" for x
    using supp supp_prob' that by fastforce

  have "expectation \<mu> = (\<Sum>\<^sub>\<infinity>x. prob \<mu> x * x)"
    apply transfer by simp
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>{a..}. prob \<mu> x * x) + (\<Sum>\<^sub>\<infinity>x\<in>{..<a}. prob \<mu> x * x)"
    apply (subst infsum_Un_disjoint[symmetric])
    using exp_ex summable_on_iff_abs_summable_on_real apply blast
    using exp_ex summable_on_iff_abs_summable_on_real apply blast
    apply (simp add: disjoint_iff_not_equal)
    by (smt (verit) Collect_cong UNIV_def Un_def atLeast_iff lessThan_iff)
  also have "\<dots> \<ge> (\<Sum>\<^sub>\<infinity>x\<in>{a..}. prob \<mu> x * x)" (is "_ \<ge> \<dots>")
    apply (rule add_increasing2)
     apply (rule infsum_nonneg)
    using pos apply auto
    by (metis linorder_not_le mult_less_0_iff prob_geq_0)
  also have "\<dots> \<ge> (\<Sum>\<^sub>\<infinity>x\<in>{a..}. prob \<mu> x * a)" (is "_ \<ge> \<dots>")
    apply (rule infsum_mono)
    apply (metis prob_summable summable_on_cmult_left summable_on_subset_banach top_greatest)
    using exp_ex summable_on_iff_abs_summable_on_real apply blast
    apply (rule mult_left_mono)
    by auto
  moreover have "\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>{a..}. prob \<mu> x) * a"
    apply (rule infsum_cmult_left)
    by (meson prob_summable subset_UNIV summable_on_subset_banach)
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
    using summable_on_subset_banach by blast
  assume sum_UNIV: "infsum \<mu> UNIV = w"
      and pos: "{x. \<mu> x > 0} = UNIV"
      and sum_A: "infsum \<mu> A = w"

  have 0: "infsum \<mu> (- A) = 0"
    unfolding Compl_eq_Diff_UNIV
    apply (subst infsum_Diff)
    unfolding sum_UNIV sum_A 
    using \<open>is_distribution \<mu>\<close> is_distribution_def apply auto
    using \<mu>_abs_sum summable_on_iff_abs_summable_on_real by blast

  assume "A \<noteq> UNIV"
  then obtain x where "x \<in> - A"
    by auto
  have "\<mu> x = 0"
    using 0 \<open>x \<in> - A\<close>
    by (metis \<open>is_distribution \<mu>\<close> distr_summable_on dual_order.refl is_distribution_def' nonneg_infsum_le_0D)
  with pos show False
    unfolding Collect_UNIV
    by (metis rel_simps(70))
qed


lemma supp_0[simp]: "supp 0 = {}"
  apply transfer by simp

(* TODO move? erase? rename? *)
lemma abs_summable_on_Sigma_project1:
  assumes "(\<lambda>(x,y). f x y) abs_summable_on Sigma A B"
  shows   "(\<lambda>x. infsum (\<lambda>y. norm (f x y)) (B x)) abs_summable_on A"
  using assms by (subst (asm) abs_summable_on_Sigma_iff) auto

(* lemma abs_summable_on_Sigma_project1':
  assumes "(\<lambda>(x,y). f x y) abs_summable_on Sigma A B"
  shows   "(\<lambda>x. infsum (\<lambda>y. f x y) (B x)) abs_summable_on A"
  apply (rule abs_summable_on_comparison_test)
   apply (rule abs_summable_on_Sigma_project1)
   apply (fact assms)
  by - *)

lemma expectation_exists'_bounded:
  fixes a b :: real
  assumes "\<And>x. x\<in>supp \<mu> \<Longrightarrow> f x \<ge> a"
  assumes "\<And>x. x\<in>supp \<mu> \<Longrightarrow> f x \<le> b"
  shows "expectation_exists' \<mu> f"
  apply (rule expectation_exists_bounded)
  using assms by auto

lemma prob_expectation_exists: "expectation_exists' \<mu> (\<lambda>x. prob (f x) a)"
  apply (rule expectation_exists_bounded[where a=0 and b=1])
  by auto

lemma prob_expectation: "prob (bind_distr \<mu> f) a = expectation' \<mu> (\<lambda>x. prob (f x) a)"
  apply (insert bind_distr_summable[of \<mu> f a])
  apply (transfer fixing: a)
proof -
  fix \<mu> :: "'b\<Rightarrow>real" and f :: "'b\<Rightarrow>'a\<Rightarrow>real"
  assume "is_distribution \<mu>"

  have y_preimage: "(\<lambda>x. f x a) -` {y} = {x. f x a = y}" for y
    by blast
  have Sigma: "(SIGMA y:UNIV. {x. f x a = y}) = (\<lambda>x. (f x a, x)) ` UNIV"
    unfolding image_def unfolding Sigma_def by auto

  (* We can make this assumption because of the "using bind_distr_summable[of \<mu> f a] apply -" step before the proof command *)
  assume "(\<lambda>x. \<mu> x * f x a) summable_on UNIV"
  then have \<open>(\<lambda>x. \<mu> x * f x a) abs_summable_on UNIV\<close>
    by (metis summable_on_iff_abs_summable_on_real)
  then have "(\<lambda>(x, y). \<mu> y * x) abs_summable_on (\<lambda>x. (f x a, x)) ` UNIV"
    apply (subst summable_on_reindex)
    by (auto simp: o_def intro!: injI)
  then have summ1: "(\<lambda>(x, y). \<mu> y * x) summable_on (SIGMA y:UNIV. {x. f x a = y})"
    using Sigma summable_on_iff_abs_summable_on_real by auto
  
  have "(\<Sum>\<^sub>\<infinity>x. \<mu> x * f x a) = (\<Sum>\<^sub>\<infinity>(x, y)\<in>(\<lambda>x. (f x a, x)) ` UNIV. \<mu> y * x)"
    apply (subst infsum_reindex)
     apply (rule injI, simp)
    by (simp add: o_def case_prod_beta)
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>(x, y)\<in>(SIGMA y:UNIV. {x. f x a = y}). \<mu> y * x)"
    unfolding Sigma by rule
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. \<Sum>\<^sub>\<infinity>x|f x a = y. \<mu> x * y)"
    apply (subst infsum_Sigma'_banach)
    using summ1
    by simp_all
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>y. infsum \<mu> ((\<lambda>x. f x a) -` {y}) *\<^sub>R y)"
    apply simp apply (subst infsum_cmult_left[symmetric])
    unfolding y_preimage
     apply (meson \<open>is_distribution \<mu>\<close> distr_summable_on is_distribution_def')
    by simp
  finally show "(\<Sum>\<^sub>\<infinity>y. \<mu> y * f y a) = (\<Sum>\<^sub>\<infinity>x. infsum \<mu> ((\<lambda>x. f x a) -` {x}) *\<^sub>R x)"
    by -
qed


lemma Prob_expectation: "Prob (bind_distr \<mu> f) S = expectation' \<mu> (\<lambda>x. Prob (f x) S)"
  unfolding Prob_map_distr bind_distr_map_distr[symmetric]
  by (rule prob_expectation)


lemma Prob_point_distr[simp]: "Prob (point_distr x) S = indicator S x"
  apply (subst Prob_map_distr)
  by simp

lemma map_distr_scaleR: \<open>map_distr f (r *\<^sub>R \<mu>) = (min 1 (max 0 r)) *\<^sub>R map_distr f \<mu>\<close>
  apply transfer
  using infsum_cmult_right' by auto



lemma expectation_scaleR: \<open>expectation (r *\<^sub>R \<mu>) = (min 1 (max 0 r)) *\<^sub>R expectation \<mu>\<close>
proof transfer
  fix r :: real and \<mu> :: \<open>'a \<Rightarrow> real\<close>
  assume \<open>is_distribution \<mu>\<close>
  define r' where \<open>r' = min 1 (max 0 r)\<close>
  have \<open>(\<Sum>\<^sub>\<infinity>x. (r' * \<mu> x) *\<^sub>R x) = (\<Sum>\<^sub>\<infinity>x. r' *\<^sub>R (\<mu> x *\<^sub>R x))\<close>
    by auto
  also have \<open>\<dots> = r' *\<^sub>R (\<Sum>\<^sub>\<infinity>x. \<mu> x *\<^sub>R x)\<close>
    by (rule infsum_scaleR_right)
  then show \<open>(\<Sum>\<^sub>\<infinity>x. (r' * \<mu> x) *\<^sub>R x) = r' *\<^sub>R (\<Sum>\<^sub>\<infinity>x. \<mu> x *\<^sub>R x)\<close>
    by simp
qed

lemma expectation'_product_distr1:
  assumes "expectation_exists' \<mu> f"
  shows "expectation' (product_distr \<mu> \<nu>) (\<lambda>(x,y). f x) = weight \<nu> * expectation' \<mu> f"
proof -
  have \<open>expectation' (product_distr \<mu> \<nu>) (\<lambda>(x,y). f x)
      = expectation (map_distr f (map_distr fst (product_distr \<mu> \<nu>)))\<close>
    by (smt (verit, ccfv_SIG) compose_map_distr cond_case_prod_eta fst_conv)
  also have \<open>\<dots> = expectation (weight \<nu> *\<^sub>R map_distr f \<mu>)\<close>
    apply (subst map_distr_fst_product_distr)
    by (auto simp: map_distr_scaleR)
  also have \<open>\<dots> = weight \<nu> * expectation' \<mu> f\<close>
    by (simp add: expectation_scaleR)
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

lemma infsum_prob_leq1[iff]: \<open>(\<Sum>\<^sub>\<infinity>x. prob \<mu> x) \<le> 1\<close>
  by (simp flip: Prob.rep_eq)

ML_file "discrete_distributions.ML"

end
