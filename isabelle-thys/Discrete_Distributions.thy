chapter \<open>Discrete (subprobability) distributions\<close>

theory Discrete_Distributions
  imports Complex_Main "HOL-Library.Rewrite" "HOL-Analysis.Infinite_Set_Sum" 
    Universe_Instances_Complex_Main Infinite_Set_Sum_Missing
begin

typedef 'a distr = "{f::'a\<Rightarrow>real. (\<forall>x. f x \<ge> 0) \<and> (\<forall> M. finite M \<longrightarrow> sum f M \<le> 1)}" 
  morphisms prob Abs_distr
  apply (rule exI[of _ "\<lambda>x. 0"]) by auto
setup_lifting type_definition_distr
derive universe distr

lemma distr_abs_summable_on:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<forall>x. f x \<ge> 0" and "\<forall> M. finite M \<longrightarrow> sum f M \<le> 1"
  shows "f abs_summable_on UNIV"
  apply (rule abs_summable_finiteI)
  using assms by auto

lemma distr_infsetsum:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<forall>x. f x \<ge> 0" and "\<forall> M. finite M \<longrightarrow> sum f M \<le> 1"
  shows "infsetsum f UNIV \<le> 1"
  apply (rule infsetsum_finite_sets)
  using assms by auto


instantiation distr :: (type)zero begin
lift_definition zero_distr :: "'a distr" is "(\<lambda>_. 0)" by simp
instance .. 
end


lift_definition supp :: "'a distr \<Rightarrow> 'a set" is "\<lambda>\<mu>. {x. \<mu> x > 0}" .

lemma "countable (supp \<mu>)"
proof (transfer, auto)
  fix \<mu> :: "'a => real"
  assume \<mu>pos: "\<forall>x. 0 \<le> \<mu> x" and "\<forall>M. finite M \<longrightarrow> sum \<mu> M \<le> 1"
  then have "\<mu> abs_summable_on UNIV"
    by (rule distr_abs_summable_on)
  then have "countable {x\<in>UNIV. 0 \<noteq> \<mu> x}" (is "countable ?X")
    by (rule abs_summable_countable)
  also have "?X = {x. 0 < \<mu> x}"
    using less_eq_real_def \<mu>pos by auto 
  finally show "countable {x. 0 < \<mu> x}" 
    by simp 
qed

lift_definition uniform :: "'a set \<Rightarrow> 'a distr" is "\<lambda>M. (\<lambda>m. if m\<in>M then 1/card M else 0)"
proof (rule conjI; rule allI; (rule impI)?)
  fix M and x :: 'a
  show "0 \<le> (if x \<in> M then 1 / real (card M) else 0)" by auto
  fix F
  show "(\<Sum>m\<in>F. if m \<in> M then 1 / real (card M) else 0) \<le> 1" if "finite F"
  proof (cases "finite M")
    case True
    show ?thesis
      apply (subst sum.inter_restrict[symmetric, OF that])
      apply simp
      by (metis Int_lower2 True card_mono divide_le_eq_1 neq0_conv of_nat_0_less_iff of_nat_eq_0_iff of_nat_le_iff)
  next
    case False
    show ?thesis
      apply (subst card_infinite[OF False])
      apply (rewrite asm_rl[of "1/real 0 = 0"]) apply auto[1]
      by auto
  qed
qed


lemma supp_uniform [simp]: "M \<noteq> {} \<Longrightarrow> finite M \<Longrightarrow> supp (uniform M) = M" for M :: "'a set"
  apply transfer apply auto
  using card_gt_0_iff by blast

lemma uniform_infinite: "infinite M \<Longrightarrow> uniform M = 0"
  apply transfer by auto

lemma uniform_empty: "uniform {} = 0"
  apply transfer by simp

lift_definition weight :: "'a distr \<Rightarrow> real" is "\<lambda>\<mu>. infsetsum \<mu> UNIV" .

lemma weight_pos[simp]: "weight \<mu> \<ge> 0"
  apply transfer
  by (rule infsetsum_nonneg) auto

lemma weight_leq1[simp]: "weight \<mu> \<le> 1"
  apply transfer apply (subst infsetsum_nonneg_is_SUPREMUM)
  using distr_abs_summable_on apply blast
   apply simp
  by (rule cSUP_least, auto)

lemma weight_uniform[simp]: "M \<noteq> {} \<Longrightarrow> finite M \<Longrightarrow> weight (uniform M) = 1"
proof transfer
  fix M :: "'a set"
  assume "M \<noteq> {}" and "finite M"
  then have "(\<Sum>\<^sub>ax\<in>M. 1 / real (card M)) = 1"
    by (subst infsetsum_finite, auto)
  then show "(\<Sum>\<^sub>am. if m \<in> M then 1 / real (card M) else 0) = 1"
    by (subst infsetsum_cong_neutral[where B=M], auto)
qed

lift_definition "map_distr" :: "('a\<Rightarrow>'b) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" 
  is "\<lambda>(f::'a\<Rightarrow>'b) \<mu> x. infsetsum \<mu> (f -` {x})"
proof auto
  fix f :: "'a \<Rightarrow> 'b" and \<mu> :: "'a \<Rightarrow> real" and x and M :: "'b set"
  assume "(\<forall>x. 0 \<le> \<mu> x)" and sumM: "(\<forall>M. finite M \<longrightarrow> sum \<mu> M \<le> 1)"
  then have summable: "\<mu> abs_summable_on UNIV"
    by (rule distr_abs_summable_on)
  from \<open>(\<forall>x. 0 \<le> \<mu> x)\<close> have \<mu>pos: "0 \<le> \<mu> x" for x by simp

  have reindex: "bij_betw snd (SIGMA x:M. f -` {x}) (f -` M)"
    by (rule bij_betwI, auto)

  have "0 = infsetsum (\<lambda>_. 0) (f -` {x})" by simp
  also have "\<dots> \<le> infsetsum \<mu> (f -` {x})"
    apply (rule infsetsum_mono_neutral_left)
    using abs_summable_on_subset[OF summable] \<mu>pos by auto
  finally show "0 \<le> infsetsum \<mu> (f -` {x})" .

  assume "finite M"
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
    by (simp add: \<mu>pos distr_infsetsum sumM)
  finally show "?lhs \<le> 1" .
qed

lemma map_distr_0[simp]: "map_distr f 0 = 0"
  by (transfer, simp)

lemma weight_map_distr[simp]: "weight (map_distr f \<mu>) = weight \<mu>"
proof (transfer, auto)
  fix f :: "'b \<Rightarrow> 'a" and \<mu> :: "'b => real"
  assume "\<forall>x. 0 \<le> \<mu> x" and "\<forall>M. finite M \<longrightarrow> sum \<mu> M \<le> 1"
  then have summable: "\<mu> abs_summable_on UNIV"
    by (rule distr_abs_summable_on)
  have reindex: "bij_betw snd (SIGMA x:UNIV. f -` {x}) UNIV"
    by (rule bij_betwI, auto)
  show "(\<Sum>\<^sub>ax. infsetsum \<mu> (f -` {x})) = infsetsum \<mu> UNIV"
    apply (subst infsetsum_Sigma')
    unfolding case_prod_beta
    using reindex summable apply (rule abs_summable_on_reindex_bij_betw[THEN iffD2])
    using reindex by (subst infsetsum_reindex_bij_betw, auto)
qed

lemma supp_map_distr[simp]: "supp (map_distr f \<mu>) = f ` (supp \<mu>)"
proof (transfer, auto)
  fix f :: "'b \<Rightarrow> 'a" and \<mu> :: "'b \<Rightarrow> real" and x :: 'a and y :: 'b
  assume \<mu>pos: "\<forall>x. 0 \<le> \<mu> x" and "\<forall>M. finite M \<longrightarrow> sum \<mu> M \<le> 1"
  then have summable: "\<mu> abs_summable_on UNIV"
    by (rule distr_abs_summable_on)
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
proof (transfer fixing: f g, rule ext)
  fix \<mu> :: "'a => real" and x
  assume "(\<forall>x. 0 \<le> \<mu> x) \<and> (\<forall>M. finite M \<longrightarrow> sum \<mu> M \<le> 1)"
  then have summable: "\<mu> abs_summable_on UNIV"
    using distr_abs_summable_on by auto
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

end
