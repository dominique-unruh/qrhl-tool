chapter \<open>Discrete (subprobability) distributions\<close>

theory Discrete_Distributions
  imports Complex_Main "HOL-Library.Rewrite" "HOL-Analysis.Infinite_Set_Sum" 
    Universe_Instances_Complex_Main Bounded_Operators.Infinite_Set_Sum_Missing
    Bounded_Operators.Extended_Sorry
begin

typedef 'a distr = "{f::'a\<Rightarrow>real. (\<forall>x. f x \<ge> 0) \<and> (\<forall> M. finite M \<longrightarrow> sum f M \<le> 1)}" 
  morphisms prob Abs_distr
  apply (rule exI[of _ "\<lambda>x. 0"]) by auto
setup_lifting type_definition_distr
derive universe distr

lemma distr_abs_summable_on:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<forall>x. f x \<ge> 0" and "\<forall> M. finite M \<longrightarrow> sum f M \<le> 1"
  shows "f abs_summable_on E"
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

lift_definition Prob :: "'a distr \<Rightarrow> 'a set \<Rightarrow> real" is infsetsum .

abbreviation "weight \<mu> == Prob \<mu> UNIV"

lemma Prob_is_0:
  "Prob \<mu> E = 0 \<longleftrightarrow> disjnt (supp \<mu>) E"
proof (transfer fixing: E, rule)
  fix \<mu> :: "'a\<Rightarrow>real"
  assume distr: "(\<forall>x. 0 \<le> \<mu> x) \<and> (\<forall>M. finite M \<longrightarrow> sum \<mu> M \<le> 1)"
  then have "0 \<le> \<mu> x" for x
      using distr by simp
  from distr have "\<mu> abs_summable_on E"
    by (simp add: distr_abs_summable_on)
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
  assume distr: "(\<forall>x. 0 \<le> \<mu> x) \<and> (\<forall>M. finite M \<longrightarrow> sum \<mu> M \<le> 1)"
  assume "disjnt {x. 0 < \<mu> x} E"
  then have "\<mu> x = 0" if "x:E" for x
    unfolding disjnt_def distr
    using distr less_eq_real_def that by auto 
  then show "infsetsum \<mu> E = 0"
    by (rule infsetsum_all_0)
qed

lemma Prob_pos: "Prob \<mu> E \<ge> 0"
  apply transfer
  by (rule infsetsum_nonneg) auto

lemma Prob_mono:
  assumes "E \<subseteq> F"
  shows "Prob \<mu> E \<le> Prob \<mu> F"
proof (transfer fixing: E F)
  fix \<mu> :: "'a \<Rightarrow> real"
  assume distr: "(\<forall>x. 0 \<le> \<mu> x) \<and> (\<forall>M. finite M \<longrightarrow> sum \<mu> M \<le> 1)"
  then have "\<mu> abs_summable_on E" and "\<mu> abs_summable_on F"
    by (simp_all add: distr_abs_summable_on)
  then show "infsetsum \<mu> E \<le> infsetsum \<mu> F"
    apply (rule infsetsum_mono_neutral_left)
    using assms distr by auto
qed

lemma Prob_leq1: "Prob \<mu> E \<le> 1"
proof -
  have "Prob \<mu> UNIV \<le> 1"
    apply transfer apply (subst infsetsum_nonneg_is_SUPREMUM)
    using distr_abs_summable_on apply blast
     apply simp
    by (rule cSUP_least, auto)
  then show ?thesis
    using Prob_mono[of E UNIV \<mu>] by auto
qed

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


lift_definition expectation :: "'a distr \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> 'b::{banach, second_countable_topology}" is
  "\<lambda>\<mu> f. infsetsum (\<lambda>x. \<mu> x *\<^sub>R f x) UNIV" .

lift_definition expectation_exists :: "'a distr \<Rightarrow> ('a\<Rightarrow>'b::{banach, second_countable_topology}) \<Rightarrow> bool" is
  "\<lambda>\<mu> f. (\<lambda>x. \<mu> x *\<^sub>R f x) abs_summable_on UNIV" .

lemma expectation_exists_bounded:
  fixes a b :: real
  assumes "\<And>x. x\<in>supp \<mu> \<Longrightarrow> f x \<ge> a"
  assumes "\<And>x. x\<in>supp \<mu> \<Longrightarrow> f x \<le> b"
  shows "expectation_exists \<mu> f"
proof (insert assms, transfer fixing: a b f)
  fix \<mu> :: "'a \<Rightarrow> real"
  define \<mu>f where "\<mu>f x = \<mu> x *\<^sub>R f x" for x
  obtain B where "B \<ge> -a" and "B \<ge> b" and "B \<ge> 0"
    by (meson linear order_trans)
  assume distr: "(\<forall>x. 0 \<le> \<mu> x) \<and> (\<forall>M. finite M \<longrightarrow> sum \<mu> M \<le> 1)"
  then have \<mu>pos: "\<mu> x \<ge> 0" for x by auto
  from distr have sum: "sum \<mu> F \<le> 1" if "finite F" for F
    using that by auto
  assume "(\<And>x. x \<in> {x. 0 < \<mu> x} \<Longrightarrow> a \<le> f x)"
  then have fx1: "f x \<ge> -B" if "0 < \<mu> x" for x
    using that \<open>- a \<le> B\<close> by force
  assume "(\<And>x. x \<in> {x. 0 < \<mu> x} \<Longrightarrow> f x \<le> b)"
  then have fx2: "f x \<le> B" if "0 < \<mu> x" for x
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
    by (rule abs_summable_finiteI)
qed

lemma expectation_mono:
  fixes f :: "'a\<Rightarrow>real"
  assumes "expectation_exists \<mu> f"
  assumes "expectation_exists \<mu> g"
  assumes leq: "\<And>x. x\<in>supp \<mu> \<Longrightarrow> f x \<le> g x"
  shows "expectation \<mu> f \<le> expectation \<mu> g"
proof (insert assms, transfer)
  fix \<mu> :: "'a\<Rightarrow>real" and f g :: "'a\<Rightarrow>real"
  assume "(\<forall>x. 0 \<le> \<mu> x) \<and> (\<forall>M. finite M \<longrightarrow> sum \<mu> M \<le> 1)"
  then have pos: "\<mu> x \<ge> 0" for x by simp
  assume leq: "(\<And>x. x \<in> {x. 0 < \<mu> x} \<Longrightarrow> f x \<le> g x)"
  have leq': "\<mu> x *\<^sub>R f x \<le> \<mu> x *\<^sub>R g x" for x
    apply (cases "\<mu> x = 0") using pos[of x] leq[of x] by auto
  assume sumf: "(\<lambda>x. \<mu> x *\<^sub>R f x) abs_summable_on UNIV"
    and sumg: "(\<lambda>x. \<mu> x *\<^sub>R g x) abs_summable_on UNIV"
  from sumf sumg leq' show "infsetsum (\<lambda>x. \<mu> x *\<^sub>R f x) UNIV \<le> infsetsum (\<lambda>x. \<mu> x *\<^sub>R g x) UNIV"
    by (rule infsetsum_mono)
qed


lemma prob_uniform[simp]: "prob (uniform M) m = (if m\<in>M then 1/card M else 0)"
  apply transfer by simp

abbreviation "point_distr x \<equiv> uniform {x}"
lemma expectation_point_distr[simp]: "expectation (point_distr x) f = f x"
  apply (transfer fixing: x f)
  apply (subst infsetsum_cong_neutral[where B="{x}"])
  by auto

(* TODO move *)
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

lemma expectation_uminus: "expectation \<mu> (\<lambda>x. -f x) = - expectation \<mu> f"
  apply (transfer fixing: f)
  apply auto
  by (simp add: infsetsum_uminus)

lemma expectation_upper_bound:
  fixes f :: "'a \<Rightarrow> real"
  assumes "weight \<mu> = 1 \<or> B \<ge> 0"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> f x \<ge> C"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> f x \<le> B"
  shows "expectation \<mu> f \<le> B"
  using assms 
proof (transfer fixing: B C f)
  fix \<mu> :: "'a\<Rightarrow>real"
  assume \<mu>1_or_Bpos: "infsetsum \<mu> UNIV = 1 \<or> 0 \<le> B"
  assume \<mu>: "(\<forall>x. 0 \<le> \<mu> x) \<and> (\<forall>M. finite M \<longrightarrow> sum \<mu> M \<le> 1)"
  then have \<mu>sum: "\<mu> abs_summable_on UNIV"
    by (simp add: distr_abs_summable_on)
  from \<mu> have \<mu>sum1: "infsetsum \<mu> UNIV \<le> 1"
    by (simp add: distr_infsetsum)
  have \<mu>pos: "\<mu> x \<ge> 0" for x
    using \<mu> by simp
  obtain BC where "BC\<ge>B" and "BC\<ge>-C" and "BC\<ge>0" 
    apply atomize_elim
    by (meson linorder_linear order_trans_rules(23))
  assume "(\<And>x. x \<in> {x. 0 < \<mu> x} \<Longrightarrow> C \<le> f x)" and B0: "(\<And>x. x \<in> {x. 0 < \<mu> x} \<Longrightarrow> f x \<le> B)"
  then have abs_fx: "abs (f x) \<le> BC" if "\<mu> x \<noteq> 0" for x
    by (smt \<mu>pos \<open>- C \<le> BC\<close> \<open>B \<le> BC\<close> mem_Collect_eq that)
  then have abs_f\<mu>x: "abs (\<mu> x * f x) \<le> \<mu> x * BC" for x
    by (metis \<mu>pos abs_mult abs_pos mult.commute mult_eq_0_iff mult_left_mono)
  from B0 have fxB: "f x \<le> B" if "\<mu> x \<noteq> 0" for x
    using \<mu>pos less_eq_real_def that by auto
  with \<mu>pos have \<mu>FB: "\<mu> x * f x \<le> \<mu> x * B" for x
    by (metis ordered_comm_semiring_class.comm_mult_left_mono vector_space_over_itself.scale_cancel_left)
  have "(\<lambda>x. \<mu> x * BC) abs_summable_on UNIV"
    using \<mu>sum by (rule abs_summable_on_cmult_left)
  then have sum\<mu>f: "(\<lambda>x. \<mu> x * f x) abs_summable_on UNIV"
    apply (rule abs_summable_on_comparison_test')
    using abs_f\<mu>x by simp
  have sum\<mu>B: "(\<lambda>x. \<mu> x * B) abs_summable_on UNIV"
    using \<mu>sum by (rule abs_summable_on_cmult_left)

  have "(\<Sum>\<^sub>ax. \<mu> x *\<^sub>R f x) = (\<Sum>\<^sub>ax. \<mu> x * f x)" 
    by simp
  also have "\<dots> \<le> (\<Sum>\<^sub>ax. \<mu> x * B)"
    using sum\<mu>f sum\<mu>B \<mu>FB by (rule infsetsum_mono)
  also have "\<dots> = (\<Sum>\<^sub>ax. \<mu> x) * B"
    using \<mu>sum infsetsum_cmult_left by blast
  also from \<mu>sum1 \<mu>1_or_Bpos have "\<dots> \<le> B"
    by (auto simp: mult_left_le ordered_field_class.sign_simps(5))
  finally show "(\<Sum>\<^sub>ax. \<mu> x *\<^sub>R f x) \<le> B" by simp
qed

lemma expectation_lower_bound:
  fixes f :: "'a \<Rightarrow> real"
  assumes "weight \<mu> = 1 \<or> B \<le> 0"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> f x \<le> C"
  assumes "\<And>x. x \<in> supp \<mu> \<Longrightarrow> f x \<ge> B"
  shows "expectation \<mu> f \<ge> B"
proof -
  have "expectation \<mu> (\<lambda>x. -f x) \<le> -B"
    apply (rule expectation_upper_bound[where C="-C"])
    using assms by auto
  then show ?thesis
    unfolding expectation_uminus by simp
qed


ML_file "discrete_distributions.ML"

end
