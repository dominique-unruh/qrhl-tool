chapter \<open>Discrete (subprobability) distributions\<close>

theory Discrete_Distributions
  imports Complex_Main "HOL-Library.Rewrite" "HOL-Analysis.Infinite_Set_Sum" 
    Universe_Instances_Complex_Main Bounded_Operators.Infinite_Set_Sum_Missing
    Bounded_Operators.Extended_Sorry
begin



setup_lifting type_definition_distr



instantiation distr :: (type)zero begin

instance .. 
end


lift_definition supp :: "'a distr \<Rightarrow> 'a set" is "\<lambda>\<mu>. {x. \<mu> x > 0}" .

lemma "countable (supp \<mu>)"
  sorry

lift_definition uniform :: "'a set \<Rightarrow> 'a distr" is "\<lambda>M. (\<lambda>m. if m\<in>M then 1/card M else 0)"
  sorry

lemma supp_uniform [simp]: "M \<noteq> {} \<Longrightarrow> finite M \<Longrightarrow> supp (uniform M) = M" for M :: "'a set"
  apply transfer apply auto
  using card_gt_0_iff by blast

lemma uniform_infinite: "infinite M \<Longrightarrow> uniform M = 0"
  sorry

lemma uniform_empty: "uniform {} = 0"
  sorry

lift_definition Prob :: "'a distr \<Rightarrow> 'a set \<Rightarrow> real" is infsetsum .

abbreviation "weight \<mu> == Prob \<mu> UNIV"

lemma Prob_is_0:
  "Prob \<mu> E = 0 \<longleftrightarrow> disjnt (supp \<mu>) E"
  sorry

lemma Prob_pos[simp]: "Prob \<mu> E \<ge> 0"
  apply transfer
  by (rule infsetsum_nonneg) (auto simp: is_distribution_def)

lemma Prob_mono:
  assumes "E \<subseteq> F"
  shows "Prob \<mu> E \<le> Prob \<mu> F"
  sorry

lemma Prob_leq1[simp]: "Prob \<mu> E \<le> 1"
  sorry

lemma weight_uniform[simp]: "M \<noteq> {} \<Longrightarrow> finite M \<Longrightarrow> weight (uniform M) = 1"
  sorry

lift_definition "map_distr" :: "('a\<Rightarrow>'b) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" 
  is "\<lambda>(f::'a\<Rightarrow>'b) \<mu> x. infsetsum \<mu> (f -` {x})"
  sorry

lemma map_distr_0[simp]: "map_distr f 0 = 0"
  sorry

lemma weight_map_distr[simp]: "weight (map_distr f \<mu>) = weight \<mu>"
  sorry



ML_file "discrete_distributions.ML"

end
