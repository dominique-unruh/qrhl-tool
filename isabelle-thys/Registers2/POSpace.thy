theory POSpace
  imports Hilbert_Space_Tensor_Product.Misc_Tensor_Product
    \<comment> \<open>These dependencies are of course not suitable for inclusion in HOL-Main.
        But they affect only a few proofs and whichever proofs are would be included in Main, I happily rewrite them.\<close>
begin

class pospace = order + topological_space +
  assumes closed_superdiagonal_raw: \<open>(\<forall>x\<in>-{(x,y). x \<ge> y}. \<exists>A B. open A \<and> open B \<and> x \<in> A \<times> B \<and> A \<times> B \<subseteq> - {(x,y). x \<ge> y})\<close>
  \<comment> \<open>Can't write \<open>closed {(x,y) | x y. x \<ge> y}\<close> due to locale-restrictions.
      Instead, we unfold the definition of \<^const>\<open>closed\<close> on the product topology.\<close>

lemma pospaceI:
  \<comment> \<open>\<open>apply intro_classes\<close> gives an ugly subgoal when proving an instantiation for \<^class>\<open>pospace\<close>.
      \<open>apply (rule pospaceI)\<close> gives an equivalent but more readable one.\<close>
  assumes \<open>closed {(x::'a::{order,topological_space},y). x \<ge> y}\<close>
  shows \<open>OFCLASS('a, pospace_class)\<close>
  apply intro_classes
  using assms
  by (simp add: closed_def open_prod_def)

instance linorder_topology \<subseteq> pospace
  apply (rule pospaceI)
  using Topological_Spaces.closed_superdiagonal by auto

lemma closed_superdiagonal: \<open>closed {(x::_::pospace,y). x \<ge> y}\<close>
  using closed_superdiagonal_raw 
  by (auto simp: closed_def open_prod_def)

instance pospace \<subseteq> t2_space
proof -
  have rewrite: \<open>range (\<lambda>x::'a. (x, x)) = {(x,y). x \<ge> y} \<inter> prod.swap -` {(x,y). x \<ge> y}\<close>
    by (auto intro!: simp: )
  have \<open>closed (range (\<lambda>x::'a. (x, x)))\<close>
    apply (subst rewrite)
    by (intro closed_Int closed_superdiagonal closed_vimage continuous_on_swap)
  then have \<open>Hausdorff_space (euclidean :: 'a topology)\<close>
    by (simp add: Hausdorff_space_closedin_diagonal)
  then show \<open>OFCLASS('a, t2_space_class)\<close>
    by (rule hausdorff_OFCLASS_t2_space)
qed

thm tendsto_le
lemma tendsto_le:
  fixes x y :: \<open>'a :: pospace\<close>
  assumes F: "\<not> trivial_limit F"
    and x: "(f \<longlongrightarrow> x) F"
    and y: "(g \<longlongrightarrow> y) F"
    and ev: "eventually (\<lambda>x. g x \<le> f x) F"
  shows "y \<le> x"
proof -
  define upper where \<open>upper = {(x::'a,y). x \<ge> y}\<close>
  from x y have \<open>((\<lambda>x. (f x, g x)) \<longlongrightarrow> (x,y)) F\<close>
    by (rule tendsto_Pair)
  moreover from ev have \<open>\<forall>\<^sub>F x in F. (f x, g x) \<in> upper\<close>
    by (simp add: upper_def)
  moreover have \<open>closed upper\<close>
    using closed_superdiagonal upper_def by blast
  ultimately have \<open>(x,y) \<in> upper\<close>
    apply (rule_tac Lim_in_closed_set)
    using F by auto
  then show \<open>y \<le> x\<close>
    using upper_def by blast
qed

thm has_sum_mono_neutral
lemma has_sum_mono_neutral:
  fixes f :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,pospace}"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  define f' g' where \<open>f' x = (if x \<in> A then f x else 0)\<close> and \<open>g' x = (if x \<in> B then g x else 0)\<close> for x
  have [simp]: \<open>f summable_on A\<close> \<open>g summable_on B\<close>
    using assms(1,2) summable_on_def by auto
  have \<open>(f' has_sum a) (A\<union>B)\<close>
    by (smt (verit, best) DiffE IntE Un_iff f'_def assms(1) has_sum_cong_neutral)
  then have f'_lim: \<open>(sum f' \<longlongrightarrow> a) (finite_subsets_at_top (A\<union>B))\<close>
    by (meson has_sum_def)
  have \<open>(g' has_sum b) (A\<union>B)\<close>
  by (smt (verit, best) DiffD1 DiffD2 IntE UnCI g'_def assms(2) has_sum_cong_neutral)
  then have g'_lim: \<open>(sum g' \<longlongrightarrow> b) (finite_subsets_at_top (A\<union>B))\<close>
    using has_sum_def by blast

  have "\<And>X i. \<lbrakk>X \<subseteq> A \<union> B; i \<in> X\<rbrakk> \<Longrightarrow> f' i \<le> g' i"
    using assms by (auto simp: f'_def g'_def)
  then have \<open>\<forall>\<^sub>F x in finite_subsets_at_top (A \<union> B). sum f' x \<le> sum g' x\<close>
    by (intro eventually_finite_subsets_at_top_weakI sum_mono)
  then show ?thesis
    using f'_lim finite_subsets_at_top_neq_bot g'_lim tendsto_le
    by fast
qed

instance complex :: pospace
proof (rule pospaceI)
  have \<open>closed ({xy. Re (fst xy) \<ge> Re (snd xy)} \<inter> {xy. Im (fst xy) = Im (snd xy)})\<close>
    by (intro closed_Int closed_Collect_le closed_Collect_eq continuous_intros)
  moreover have \<open>\<dots> = {(x, y). x \<ge> y}\<close>
    by (auto intro!: simp: less_eq_complex_def)
  ultimately show \<open>closed {(x::complex, y). x \<ge> y}\<close>
    by simp
qed

thm closed_Collect_le
lemma closed_Collect_le:
  fixes f g :: "'a :: topological_space \<Rightarrow> 'b::pospace"
  assumes f: "continuous_on UNIV f"
    and g: "continuous_on UNIV g"
  shows "closed {x. f x \<le> g x}"
proof -
  have \<open>closed {(x::'b,y). x \<ge> y}\<close>
    using closed_superdiagonal by blast
  then have \<open>closed ((\<lambda>x. (g x, f x)) -` \<dots>)\<close>
    by (intro closed_vimage continuous_on_Pair assms)
  also have \<open>\<dots> = {x . f x \<le> g x}\<close>
    by auto
  finally show ?thesis
    by -
qed


lemma pospace_fun:
  \<open>OFCLASS('a \<Rightarrow> 'b::pospace, pospace_class)\<close>
    \<comment> \<open>Ideally, we would just instantiate \<open>instance fun :: (type, pospace) pospace\<close> but that is rejected by Isabelle.
        Hopefully when adding this earlier on in Isabelle, the conflict can be resolved.\<close>
proof (rule pospaceI)
  have \<open>closed {(x :: 'a \<Rightarrow> 'b,y). y a \<le> x a}\<close> for a
    apply (simp add: case_prod_unfold)
    apply (intro closed_Collect_le[internalize_sort' 'a] topological_space_axioms)
     apply (rule continuous_on_product_then_coordinatewise)
     apply (intro continuous_intros)
    apply (rule continuous_on_product_then_coordinatewise)
    by (intro continuous_intros)
  then have \<open>closed (\<Inter>a. {(x :: 'a \<Rightarrow> 'b, y). x a \<ge> y a})\<close>
    by blast
  also have \<open>\<dots> = {(x, y). x \<ge> y}\<close>
    by (auto simp: le_fun_def)
  finally show \<open>closed \<dots>\<close>
    by -
qed

thm tendsto_upperbound
lemma tendsto_upperbound:
  fixes x :: \<open>'a :: pospace\<close>
  assumes x: "(f \<longlongrightarrow> x) F"
      and ev: "eventually (\<lambda>i. a \<ge> f i) F"
      and F: "\<not> trivial_limit F"
  shows "a \<ge> x"
  by (rule tendsto_le [OF F tendsto_const x ev])

thm has_sum_le_finite_sums
lemma has_sum_le_finite_sums:
  fixes a :: \<open>'a::{comm_monoid_add,topological_space,pospace}\<close>
  assumes \<open>(f has_sum a) A\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> sum f F \<le> b\<close>
  shows \<open>a \<le> b\<close>
  by (metis assms eventually_finite_subsets_at_top_weakI finite_subsets_at_top_neq_bot has_sum_def tendsto_upperbound)

thm infsum_le_finite_sums
lemma infsum_le_finite_sums:
  fixes b :: \<open>'a::{comm_monoid_add,topological_space,pospace}\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> sum f F \<le> b\<close>
  shows \<open>infsum f A \<le> b\<close>
  by (metis has_sum_le_finite_sums assms bot_least finite.intros(1) has_sum_infsum infsum_not_exists
      sum.empty)

end
