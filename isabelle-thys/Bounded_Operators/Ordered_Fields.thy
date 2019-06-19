theory Ordered_Fields
  imports Main
begin

subsection \<open>Missing from Orderings.thy\<close>

class unbounded_dense_order = dense_order + no_top + no_bot

subsection \<open>Missing from Rings.thy\<close>

class incomplete_abs_if = minus + uminus + ord + zero + abs +
  assumes abs_neg: "a \<le> 0 \<Longrightarrow> abs a = -a"
  assumes abs_pos: "a \<ge> 0 \<Longrightarrow> abs a = a"

class ordered_semiring_1 = ordered_semiring + semiring_1
begin

lemma convex_bound_le:
  assumes "x \<le> a" "y \<le> a" "0 \<le> u" "0 \<le> v" "u + v = 1"
  shows "u * x + v * y \<le> a"
  sorry

end

subclass (in linordered_semiring_1) ordered_semiring_1 ..

class ordered_semiring_strict = semiring + comm_monoid_add + ordered_cancel_ab_semigroup_add +
  assumes mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
  assumes mult_strict_right_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a * c < b * c"
begin

subclass semiring_0_cancel ..

subclass ordered_semiring
  sorry

lemma mult_pos_pos[simp]: "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a * b"
  using mult_strict_left_mono [of 0 b a] by simp

lemma mult_pos_neg: "0 < a \<Longrightarrow> b < 0 \<Longrightarrow> a * b < 0"
  using mult_strict_left_mono [of b 0 a] by simp

lemma mult_neg_pos: "a < 0 \<Longrightarrow> 0 < b \<Longrightarrow> a * b < 0"
  using mult_strict_right_mono [of a 0 b] by simp

text \<open>Legacy -- use @{thm [source] mult_neg_pos}.\<close>
lemma mult_pos_neg2: "0 < a \<Longrightarrow> b < 0 \<Longrightarrow> b * a < 0"
  by (drule mult_strict_right_mono [of b 0]) auto

text \<open>Strict monotonicity in both arguments\<close>

lemma mult_strict_mono':
  assumes "a < b" and "c < d" and "0 \<le> a" and "0 \<le> c"
  shows "a * c < b * d"
  sorry

lemma mult_less_le_imp_less:
  assumes "a < b" and "c \<le> d" and "0 \<le> a" and "0 < c"
  shows "a * c < b * d"
  using assms
  apply (subgoal_tac "a * c < b * c")
   apply (erule less_le_trans)
   apply (erule mult_left_mono)
   apply simp
  apply (erule (1) mult_strict_right_mono)
  done

lemma mult_le_less_imp_less:
  assumes "a \<le> b" and "c < d" and "0 < a" and "0 \<le> c"
  shows "a * c < b * d"
  using assms
  apply (subgoal_tac "a * c \<le> b * c")
   apply (erule le_less_trans)
   apply (erule mult_strict_left_mono)
   apply simp
  apply (erule (1) mult_right_mono)
  done

end




subclass (in linordered_semiring_strict) ordered_semiring_strict 
  apply standard
  apply (simp add: local.mult_strict_left_mono)
  by (simp add: local.mult_strict_right_mono)


class ordered_semiring_1_strict = ordered_semiring_strict + semiring_1
begin

subclass ordered_semiring_1 ..

lemma convex_bound_lt:
  assumes "x < a" "y < a" "0 \<le> u" "0 \<le> v" "u + v = 1"
  shows "u * x + v * y < a"
proof -
  from assms have "u * x + v * y < u * a + v * a"
    by (cases "u = 0") (auto intro!: add_less_le_mono mult_strict_left_mono mult_left_mono)
  with assms show ?thesis
    unfolding distrib_right[symmetric] by simp
qed

end

subclass (in linordered_semiring_1_strict) ordered_semiring_1_strict .. 

class ordered_comm_semiring_strict = comm_semiring_0 + ordered_cancel_ab_semigroup_add +
  assumes comm_mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
begin

subclass ordered_semiring_strict
proof
  fix a b c :: 'a
  assume "a < b" "0 < c"
  then show "c * a < c * b"
    by (rule comm_mult_strict_left_mono)
  then show "a * c < b * c"
    by (simp only: mult.commute)
qed

subclass ordered_cancel_comm_semiring
  sorry

end

subclass (in linordered_comm_semiring_strict) ordered_comm_semiring_strict 
  apply standard
  by (simp add: local.mult_strict_left_mono)


class ordered_ring_strict = ring + ordered_semiring_strict
  + ordered_ab_group_add + incomplete_abs_if
begin

subclass ordered_ring ..

lemma mult_strict_left_mono_neg: "b < a \<Longrightarrow> c < 0 \<Longrightarrow> c * a < c * b"
  using mult_strict_left_mono [of b a "- c"] by simp

lemma mult_strict_right_mono_neg: "b < a \<Longrightarrow> c < 0 \<Longrightarrow> a * c < b * c"
  using mult_strict_right_mono [of b a "- c"] by simp

lemma mult_neg_neg: "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> 0 < a * b"
  using mult_strict_right_mono_neg [of a 0 b] by simp

end

lemmas mult_sign_intros =
  mult_nonneg_nonneg mult_nonneg_nonpos
  mult_nonpos_nonneg mult_nonpos_nonpos
  mult_pos_pos mult_pos_neg
  mult_neg_pos mult_neg_neg


subsection \<open>Ordered fields\<close>

class ordered_field = field + order + ordered_comm_semiring_strict + ordered_ab_group_add + incomplete_abs_if 
begin


lemmas sign_simps = algebra_simps zero_less_mult_iff mult_less_0_iff

lemmas (in -) sign_simps = algebra_simps zero_less_mult_iff mult_less_0_iff


text \<open>Division and the Number One\<close>

text\<open>Simplify expressions equated with 1\<close>

lemma zero_eq_1_divide_iff [simp]: "0 = 1 / a \<longleftrightarrow> a = 0"
  by (cases "a = 0") (auto simp: field_simps)

lemma one_divide_eq_0_iff [simp]: "1 / a = 0 \<longleftrightarrow> a = 0"
  using zero_eq_1_divide_iff[of a] by simp

text\<open>Simplify expressions such as \<open>0 < 1/x\<close> to \<open>0 < x\<close>\<close>

text\<open>Simplify quotients that are compared with the value 1.\<close>

text \<open>Conditional Simplification Rules: No Case Splits\<close>

lemma eq_divide_eq_1 [simp]:
  "(1 = b/a) = ((a \<noteq> 0 & a = b))"
by (auto simp add: eq_divide_eq)

lemma divide_eq_eq_1 [simp]:
  "(b/a = 1) = ((a \<noteq> 0 & a = b))"
by (auto simp add: divide_eq_eq)

end

class nice_ordered_field = ordered_field + zero_less_one + idom_abs_sgn +
  assumes positive_imp_inverse_positive: "0 < a \<Longrightarrow> 0 < inverse a"
  and inverse_le_imp_le: "inverse a \<le> inverse b \<Longrightarrow> 0 < a \<Longrightarrow> b \<le> a"
  and dense_le: "(\<And>x. x < y \<Longrightarrow> x \<le> z) \<Longrightarrow> y \<le> z"
  and nn_comparable: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a \<le> b \<or> b \<le> a"
  and abs_nn: "abs x \<ge> 0"
begin

subclass (in linordered_field) nice_ordered_field
  apply standard
       apply auto
  using local.inverse_le_imp_le apply blast
  using local.dense_le by blast


lemma inverse_positive_imp_positive:
  assumes inv_gt_0: "0 < inverse a" and nz: "a \<noteq> 0"
  shows "0 < a"
  sorry

lemma inverse_negative_imp_negative:
  assumes inv_less_0: "inverse a < 0" and nz: "a \<noteq> 0"
  shows "a < 0"
  sorry

lemma linordered_field_no_lb:
  "\<forall>x. \<exists>y. y < x"
proof
  fix x::'a
  have m1: "- (1::'a) < 0" by simp
  from add_strict_right_mono[OF m1, where c=x]
  have "(- 1) + x < x" by simp
  thus "\<exists>y. y < x" by blast
qed


text\<open>Both premises are essential. Consider -1 and 1.\<close>

text\<open>These results refer to both operands being negative.  The opposite-sign
case is trivial, since inverse preserves signs.\<close>
lemma inverse_le_imp_le_neg:
  "inverse a \<le> inverse b \<Longrightarrow> b < 0 \<Longrightarrow> b \<le> a"
  by (metis local.inverse_le_imp_le local.inverse_minus_eq local.neg_0_less_iff_less local.neg_le_iff_le)

lemma inverse_less_imp_less_neg:
   "inverse a < inverse b \<Longrightarrow> b < 0 \<Longrightarrow> b < a"
  using local.dual_order.strict_iff_order local.inverse_le_imp_le_neg by blast

lemma inverse_less_iff_less_neg [simp]:
  "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> inverse a < inverse b \<longleftrightarrow> b < a"
  sorry

lemma le_imp_inverse_le_neg:
  "a \<le> b \<Longrightarrow> b < 0 ==> inverse b \<le> inverse a"
  by (force simp add: le_less less_imp_inverse_less_neg)

lemma inverse_le_iff_le_neg [simp]:
  "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> inverse a \<le> inverse b \<longleftrightarrow> b \<le> a"
  by (blast intro: le_imp_inverse_le_neg dest: inverse_le_imp_le_neg)

lemma one_less_inverse:
  "0 < a \<Longrightarrow> a < 1 \<Longrightarrow> 1 < inverse a"
  sorry

lemma one_le_inverse:
  "0 < a \<Longrightarrow> a \<le> 1 \<Longrightarrow> 1 \<le> inverse a"
  sorry

lemma pos_le_divide_eq [field_simps]:
  assumes "0 < c"
  shows "a \<le> b / c \<longleftrightarrow> a * c \<le> b"
  using assms by (metis local.divide_eq_imp local.divide_inverse_commute local.dual_order.order_iff_strict local.dual_order.strict_iff_order local.mult_right_mono local.mult_strict_left_mono local.nonzero_divide_eq_eq local.order.strict_implies_order local.positive_imp_inverse_positive)

lemma pos_less_divide_eq [field_simps]:
  assumes "0 < c"
  shows "a < b / c \<longleftrightarrow> a * c < b"
  using assms local.dual_order.strict_iff_order local.nonzero_divide_eq_eq local.pos_le_divide_eq by auto

lemma neg_less_divide_eq [field_simps]:
  assumes "c < 0"
  shows "a < b / c \<longleftrightarrow> b < a * c"
  by (metis assms local.minus_divide_divide local.mult_minus_right local.neg_0_less_iff_less local.neg_less_iff_less local.pos_less_divide_eq)

lemma neg_le_divide_eq [field_simps]:
  assumes "c < 0"
  shows "a \<le> b / c \<longleftrightarrow> b \<le> a * c"
  by (metis assms local.dual_order.order_iff_strict local.dual_order.strict_iff_order local.neg_less_divide_eq local.nonzero_divide_eq_eq)

lemma pos_divide_le_eq [field_simps]:
  assumes "0 < c"
  shows "b / c \<le> a \<longleftrightarrow> b \<le> a * c"
  by (metis assms local.dual_order.strict_iff_order local.nonzero_eq_divide_eq local.pos_le_divide_eq)

lemma pos_divide_less_eq [field_simps]:
  assumes "0 < c"
  shows "b / c < a \<longleftrightarrow> b < a * c"
  by (metis assms local.minus_divide_left local.mult_minus_left local.neg_less_iff_less local.pos_less_divide_eq)

lemma neg_divide_le_eq [field_simps]:
  assumes "c < 0"
  shows "b / c \<le> a \<longleftrightarrow> a * c \<le> b"
  by (metis assms local.minus_divide_left local.mult_minus_left local.neg_le_divide_eq local.neg_le_iff_le)

lemma neg_divide_less_eq [field_simps]:
  assumes "c < 0"
  shows "b / c < a \<longleftrightarrow> a * c < b"
  using assms local.dual_order.strict_iff_order local.neg_divide_le_eq by auto

text\<open>The following \<open>field_simps\<close> rules are necessary, as minus is always moved atop of
division but we want to get rid of division.\<close>

lemma pos_le_minus_divide_eq [field_simps]: "0 < c \<Longrightarrow> a \<le> - (b / c) \<longleftrightarrow> a * c \<le> - b"
  unfolding minus_divide_left by (rule pos_le_divide_eq)

lemma neg_le_minus_divide_eq [field_simps]: "c < 0 \<Longrightarrow> a \<le> - (b / c) \<longleftrightarrow> - b \<le> a * c"
  unfolding minus_divide_left by (rule neg_le_divide_eq)

lemma pos_less_minus_divide_eq [field_simps]: "0 < c \<Longrightarrow> a < - (b / c) \<longleftrightarrow> a * c < - b"
  unfolding minus_divide_left by (rule pos_less_divide_eq)

lemma neg_less_minus_divide_eq [field_simps]: "c < 0 \<Longrightarrow> a < - (b / c) \<longleftrightarrow> - b < a * c"
  unfolding minus_divide_left by (rule neg_less_divide_eq)

lemma pos_minus_divide_less_eq [field_simps]: "0 < c \<Longrightarrow> - (b / c) < a \<longleftrightarrow> - b < a * c"
  unfolding minus_divide_left by (rule pos_divide_less_eq)

lemma neg_minus_divide_less_eq [field_simps]: "c < 0 \<Longrightarrow> - (b / c) < a \<longleftrightarrow> a * c < - b"
  unfolding minus_divide_left by (rule neg_divide_less_eq)

lemma pos_minus_divide_le_eq [field_simps]: "0 < c \<Longrightarrow> - (b / c) \<le> a \<longleftrightarrow> - b \<le> a * c"
  unfolding minus_divide_left by (rule pos_divide_le_eq)

lemma neg_minus_divide_le_eq [field_simps]: "c < 0 \<Longrightarrow> - (b / c) \<le> a \<longleftrightarrow> a * c \<le> - b"
  unfolding minus_divide_left by (rule neg_divide_le_eq)

lemma frac_less_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y < w / z \<longleftrightarrow> (x * z - w * y) / (y * z) < 0"
  by (subst less_iff_diff_less_0) (simp add: diff_frac_eq )

lemma frac_le_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y \<le> w / z \<longleftrightarrow> (x * z - w * y) / (y * z) \<le> 0"
  by (subst le_iff_diff_le_0) (simp add: diff_frac_eq )

text\<open>Lemmas \<open>sign_simps\<close> is a first attempt to automate proofs
of positivity/negativity needed for \<open>field_simps\<close>. Have not added \<open>sign_simps\<close> to \<open>field_simps\<close> because the former can lead to case
explosions.\<close>


(* Only works once linear arithmetic is installed:
text{*An example:*}
lemma fixes a b c d e f :: "'a::linordered_field"
shows "\<lbrakk>a>b; c<d; e<f; 0 < u \<rbrakk> \<Longrightarrow>
 ((a-b)*(c-d)*(e-f))/((c-d)*(e-f)*(a-b)) <
 ((e-f)*(a-b)*(c-d))/((e-f)*(a-b)*(c-d)) + u"
apply(subgoal_tac "(c-d)*(e-f)*(a-b) > 0")
 prefer 2 apply(simp add:sign_simps)
apply(subgoal_tac "(c-d)*(e-f)*(a-b)*u > 0")
 prefer 2 apply(simp add:sign_simps)
apply(simp add:field_simps)
done
*)

lemma divide_pos_pos[simp]:
  "0 < x ==> 0 < y ==> 0 < x / y"
by(simp add:field_simps)

lemma divide_nonneg_pos:
  "0 <= x ==> 0 < y ==> 0 <= x / y"
by(simp add:field_simps)

lemma divide_neg_pos:
  "x < 0 ==> 0 < y ==> x / y < 0"
by(simp add:field_simps)

lemma divide_nonpos_pos:
  "x <= 0 ==> 0 < y ==> x / y <= 0"
by(simp add:field_simps)

lemma divide_pos_neg:
  "0 < x ==> y < 0 ==> x / y < 0"
by(simp add:field_simps)

lemma divide_nonneg_neg:
  "0 <= x ==> y < 0 ==> x / y <= 0"
by(simp add:field_simps)

lemma divide_neg_neg:
  "x < 0 ==> y < 0 ==> 0 < x / y"
by(simp add:field_simps)

lemma divide_nonpos_neg:
  "x <= 0 ==> y < 0 ==> 0 <= x / y"
by(simp add:field_simps)

lemma divide_strict_right_mono:
     "[|a < b; 0 < c|] ==> a / c < b / c"
by (simp add: less_imp_not_eq2 divide_inverse mult_strict_right_mono
              positive_imp_inverse_positive)


lemma divide_strict_right_mono_neg:
     "[|b < a; c < 0|] ==> a / c < b / c"
apply (drule divide_strict_right_mono [of _ _ "-c"], simp)
apply (simp add: less_imp_not_eq nonzero_minus_divide_right [symmetric])
done

text\<open>The last premise ensures that \<^term>\<open>a\<close> and \<^term>\<open>b\<close>
      have the same sign\<close>
lemma divide_strict_left_mono:
  "[|b < a; 0 < c; 0 < a*b|] ==> c / a < c / b"
  by (metis local.divide_neg_pos local.dual_order.strict_iff_order local.frac_less_eq local.less_iff_diff_less_0 local.mult_not_zero local.mult_strict_left_mono)

lemma divide_left_mono:
  "[|b \<le> a; 0 \<le> c; 0 < a*b|] ==> c / a \<le> c / b"
  using local.divide_cancel_left local.divide_strict_left_mono local.dual_order.order_iff_strict by auto

lemma divide_strict_left_mono_neg:
  "[|a < b; c < 0; 0 < a*b|] ==> c / a < c / b"
  by (metis local.divide_strict_left_mono local.minus_divide_left local.neg_0_less_iff_less local.neg_less_iff_less mult_commute)

lemma mult_imp_div_pos_le: "0 < y ==> x <= z * y ==>
    x / y <= z"
by (subst pos_divide_le_eq, assumption+)

lemma mult_imp_le_div_pos: "0 < y ==> z * y <= x ==>
    z <= x / y"
by(simp add:field_simps)

lemma mult_imp_div_pos_less: "0 < y ==> x < z * y ==>
    x / y < z"
by(simp add:field_simps)

lemma mult_imp_less_div_pos: "0 < y ==> z * y < x ==>
    z < x / y"
by(simp add:field_simps)

lemma frac_le: "0 <= x ==>
    x <= y ==> 0 < w ==> w <= z  ==> x / z <= y / w"
  apply (rule mult_imp_div_pos_le)
  apply simp
  apply (subst times_divide_eq_left)
  apply (rule mult_imp_le_div_pos, assumption)
  apply (rule mult_mono)
  apply simp_all
done

lemma frac_less: "0 <= x ==>
    x < y ==> 0 < w ==> w <= z  ==> x / z < y / w"
  apply (rule mult_imp_div_pos_less)
  apply simp
  apply (subst times_divide_eq_left)
  apply (rule mult_imp_less_div_pos, assumption)
  apply (erule mult_less_le_imp_less)
  apply simp_all
done

lemma frac_less2: "0 < x ==>
    x <= y ==> 0 < w ==> w < z  ==> x / z < y / w"
  apply (rule mult_imp_div_pos_less)
  apply simp_all
  apply (rule mult_imp_less_div_pos, assumption)
  apply (erule mult_le_less_imp_less)
  apply simp_all
done

lemma less_half_sum: "a < b ==> a < (a+b) / (1+1)"
  by (metis local.add_pos_pos local.add_strict_left_mono local.mult_imp_less_div_pos local.semiring_normalization_rules(4) local.zero_less_one mult_commute)

lemma gt_half_sum: "a < b ==> (a+b)/(1+1) < b"
  by (metis local.add_pos_pos local.add_strict_left_mono local.mult_imp_div_pos_less local.semiring_normalization_rules(24) local.semiring_normalization_rules(4) local.zero_less_one mult_commute)

subclass unbounded_dense_order
  sorry



lemma nonzero_abs_inverse:
  "a \<noteq> 0 ==> \<bar>inverse a\<bar> = inverse \<bar>a\<bar>"
  sorry

lemma nonzero_abs_divide:
  "b \<noteq> 0 ==> \<bar>a / b\<bar> = \<bar>a\<bar> / \<bar>b\<bar>"
  sorry

lemma field_le_epsilon:
  assumes e: "\<And>e. 0 < e \<Longrightarrow> x \<le> y + e"
  shows "x \<le> y"
  sorry

lemma inverse_positive_iff_positive [simp]:
  "(0 < inverse a) = (0 < a)"
apply (cases "a = 0", simp)
apply (blast intro: inverse_positive_imp_positive positive_imp_inverse_positive)
done


lemma zero_le_divide_abs_iff [simp]: "(0 \<le> a / \<bar>b\<bar>) = (0 \<le> a | b = 0)"
  sorry

end

code_identifier
  code_module Ordered_Fields \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

end
