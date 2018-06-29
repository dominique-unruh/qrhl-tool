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
proof-
  from assms have "u * x + v * y \<le> u * a + v * a"
    by (simp add: add_mono mult_left_mono)
  with assms show ?thesis
    unfolding distrib_right[symmetric] by simp
qed

end

subclass (in linordered_semiring_1) ordered_semiring_1 ..

class ordered_semiring_strict = semiring + comm_monoid_add + ordered_cancel_ab_semigroup_add +
  assumes mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
  assumes mult_strict_right_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a * c < b * c"
begin

subclass semiring_0_cancel ..

subclass ordered_semiring
proof
  fix a b c :: 'a
  assume *: "a \<le> b" "0 \<le> c"
  then show "c * a \<le> c * b"
    unfolding le_less
    using mult_strict_left_mono by (cases "c = 0") auto
  from * show "a * c \<le> b * c"
    unfolding le_less
    using mult_strict_right_mono by (cases "c = 0") auto
qed

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
lemma mult_strict_mono:
  assumes "a < b" and "c < d" and "0 < b" and "0 \<le> c"
  shows "a * c < b * d"
  using assms
  apply (cases "c = 0")
   apply simp
  apply (erule mult_strict_right_mono [THEN less_trans])
   apply (auto simp add: le_less)
  apply (erule (1) mult_strict_left_mono)
  done

text \<open>This weaker variant has more natural premises\<close>
lemma mult_strict_mono':
  assumes "a < b" and "c < d" and "0 \<le> a" and "0 \<le> c"
  shows "a * c < b * d"
  by (rule mult_strict_mono) (insert assms, auto)

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
proof
  fix a b c :: 'a
  assume "a \<le> b" "0 \<le> c"
  then show "c * a \<le> c * b"
    unfolding le_less
    using mult_strict_left_mono by (cases "c = 0") auto
qed

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

lemma frac_less_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y < w / z \<longleftrightarrow> (x * z - w * y) / (y * z) < 0"
  by (subst less_iff_diff_less_0) (simp add: diff_frac_eq )

lemma frac_le_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y \<le> w / z \<longleftrightarrow> (x * z - w * y) / (y * z) \<le> 0"
  by (subst le_iff_diff_le_0) (simp add: diff_frac_eq )


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

lemma comparable:
  assumes "a \<le> c \<or> a \<ge> c"
    and "b \<le> c \<or> b \<ge> c"
  shows "a \<le> b \<or> b \<le> a"
  using assms 
proof auto
  assume "a \<le> c" and "b \<le> c"
  hence "0 \<le> c-a" and "0 \<le> c-b" by auto
  hence "c-a \<le> c-b \<or> c-a \<ge> c-b" by (rule nn_comparable)
  hence "-a \<le> -b \<or> -a \<ge> -b"
    using local.add_le_imp_le_right local.uminus_add_conv_diff by presburger
  moreover assume "\<not> b \<le> a"
  ultimately show "a \<le> b" by simp
    thm nn_comparable
  next
    assume "c \<le> a" and "b \<le> c"
    hence "b \<le> a" by auto
    moreover assume "\<not> b \<le> a"
    ultimately have False by simp
    then show "a \<le> b" by simp
  next
  assume "a \<ge> c" and "b \<ge> c"
  hence "0 \<le> a-c" and "0 \<le> b-c" by auto
  hence "a-c \<le> b-c \<or> a-c \<ge> b-c" by (rule nn_comparable)
  hence "a \<le> b \<or> a \<ge> b"
    by (simp add: local.le_diff_eq)
  moreover assume "\<not> b \<le> a"
  ultimately show "a \<le> b" by simp
qed

lemma negative_imp_inverse_negative:
  "a < 0 \<Longrightarrow> inverse a < 0"
  by (insert positive_imp_inverse_positive [of "-a"],
    simp add: nonzero_inverse_minus_eq less_imp_not_eq)


lemma inverse_positive_imp_positive:
  assumes inv_gt_0: "0 < inverse a" and nz: "a \<noteq> 0"
  shows "0 < a"
proof -
  have "0 < inverse (inverse a)"
    using inv_gt_0 by (rule positive_imp_inverse_positive)
  thus "0 < a"
    using nz by (simp add: nonzero_inverse_inverse_eq)
qed

lemma inverse_negative_imp_negative:
  assumes inv_less_0: "inverse a < 0" and nz: "a \<noteq> 0"
  shows "a < 0"
proof -
  have "inverse (inverse a) < 0"
    using inv_less_0 by (rule negative_imp_inverse_negative)
  thus "a < 0" using nz by (simp add: nonzero_inverse_inverse_eq)
qed

lemma linordered_field_no_lb:
  "\<forall>x. \<exists>y. y < x"
proof
  fix x::'a
  have m1: "- (1::'a) < 0" by simp
  from add_strict_right_mono[OF m1, where c=x]
  have "(- 1) + x < x" by simp
  thus "\<exists>y. y < x" by blast
qed

lemma linordered_field_no_ub:
  "\<forall> x. \<exists>y. y > x"
proof
  fix x::'a
  have m1: " (1::'a) > 0" by simp
  from add_strict_right_mono[OF m1, where c=x]
  have "1 + x > x" by simp
  thus "\<exists>y. y > x" by blast
qed

lemma less_imp_inverse_less:
  assumes less: "a < b" and apos:  "0 < a"
  shows "inverse b < inverse a"
  using assms by (metis local.dual_order.strict_iff_order local.inverse_inverse_eq local.inverse_le_imp_le local.positive_imp_inverse_positive)

lemma inverse_less_imp_less:
  "inverse a < inverse b \<Longrightarrow> 0 < a \<Longrightarrow> b < a"
  apply (simp add: less_le [of "inverse a"] less_le [of "b"])
  by (force dest!: inverse_le_imp_le nonzero_inverse_eq_imp_eq)


text\<open>Both premises are essential. Consider -1 and 1.\<close>
lemma inverse_less_iff_less [simp]:
  "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> inverse a < inverse b \<longleftrightarrow> b < a"
  by (blast intro: less_imp_inverse_less dest: inverse_less_imp_less)

lemma le_imp_inverse_le:
  "a \<le> b \<Longrightarrow> 0 < a \<Longrightarrow> inverse b \<le> inverse a"
  by (force simp add: le_less less_imp_inverse_less)

lemma inverse_le_iff_le [simp]:
  "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> inverse a \<le> inverse b \<longleftrightarrow> b \<le> a"
  by (blast intro: le_imp_inverse_le dest: inverse_le_imp_le)


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
apply (insert inverse_less_iff_less [of "-b" "-a"])
apply (simp del: inverse_less_iff_less
            add: nonzero_inverse_minus_eq)
done

lemma le_imp_inverse_le_neg:
  "a \<le> b \<Longrightarrow> b < 0 ==> inverse b \<le> inverse a"
  by (force simp add: le_less less_imp_inverse_less_neg)

lemma inverse_le_iff_le_neg [simp]:
  "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> inverse a \<le> inverse b \<longleftrightarrow> b \<le> a"
  by (blast intro: le_imp_inverse_le_neg dest: inverse_le_imp_le_neg)

lemma one_less_inverse:
  "0 < a \<Longrightarrow> a < 1 \<Longrightarrow> 1 < inverse a"
  using less_imp_inverse_less [of a 1, unfolded inverse_1] .

lemma one_le_inverse:
  "0 < a \<Longrightarrow> a \<le> 1 \<Longrightarrow> 1 \<le> inverse a"
  using le_imp_inverse_le [of a 1, unfolded inverse_1] .

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
proof
  fix x y :: 'a
  have less_add_one: "a < a + 1" for a::'a by auto
  from less_add_one show "\<exists>y. x < y" apply (rule_tac exI[of _ "x+1"]) by auto
  from less_add_one have "x + (- 1) < (x + 1) + (- 1)"
    by (rule add_strict_right_mono)
  then have "x - 1 < x + 1 - 1" by simp
  then have "x - 1 < x" by (simp add: algebra_simps)
  then show "\<exists>y. y < x" ..
  show "x < y \<Longrightarrow> \<exists>z>x. z < y" by (blast intro!: less_half_sum gt_half_sum)
qed


lemma dense_le_bounded:
  fixes x y z :: 'a
  assumes "x < y"
  assumes *: "\<And>w. \<lbrakk> x < w ; w < y \<rbrakk> \<Longrightarrow> w \<le> z"
  shows "y \<le> z"
proof (rule dense_le)
  fix w assume "w < y"
  from dense[OF \<open>x < y\<close>] obtain u where "x < u" "u < y" by safe
  have "u \<le> w \<or> w \<le> u"
    apply (rule comparable[of _ y])
    using \<open>w<y\<close> \<open>u<y\<close> by auto
  then show "w \<le> z"
  proof (rule disjE)
    assume "u \<le> w"
    from less_le_trans[OF \<open>x < u\<close> \<open>u \<le> w\<close>] \<open>w < y\<close>
    show "w \<le> z" by (rule *)
  next
    assume "w \<le> u"
    from \<open>w \<le> u\<close> *[OF \<open>x < u\<close> \<open>u < y\<close>]
    show "w \<le> z" by (rule order_trans)
  qed
qed

subclass field_abs_sgn ..


lemma nonzero_abs_inverse:
  "a \<noteq> 0 ==> \<bar>inverse a\<bar> = inverse \<bar>a\<bar>"
  by (rule abs_inverse)

lemma nonzero_abs_divide:
  "b \<noteq> 0 ==> \<bar>a / b\<bar> = \<bar>a\<bar> / \<bar>b\<bar>"
  by (rule abs_divide)

lemma field_le_epsilon:
  assumes e: "\<And>e. 0 < e \<Longrightarrow> x \<le> y + e"
  shows "x \<le> y"
proof (rule dense_le)
  fix t assume "t < x"
  hence "0 < x - t" by (simp add: less_diff_eq)
  from e [OF this] have "x + 0 \<le> x + (y - t)" by (simp add: algebra_simps)
  then have "0 \<le> y - t" by (simp only: add_le_cancel_left)
  then show "t \<le> y" by (simp add: algebra_simps)
qed

lemma inverse_positive_iff_positive [simp]:
  "(0 < inverse a) = (0 < a)"
apply (cases "a = 0", simp)
apply (blast intro: inverse_positive_imp_positive positive_imp_inverse_positive)
done

lemma inverse_negative_iff_negative [simp]:
  "(inverse a < 0) = (a < 0)"
apply (cases "a = 0", simp)
apply (blast intro: inverse_negative_imp_negative negative_imp_inverse_negative)
done

lemma inverse_nonnegative_iff_nonnegative [simp]:
  "0 \<le> inverse a \<longleftrightarrow> 0 \<le> a"
  by (simp add: local.dual_order.order_iff_strict)

lemma inverse_nonpositive_iff_nonpositive [simp]:
  "inverse a \<le> 0 \<longleftrightarrow> a \<le> 0"
  using local.inverse_nonnegative_iff_nonnegative local.neg_0_le_iff_le by fastforce

lemma one_less_inverse_iff: "1 < inverse x \<longleftrightarrow> 0 < x \<and> x < 1"
  using less_trans[of 1 x 0 for x]
  by (metis local.dual_order.strict_trans local.inverse_1 local.inverse_less_imp_less local.inverse_positive_iff_positive local.one_less_inverse local.zero_less_one)

lemma one_le_inverse_iff: "1 \<le> inverse x \<longleftrightarrow> 0 < x \<and> x \<le> 1"
  by (metis local.dual_order.strict_trans1 local.inverse_1 local.inverse_le_imp_le local.inverse_positive_iff_positive local.one_le_inverse local.zero_less_one)

lemma inverse_less_1_iff: "inverse x < 1 \<longleftrightarrow> x \<le> 0 \<or> 1 < x"
proof (rule)
  assume invx1: "inverse x < 1"
  have "inverse x \<le> 0 \<or> inverse x \<ge> 0"
    apply (rule comparable[where c=1]) 
    apply (rule disjI1) using invx1 apply simp
    using zero_less_one
    by (simp add: local.order.strict_iff_order)
  then consider (leq0) "inverse x \<le> 0" | (pos) "inverse x > 0" | (zero) "inverse x = 0"
    apply atomize_elim by auto
  then show "x \<le> 0 \<or> 1 < x"
  proof cases
    case leq0
    (* hence "x \<le> 0" by auto *)
    then show ?thesis by simp
  next
    case pos
    hence "x > 0" by auto
    moreover from invx1 have "inverse x < inverse 1" by auto
    ultimately have "x > 1"
      using local.inverse_less_imp_less by blast
    then show ?thesis by simp
  next
    case zero then show ?thesis by simp
  qed
next
  assume "x \<le> 0 \<or> 1 < x"
  then consider (neg) "x \<le> 0" | (g1) "1 < x" by auto
  then show "inverse x < 1"
  proof cases
    case neg
    then show ?thesis
      by (metis local.dual_order.order_iff_strict local.dual_order.strict_trans local.inverse_negative_iff_negative local.inverse_zero local.zero_less_one)
  next
    case g1
    then show ?thesis
      using local.less_imp_inverse_less by fastforce
  qed
qed

lemma inverse_le_1_iff: "inverse x \<le> 1 \<longleftrightarrow> x \<le> 0 \<or> 1 \<le> x"
  by (metis local.dual_order.order_iff_strict local.inverse_1 local.inverse_le_iff_le local.inverse_less_1_iff local.one_le_inverse_iff)

(* lemma [divide_simps]:
  shows le_divide_eq: "a \<le> b / c \<longleftrightarrow> (if 0 < c then a * c \<le> b else if c < 0 then b \<le> a * c else a \<le> 0)"
    and divide_le_eq: "b / c \<le> a \<longleftrightarrow> (if 0 < c then b \<le> a * c else if c < 0 then a * c \<le> b else 0 \<le> a)"
    and less_divide_eq: "a < b / c \<longleftrightarrow> (if 0 < c then a * c < b else if c < 0 then b < a * c else a < 0)"
    and divide_less_eq: "b / c < a \<longleftrightarrow> (if 0 < c then b < a * c else if c < 0 then a * c < b else 0 < a)"
    and le_minus_divide_eq: "a \<le> - (b / c) \<longleftrightarrow> (if 0 < c then a * c \<le> - b else if c < 0 then - b \<le> a * c else a \<le> 0)"
    and minus_divide_le_eq: "- (b / c) \<le> a \<longleftrightarrow> (if 0 < c then - b \<le> a * c else if c < 0 then a * c \<le> - b else 0 \<le> a)"
    and less_minus_divide_eq: "a < - (b / c) \<longleftrightarrow> (if 0 < c then a * c < - b else if c < 0 then - b < a * c else  a < 0)"
    and minus_divide_less_eq: "- (b / c) < a \<longleftrightarrow> (if 0 < c then - b < a * c else if c < 0 then a * c < - b else 0 < a)"
  by (auto simp: field_simps not_less dest: antisym) *)

text \<open>Division and Signs\<close>

(* lemma
  shows zero_less_divide_iff: "0 < a / b \<longleftrightarrow> 0 < a \<and> 0 < b \<or> a < 0 \<and> b < 0"
    and divide_less_0_iff: "a / b < 0 \<longleftrightarrow> 0 < a \<and> b < 0 \<or> a < 0 \<and> 0 < b"
    and zero_le_divide_iff: "0 \<le> a / b \<longleftrightarrow> 0 \<le> a \<and> 0 \<le> b \<or> a \<le> 0 \<and> b \<le> 0"
    and divide_le_0_iff: "a / b \<le> 0 \<longleftrightarrow> 0 \<le> a \<and> b \<le> 0 \<or> a \<le> 0 \<and> 0 \<le> b"
  by (auto simp add: divide_simps) *)

text \<open>Division and the Number One\<close>

text\<open>Simplify expressions such as \<open>0 < 1/x\<close> to \<open>0 < x\<close>\<close>

lemma zero_le_divide_1_iff [simp]:
  "0 \<le> 1 / a \<longleftrightarrow> 0 \<le> a"
  using local.dual_order.order_iff_strict local.inverse_eq_divide local.inverse_positive_iff_positive by auto

lemma zero_less_divide_1_iff [simp]:
  "0 < 1 / a \<longleftrightarrow> 0 < a"
  by (simp add: local.dual_order.strict_iff_order)

lemma divide_le_0_1_iff [simp]:
  "1 / a \<le> 0 \<longleftrightarrow> a \<le> 0"
  by (smt comparable local.dual_order.order_iff_strict local.eq_iff local.inverse_eq_divide local.inverse_le_1_iff local.one_divide_eq_0_iff local.one_le_inverse_iff local.zero_less_divide_1_iff)

lemma divide_less_0_1_iff [simp]:
  "1 / a < 0 \<longleftrightarrow> a < 0"
  using local.dual_order.strict_iff_order by auto

lemma divide_right_mono:
     "[|a \<le> b; 0 \<le> c|] ==> a/c \<le> b/c"
  using local.divide_cancel_right local.divide_strict_right_mono local.dual_order.order_iff_strict by blast

lemma divide_right_mono_neg: "a <= b
    ==> c <= 0 ==> b / c <= a / c"
  by (metis local.divide_cancel_right local.divide_strict_right_mono_neg local.dual_order.strict_implies_order local.eq_refl local.le_imp_less_or_eq)

lemma divide_left_mono_neg: "a <= b
    ==> c <= 0 ==> 0 < a * b ==> c / a <= c / b"  
  by (metis local.divide_left_mono local.minus_divide_left local.neg_0_le_iff_le local.neg_le_iff_le mult_commute)

lemma divide_nonneg_nonneg [simp]:
  "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> x / y"
  using local.divide_eq_0_iff local.divide_nonneg_pos local.dual_order.order_iff_strict by blast

lemma divide_nonpos_nonpos:
  "x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> 0 \<le> x / y"
  using local.divide_nonpos_neg local.dual_order.order_iff_strict by auto

lemma divide_nonneg_nonpos:
  "0 \<le> x \<Longrightarrow> y \<le> 0 \<Longrightarrow> x / y \<le> 0"
  by (metis local.divide_eq_0_iff local.divide_nonneg_neg local.dual_order.order_iff_strict)

lemma divide_nonpos_nonneg:
  "x \<le> 0 \<Longrightarrow> 0 \<le> y \<Longrightarrow> x / y \<le> 0"
  using local.divide_nonpos_pos local.dual_order.order_iff_strict by auto

text \<open>Conditional Simplification Rules: No Case Splits\<close>

lemma le_divide_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (1 \<le> b/a) = (a \<le> b)"
  by (simp add: local.pos_le_divide_eq)

lemma le_divide_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> (1 \<le> b/a) = (b \<le> a)"
  by (metis local.le_divide_eq_1_pos local.minus_divide_divide local.neg_0_less_iff_less local.neg_le_iff_le)

lemma divide_le_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (b/a \<le> 1) = (b \<le> a)"
  using local.pos_divide_le_eq by auto

lemma divide_le_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> (b/a \<le> 1) = (a \<le> b)"
  by (metis local.divide_le_eq_1_pos local.minus_divide_divide local.neg_0_less_iff_less local.neg_le_iff_le)

lemma less_divide_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (1 < b/a) = (a < b)"
  by (simp add: local.dual_order.strict_iff_order)

lemma less_divide_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> (1 < b/a) = (b < a)"
  using local.dual_order.strict_iff_order by auto

lemma divide_less_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (b/a < 1) = (b < a)"
  using local.divide_le_eq_1_pos local.dual_order.strict_iff_order by auto

lemma divide_less_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> b/a < 1 \<longleftrightarrow> a < b"
  using local.dual_order.strict_iff_order by auto

lemma abs_div_pos: "0 < y ==>
    \<bar>x\<bar> / y = \<bar>x / y\<bar>"
  by (simp add: local.abs_pos)


lemma zero_le_divide_abs_iff [simp]: "(0 \<le> a / \<bar>b\<bar>) = (0 \<le> a | b = 0)"
proof 
  assume assm: "0 \<le> a / \<bar>b\<bar>"
  have absb: "abs b \<ge> 0" by (fact abs_nn)
  then have eq: "0 * abs b \<le> a / abs b * abs b"
    using assm local.mult_right_mono by blast
  show "0 \<le> a \<or> b = 0"
  proof (cases "b=0")
    case False
    then have absb0: "abs b \<noteq> 0"
      by (simp add: local.abs_eq_0_iff)
    then have "a / abs b * abs b = a" by simp
    with eq absb0 have "0 \<le> a" by auto
    then show ?thesis by simp
  next
    case True
    then show ?thesis by simp
  qed
next
  assume "0 \<le> a \<or> b = 0"
  then consider (a) "0 \<le> a" | (b) "b = 0" by atomize_elim auto
  then show "0 \<le> a / \<bar>b\<bar>"
  proof cases
    case a
    then show ?thesis using abs_nn by auto
  next
    case b
    then show ?thesis by auto
  qed
qed


lemma divide_le_0_abs_iff [simp]: "(a / \<bar>b\<bar> \<le> 0) = (a \<le> 0 | b = 0)"
  by (metis local.minus_divide_left local.neg_0_le_iff_le local.zero_le_divide_abs_iff)

(* True? 
lemma field_le_mult_one_interval:
  assumes *: "\<And>z. \<lbrakk> 0 < z ; z < 1 \<rbrakk> \<Longrightarrow> z * x \<le> y"
  shows "x \<le> y"
*)

text\<open>For creating values between \<^term>\<open>u\<close> and \<^term>\<open>v\<close>.\<close>
lemma scaling_mono:
  assumes "u \<le> v" "0 \<le> r" "r \<le> s"
    shows "u + r * (v - u) / s \<le> v"
proof -
  have "r/s \<le> 1" using assms
    by (metis local.divide_le_eq_1_pos local.division_ring_divide_zero local.dual_order.order_iff_strict local.dual_order.trans local.zero_less_one)
  then have "(r/s) * (v - u) \<le> 1 * (v - u)"
    apply (rule mult_right_mono)
    using assms by simp
  then show ?thesis
    by (simp add: field_simps)
qed

end


code_identifier
  code_module Ordered_Fields \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

end
