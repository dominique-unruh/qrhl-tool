theory Ordered_Complex
  imports "HOL.Complex" Ordered_Fields "Jordan_Normal_Form.Conjugate" 
begin

declare Conjugate.less_eq_complex_def[simp del]
declare Conjugate.less_complex_def[simp del]

(* declare[[coercion_enabled=false]] *)

subsection \<open>Ordering on complex numbers\<close>

(*
Add this if we remove Jordan_Normal_Form.Conjugate 

instantiation complex :: ord begin
definition [simp]: "x < y \<equiv> Im x = Im y \<and> Re x < Re y"
definition [simp]: "x \<le> y \<equiv> Im x = Im y \<and> Re x \<le> Re y"
instance ..
end

instantiation complex :: ordered_comm_monoid_add begin
instance
proof intro_classes
  note defs = less_eq_complex_def less_complex_def abs_complex_def
  fix x y z a b c :: complex
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding defs by auto
  show "x \<le> x" unfolding defs by auto
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding defs by auto
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding defs by (simp add: complex.expand)
  show "a \<le> b \<Longrightarrow> c + a \<le> c + b" unfolding defs by auto
qed
end *)

instantiation complex :: nice_ordered_field begin
(* definition "x \<le> y \<longleftrightarrow> Re x \<le> Re y \<and> Im x = Im y"
definition "x < y \<longleftrightarrow> Re x < Re y \<and> Im x = Im y" for x y :: complex *)
instance
proof intro_classes
  note defs = less_eq_complex_def less_complex_def abs_complex_def
  fix x y z a b c :: complex
(*    show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding defs by auto
  show "x \<le> x" unfolding defs by auto
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding defs by auto
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding defs by (simp add: complex.expand)
  show "a \<le> b \<Longrightarrow> c + a \<le> c + b" unfolding defs by auto *)
  show "a \<le> 0 \<Longrightarrow> \<bar>a\<bar> = - a" unfolding defs
    by (simp add: cmod_eq_Re complex_is_Real_iff)
  show "0 \<le> a \<Longrightarrow> \<bar>a\<bar> = a"
    unfolding defs
    by (metis abs_of_nonneg cmod_eq_Re comp_apply complex.exhaust_sel complex_of_real_def zero_complex.simps(1) zero_complex.simps(2))
  show "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b" unfolding defs by auto
  show "0 < (1::complex)" unfolding defs by simp
  show "0 < a \<Longrightarrow> 0 < inverse a" unfolding defs by auto
  define ra ia rb ib rc ic where "ra = Re a" "ia = Im a" "rb = Re b" "ib = Im b" "rc = Re c" "ic = Im c"
  note ri = this[symmetric]
  then have "a = Complex ra ia" "b = Complex rb ib" "c = Complex rc ic" by auto
  note ri = this ri
  show "inverse a \<le> inverse b \<Longrightarrow> 0 < a \<Longrightarrow> b \<le> a" unfolding defs ri
    apply (auto simp: power2_eq_square) apply (cases "rb=0") 
    apply auto
    by (metis divide_eq_0_iff divide_le_eq_1 eq_iff less_eq_real_def less_le nice_ordered_field_class.frac_le nice_ordered_field_class.frac_less2 not_le)
  show "(\<And>a. a < b \<Longrightarrow> a \<le> c) \<Longrightarrow> b \<le> c" unfolding defs ri
    apply auto
    apply (metis complex.sel(1) complex.sel(2) lt_ex)
    by (metis complex.sel(1) complex.sel(2) dense not_less)
  show "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a \<le> b \<or> b \<le> a" unfolding defs by auto
  show "0 \<le> \<bar>x\<bar>" unfolding defs by auto
qed
end

lemma less_eq_complexI: "Re x \<le> Re y \<Longrightarrow> Im x = Im y \<Longrightarrow> x\<le>y" unfolding less_eq_complex_def by simp
lemma less_complexI: "Re x < Re y \<Longrightarrow> Im x = Im y \<Longrightarrow> x<y" unfolding less_complex_def by simp

lemma complex_of_real_mono:
  "x \<le> y \<Longrightarrow> complex_of_real x \<le> complex_of_real y"
  unfolding less_eq_complex_def by auto

lemma complex_of_real_mono_iff[simp]:
  "complex_of_real x \<le> complex_of_real y \<longleftrightarrow> x \<le> y"
  unfolding less_eq_complex_def by auto

lemma complex_of_real_strict_mono_iff[simp]:
  "complex_of_real x < complex_of_real y \<longleftrightarrow> x < y"
  unfolding less_complex_def by auto

lemma complex_of_real_nn_iff[simp]:
  "0 \<le> complex_of_real y \<longleftrightarrow> 0 \<le> y"
  unfolding less_eq_complex_def by auto

lemma complex_of_real_pos_iff[simp]:
  "0 < complex_of_real y \<longleftrightarrow> 0 < y"
  unfolding less_complex_def by auto

lemma Re_mono: "x \<le> y \<Longrightarrow> Re x \<le> Re y"
  unfolding less_eq_complex_def by simp

lemma comp_Im_same: "x \<le> y \<Longrightarrow> Im x = Im y"
  unfolding less_eq_complex_def by simp


lemma Re_strict_mono: "x < y \<Longrightarrow> Re x < Re y"
  unfolding less_complex_def by simp

lemma complex_of_real_cmod: assumes "x \<ge> 0" shows "complex_of_real (cmod x) = x"
  by (metis Reals_cases abs_of_nonneg assms comp_Im_same complex_is_Real_iff complex_of_real_nn_iff norm_of_real zero_complex.simps(2))

end
