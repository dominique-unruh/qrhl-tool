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

end

instantiation complex :: ordered_comm_monoid_add begin
instance
  sorry
end *)

instantiation complex :: nice_ordered_field begin
(* definition "x \<le> y \<longleftrightarrow> Re x \<le> Re y \<and> Im x = Im y"
definition "x < y \<longleftrightarrow> Re x < Re y \<and> Im x = Im y" for x y :: complex *)
instance
  sorry
end



lemma Re_strict_mono: "x < y \<Longrightarrow> Re x < Re y"
  unfolding less_complex_def by simp

lemma complex_of_real_cmod: assumes "x \<ge> 0" shows "complex_of_real (cmod x) = x"
  sorry

end
