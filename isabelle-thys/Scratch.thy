theory Scratch
  imports "HOL-Library.Rewrite"
Complex_Bounded_Operators.Cblinfun_Matrix
Complex_Bounded_Operators.Cblinfun_Code
    (* "HOL-Library.Code_Target_Nat" *)
begin

unbundle cblinfun_notation

lemma \<open>one_dim_iso (vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi>) = \<psi> \<bullet>\<^sub>C \<phi>\<close>
  by simp


lemma \<open>\<psi> * \<phi> = one_dim_iso \<psi> \<bullet>\<^sub>C \<phi>\<close>
by -

lemma \<open>one_dim_iso \<psi> * \<phi> = \<psi> \<bullet>\<^sub>C \<phi>\<close>
by -

lemma \<open>one_dim_iso \<psi> * one_dim_iso \<phi> = \<psi> \<bullet>\<^sub>C \<phi>\<close>
by -

lemma \<open>\<psi> * \<phi> = one_dim_iso \<psi> \<bullet>\<^sub>C one_dim_iso \<phi>\<close>
  by -

lemma \<open>xxx = one_dim_iso (one_dim_iso \<psi> *\<^sub>C \<phi>)\<close>
(* apply (subst one_dim_scaleC_1[of \<psi>, symmetric]) *)
  (* apply (subst (1) one_dim_scaleC_1[of \<phi>, symmetric]) *)
  (* apply (subst (2) one_dim_scaleC_1[of \<phi>, symmetric]) *)
  using[[simp_trace]]
  apply (simp add: )

try0
sledgehammer [dont_slice]
apply (simp add: )

thm scaleC_conv_of_complex
  by x

lemma one_dim_apply_is_times:
  fixes A :: "'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'b::one_dim" and B :: "'a"
  shows "A *\<^sub>V B = one_dim_iso A * one_dim_iso B"
  apply (subst one_dim_scaleC_1[of A, symmetric])
  apply (subst one_dim_scaleC_1[of B, symmetric])
  apply (simp only: cblinfun.scaleC_left cblinfun.scaleC_right)
  by simp

typ ell2
thm one_dim_apply_is_times
thm one_dim_iso_comp_distr_times

class one_dim = one_dim
class complex_inner = complex_inner
instantiation cblinfun :: (one_dim, one_dim) complex_inner begin
instance sorry
end

end


instantiation cblinfun :: (one_dim, one_dim) complex_inner begin

typ \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>

  by (metis norm_of_complex of_complex_one_dim_iso one_dim_norm)


instance complex :: one_dim sorry


lemma \<open>one_dim_iso\<close>

class one_dim = onb_enum + one + times + inverse +
  assumes one_dim_canonical_basis[simp]: \<open>canonical_basis = [1]\<close>
  assumes one_dim_prod_scale1: \<open>(a *\<^sub>C 1) * (b *\<^sub>C 1) = (a * b) *\<^sub>C 1\<close>
  assumes divide_inverse: \<open>x / y = x * inverse y\<close>
  assumes one_dim_inverse: \<open>inverse (a *\<^sub>C 1) = inverse a *\<^sub>C 1\<close>

term \<open>x :: _ :: one_dim\<close>

term \<open>cdim UNIV = 1\<close>

term \<open>norm 1 \<noteq> 1\<close>

definition \<open>one_dim_iso a = of_complex (1 \<bullet>\<^sub>C a)\<close> for one_dim_iso

thm norm_one
term one_dim_iso