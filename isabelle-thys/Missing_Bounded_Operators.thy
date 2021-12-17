theory Missing_Bounded_Operators
  imports Complex_Bounded_Operators.Complex_L2
begin

unbundle cblinfun_notation

declare cindependent_ket[simp]

definition explicit_cblinfun :: \<open>('a \<Rightarrow> 'b \<Rightarrow> complex) \<Rightarrow> ('b ell2, 'a ell2) cblinfun\<close> where
  \<open>explicit_cblinfun m = cblinfun_extension (range ket) (\<lambda>a. Abs_ell2 (\<lambda>j. m j (inv ket a)))\<close>

lemma explicit_cblinfun_ket[simp]: \<open>explicit_cblinfun m *\<^sub>V ket a = Abs_ell2 (\<lambda>b. m b a)\<close> for m :: "_ \<Rightarrow> _ :: finite \<Rightarrow> _"
  by (auto simp: cblinfun_extension_exists_finite_dim explicit_cblinfun_def cblinfun_extension_apply)

definition permute_and_tensor1_cblinfun where [code del]: \<open>permute_and_tensor1_cblinfun f R a =
  explicit_cblinfun (\<lambda>i j. if R i j then Rep_ell2 (a *\<^sub>V ket (f j)) (f i) else 0)\<close>

(* Original enum_idx_bound should say this, and be [simp] *)
lemma enum_idx_bound'[simp]: "enum_idx x < CARD('a)" for x :: "'a::enum"
  using enum_idx_bound unfolding card_UNIV_length_enum by auto

(* basis_enum should define "canonical_basis_length" (or maybe "dimension" or something). Reason: code generation otherwise has to 
    compute the length of canonical_basis each time the dimension is needed.
   Or it could be in the/a type class "finite_dim".
 *)
abbreviation \<open>cdimension (x::'a::basis_enum itself) \<equiv> length (canonical_basis :: 'a list)\<close>

end