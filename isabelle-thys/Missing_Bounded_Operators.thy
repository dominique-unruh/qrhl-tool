theory Missing_Bounded_Operators
  imports Complex_Bounded_Operators.Complex_L2
begin

unbundle cblinfun_notation

declare cindependent_ket[simp]

definition explicit_cblinfun :: \<open>('a \<Rightarrow> 'b \<Rightarrow> complex) \<Rightarrow> ('b ell2, 'a ell2) cblinfun\<close> where
  \<open>explicit_cblinfun m = cblinfun_extension (range ket) (\<lambda>a. Abs_ell2 (\<lambda>j. m j (inv ket a)))\<close>

lemma explicit_cblinfun_ket[simp]: \<open>explicit_cblinfun m *\<^sub>V ket a = Abs_ell2 (\<lambda>b. m b a)\<close> for m :: "_ \<Rightarrow> _ :: finite \<Rightarrow> _"
  by (auto simp: cblinfun_extension_exists_finite_dim explicit_cblinfun_def cblinfun_extension_apply)


end