theory Missing_Bounded_Operators
  imports Complex_Bounded_Operators.Complex_L2 Complex_Bounded_Operators.Cblinfun_Code
begin

unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)
unbundle jnf_notation

declare cindependent_ket[simp]

definition explicit_cblinfun :: \<open>('a \<Rightarrow> 'b \<Rightarrow> complex) \<Rightarrow> ('b ell2, 'a ell2) cblinfun\<close> where
  \<open>explicit_cblinfun m = cblinfun_extension (range ket) (\<lambda>a. Abs_ell2 (\<lambda>j. m j (inv ket a)))\<close>

lemma explicit_cblinfun_ket[simp]: \<open>explicit_cblinfun m *\<^sub>V ket a = Abs_ell2 (\<lambda>b. m b a)\<close> for m :: "_ \<Rightarrow> _ :: finite \<Rightarrow> _"
  by (auto simp: cblinfun_extension_exists_finite_dim explicit_cblinfun_def cblinfun_extension_apply)

(* Original enum_idx_bound should say this, and be [simp] *)
lemma enum_idx_bound'[simp]: "enum_idx x < CARD('a)" for x :: "'a::enum"
  using enum_idx_bound unfolding card_UNIV_length_enum by auto

(* basis_enum should define "canonical_basis_length" (or maybe "dimension" or something). Reason: code generation otherwise has to 
    compute the length of canonical_basis each time the dimension is needed.
   Or it could be in the/a type class "finite_dim".
 *)
abbreviation \<open>cdimension (x::'a::basis_enum itself) \<equiv> length (canonical_basis :: 'a list)\<close>


class eenum = enum +
  fixes enum_nth :: \<open>nat \<Rightarrow> 'a\<close>
  fixes enum_index :: \<open>'a \<Rightarrow> nat\<close>
  assumes enum_nth_enum[simp]: \<open>\<And>i. i < CARD('a) \<Longrightarrow> Enum.enum ! i = enum_nth i\<close>
  assumes enum_nth_invalid: \<open>\<And>i. i \<ge> CARD('a) \<Longrightarrow> enum_nth i = enum_nth 0\<close> (* To get enum_index_nth below *)
  assumes enum_nth_index[simp]: \<open>\<And>a. enum_nth (enum_index a) = a\<close>
  assumes enum_index_bound[simp]: \<open>\<And>a. enum_index a < CARD('a)\<close>

lemma inj_enum_index[simp]: \<open>inj enum_index\<close>
  by (metis enum_nth_index injI)

lemma bij_betw_enum_index: \<open>bij_betw (enum_index :: 'a::eenum \<Rightarrow> nat) UNIV {..<CARD('a)}\<close>
proof -
  let ?f = \<open>enum_index :: 'a::eenum \<Rightarrow> nat\<close>
  have \<open>range ?f \<subseteq> {..<CARD('a)}\<close>
    by (simp add: image_subsetI)
  moreover have \<open>card (range ?f) = card {..<CARD('a)}\<close>
    by (simp add: card_image)
  moreover have \<open>finite {..<CARD('a)}\<close>
    by simp
  ultimately have \<open>range ?f = {..<CARD('a)}\<close>
    by (meson card_subset_eq)
  then show ?thesis
    by (simp add: bij_betw_imageI)
qed

lemma inj_on_enum_nth[simp]: \<open>inj_on (enum_nth :: _ \<Rightarrow> 'a::eenum) {..<CARD('a)}\<close>
  by (metis (mono_tags, opaque_lifting) bij_betw_enum_index enum_nth_index f_the_inv_into_f_bij_betw inj_on_inverseI)

lemma enum_index_nth: \<open>enum_index (enum_nth i :: 'a::eenum) = (if i < CARD('a) then i else 0)\<close>
  by (metis bij_betw_enum_index enum_nth_index enum_nth_invalid f_the_inv_into_f_bij_betw lessThan_iff linorder_not_le zero_less_card_finite)

instantiation bool :: eenum begin
definition \<open>enum_index_bool x = (if x then 1 else 0 :: nat)\<close>
definition \<open>enum_nth_bool (i::nat) = (i=1)\<close>
instance 
  apply standard
  apply (auto simp: enum_bool_def enum_index_bool_def enum_nth_bool_def)
  by (metis less_2_cases nth_Cons_0)
end

instantiation prod :: (eenum,eenum) eenum begin
definition \<open>enum_index_prod = (\<lambda>(i::'a,j::'b). enum_index i * CARD('b) + enum_index j)\<close>
definition \<open>enum_nth_prod ij = (let i = ij div CARD('b) in if i < CARD('a) then (enum_nth i, enum_nth (ij mod CARD('b))) else (enum_nth 0, enum_nth 0) :: 'a\<times>'b)\<close>
instance
proof standard
  show \<open>i < CARD('a \<times> 'b) \<Longrightarrow> (Enum.enum ! i :: 'a\<times>'b) = enum_nth i\<close> for i
    apply (auto simp: card_UNIV_length_enum[symmetric] enum_nth_enum enum_prod_def product_nth enum_nth_prod_def Let_def)
    using less_mult_imp_div_less by blast+
  show \<open>CARD('a \<times> 'b) \<le> i \<Longrightarrow> enum_nth i = (enum_nth 0 :: 'a\<times>'b)\<close> for i
    by (auto simp: div_less_iff_less_mult enum_nth_prod_def)
  show \<open>enum_nth (enum_index a) = a\<close> for a :: \<open>'a\<times>'b\<close>
    apply (cases a)
    by (auto simp: div_less_iff_less_mult enum_nth_prod_def enum_index_prod_def)
  show \<open>enum_index a < CARD('a \<times> 'b)\<close> for a :: \<open>'a\<times>'b\<close>
    apply (cases a)
    apply (auto simp: enum_index_prod_def)
    by (metis (no_types, lifting) add_cancel_right_right div_less div_mult_self3 enum_index_bound less_eq_div_iff_mult_less_eq less_not_refl2 linorder_not_less zero_less_card_finite)
qed
end

lemma fst_enum_nth: \<open>fst (enum_nth ij :: 'a::eenum\<times>'b::eenum) = enum_nth (ij div CARD('b))\<close>
  by (auto simp: enum_nth_invalid enum_nth_prod_def Let_def)

lemma snd_enum_nth: \<open>snd (enum_nth ij :: 'a::eenum\<times>'b::eenum) = (if ij < CARD('a\<times>'b) then enum_nth (ij mod CARD('b)) else enum_nth 0)\<close>
  apply (auto simp: enum_nth_prod_def Let_def)
  using div_less_iff_less_mult zero_less_card_finite by blast+

lemma enum_index_fst: \<open>enum_index (fst x) = enum_index x div CARD('b)\<close> for x :: \<open>'a::eenum\<times>'b::eenum\<close>
  by (auto simp add: enum_index_prod_def case_prod_beta)
lemma enum_index_snd: \<open>enum_index (snd x) = enum_index x mod CARD('b)\<close> for x :: \<open>'a::eenum\<times>'b::eenum\<close>
  by (auto simp add: enum_index_prod_def case_prod_beta)

lemma enum_idx_enum_index[simp]: \<open>enum_idx = enum_index\<close>
proof (rule ext)
  fix x :: 'a
  have \<open>(Enum.enum ! enum_idx x :: 'a) = Enum.enum ! enum_index x\<close>
    unfolding enum_idx_correct
    by simp
  then show \<open>enum_idx x = enum_index x\<close>
    using enum_distinct apply (rule nth_eq_iff_index_eq[THEN iffD1, rotated -1])
    by (simp_all flip: card_UNIV_length_enum)
qed

lemma enum_nth_injective: \<open>i < CARD('a) \<Longrightarrow> j < CARD('a) \<Longrightarrow> (enum_nth i :: 'a::eenum) = enum_nth j \<longleftrightarrow> i = j\<close>
  by (metis enum_index_nth)

lemma Abs_ell2_inverse_finite[simp]: \<open>Rep_ell2 (Abs_ell2 \<psi>) = \<psi>\<close> for \<psi> :: \<open>_::finite \<Rightarrow> complex\<close>
  by (simp add: Abs_ell2_inverse)

lemma mat_of_cblinfun_explicit_cblinfun[code,simp]:
  fixes m :: \<open>'a::eenum \<Rightarrow> 'b::eenum \<Rightarrow> complex\<close>
  defines \<open>m' \<equiv> (\<lambda>(i,j). m (enum_nth i) (enum_nth j))\<close>
  shows \<open>mat_of_cblinfun (explicit_cblinfun m) = mat CARD('a) CARD('b) m'\<close> 
proof (rule eq_matI)
  fix i j
  assume \<open>i < dim_row (mat CARD('a) CARD('b) m')\<close> \<open>j < dim_col (mat CARD('a) CARD('b) m')\<close>
  then have ij[simp]: \<open>i < CARD('a)\<close> \<open>j < CARD('b)\<close>
    by auto
  have \<open>m (enum_class.enum ! i) (enum_class.enum ! j) = m' (i, j)\<close>
    by (auto simp: m'_def)
  then show \<open>mat_of_cblinfun (explicit_cblinfun m) $$ (i, j) = Matrix.mat CARD('a) CARD('b) m' $$ (i, j)\<close>
    by (simp add: mat_of_cblinfun_ell2_component)
next
  show \<open>dim_row (mat_of_cblinfun (explicit_cblinfun m)) = dim_row (Matrix.mat CARD('a) CARD('b) m')\<close> by simp
  show \<open>dim_col (mat_of_cblinfun (explicit_cblinfun m)) = dim_col (Matrix.mat CARD('a) CARD('b) m')\<close> by simp
qed

definition permute_and_tensor1_cblinfun where [code del]: \<open>permute_and_tensor1_cblinfun f R a =
  explicit_cblinfun (\<lambda>i j. if R i j then Rep_ell2 (a *\<^sub>V ket (f j)) (f i) else 0)\<close>

definition permute_and_tensor1_mat where \<open>permute_and_tensor1_mat d f R m =
  mat d d (\<lambda>(i,j). if R i j then m $$ (f i, f j) else 0)\<close>

definition permute_and_tensor1_mat' :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a::enum ell2)\<close> where 
 [code del]: \<open>permute_and_tensor1_mat' d f R m = cblinfun_of_mat (permute_and_tensor1_mat d f R m)\<close>

lemma permute_and_tensor1_cblinfun_code_prep[code]:
  fixes f :: \<open>'b::eenum \<Rightarrow> 'a::eenum\<close>
  shows \<open>permute_and_tensor1_cblinfun f R a = 
      permute_and_tensor1_mat' CARD('b) (\<lambda>i. enum_index (f (enum_nth i)))
      (\<lambda>i j. R (enum_nth i) (enum_nth j)) (mat_of_cblinfun a)\<close>
  apply (rule cblinfun_eq_mat_of_cblinfunI)
  apply (simp add: mat_of_cblinfun_explicit_cblinfun permute_and_tensor1_cblinfun_def
      permute_and_tensor1_mat_def permute_and_tensor1_mat'_def cblinfun_of_mat_inverse)
  apply (rule cong_mat, simp, simp)
  by (simp add: mat_of_cblinfun_ell2_component enum_idx_correct)



end