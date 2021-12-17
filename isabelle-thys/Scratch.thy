theory Scratch
  imports QRHL.QRHL Missing_Bounded_Operators
begin

no_notation m_inv ("inv\<index> _" [81] 80)
unbundle no_vec_syntax
unbundle jnf_notation
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Finite_Cartesian_Product.vec

derive (eq) ceq bit
derive (compare) ccompare bit
derive (dlist) set_impl bit

ML \<open>open Prog_Variables\<close>

class eenum = enum +
  fixes enum_nth :: \<open>nat \<Rightarrow> 'a\<close>
  fixes enum_index :: \<open>'a \<Rightarrow> nat\<close>
  assumes enum_nth_enum: \<open>\<And>i. i < CARD('a) \<Longrightarrow> enum_nth i = Enum.enum ! i\<close>
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

(* lemma enum_nth_injective[simp]: \<open>enum_nth x = enum_nth y \<longleftrightarrow> x = y\<close>
  sorry *)


instantiation bool :: eenum begin
definition \<open>enum_index_bool x = (if x then 1 else 0 :: nat)\<close>
definition \<open>enum_nth_bool (i::nat) = (i=1)\<close>
instance 
  apply standard
  apply (auto simp: enum_bool_def enum_index_bool_def enum_nth_bool_def)
  by (metis less_2_cases nth_Cons_0)
end

instantiation bit :: eenum begin
definition \<open>enum_index_bit (x::bit) = (if x=1 then 1 else 0 :: nat)\<close>
definition \<open>enum_nth_bit (i::nat) = (if i=1 then 1 else 0 :: bit)\<close>
instance
  apply standard
  by (auto simp: nth_Cons' enum_bit_def enum_index_bit_def enum_nth_bit_def)
end

instantiation prod :: (eenum,eenum) eenum begin
definition \<open>enum_index_prod = (\<lambda>(i::'a,j::'b). enum_index i * CARD('b) + enum_index j)\<close>
definition \<open>enum_nth_prod ij = (let i = ij div CARD('b) in if i < CARD('a) then (enum_nth i, enum_nth (ij mod CARD('b))) else (enum_nth 0, enum_nth 0) :: 'a\<times>'b)\<close>
(* definition \<open>enum_nth_prod ij = (enum_nth (ij div CARD('b)) :: 'a, enum_nth (ij mod CARD('b)) :: 'b)\<close> *)
instance
proof standard
  show \<open>i < CARD('a \<times> 'b) \<Longrightarrow> enum_nth i = (Enum.enum ! i :: 'a\<times>'b)\<close> for i
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
  apply (auto simp: enum_nth_prod_def Let_def)
  by (metis enum_nth_invalid linorder_not_less)

lemma snd_enum_nth: \<open>snd (enum_nth ij :: 'a::eenum\<times>'b::eenum) = (if ij < CARD('a\<times>'b) then enum_nth (ij mod CARD('b)) else enum_nth 0)\<close>
  apply (auto simp: enum_nth_prod_def Let_def)
  using div_less_iff_less_mult zero_less_card_finite by blast+

lemma enum_index_fst: \<open>enum_index (fst x) = enum_index x div CARD('b)\<close> for x :: \<open>'a::eenum\<times>'b::eenum\<close>
  by (auto simp add: enum_index_prod_def case_prod_beta)
lemma enum_index_snd: \<open>enum_index (snd x) = enum_index x mod CARD('b)\<close> for x :: \<open>'a::eenum\<times>'b::eenum\<close>
  by (auto simp add: enum_index_prod_def case_prod_beta)

lemma [simp]: \<open>enum_idx = enum_index\<close>
  sorry

lemma [simp]: \<open>(Enum.enum ! i :: 'a::eenum) = (if i < CARD('a) then enum_nth i else Enum.enum ! i)\<close>
  sorry

experiment
  fixes a b c :: \<open>bit qvariable\<close>
  assumes [variable]: \<open>qregister \<lbrakk>a,b,c\<rbrakk>\<close>
begin
ML \<open>
qregister_conversion_to_register_conv \<^context>
\<^cterm>\<open>\<lbrakk>a,\<lbrakk>\<rbrakk>,c \<mapsto> a,b,c,\<lbrakk>\<rbrakk>\<rbrakk>\<close>
\<close>
end

lemma apply_qregister_of_cregister:
  assumes \<open>cregister F\<close>
  shows \<open>apply_qregister (qregister_of_cregister F) a = 
          permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) a\<close>
  unfolding qregister_of_cregister.rep_eq using assms by simp

lemma apply_qregister_Fst[simp]: \<open>apply_qregister qFst x = x \<otimes> id_cblinfun\<close>
  sorry
lemma apply_qregister_Snd[simp]: \<open>apply_qregister qSnd x = id_cblinfun \<otimes> x\<close>
  sorry

lemma cregister_chain_is_cregister[simp]: \<open>cregister (cregister_chain F G) \<longleftrightarrow> cregister F \<and> cregister G\<close>
  by (metis Cccompatible_CREGISTER_of Cccompatible_comp_right ccompatible_CCcompatible cregister.rep_eq cregister_chain.rep_eq non_cregister_raw)


lemma qregister_chain_pair_Fst_chain[simp]:
  assumes \<open>qcompatible F G\<close>
  shows \<open>qregister_chain (qregister_pair F G) (qregister_chain qFst H) = qregister_chain F H\<close>
  by (metis qregister_chain_pair_Fst assms qregister_chain_assoc)

lemma qregister_chain_pair_Snd_chain[simp]:
  assumes \<open>qcompatible F G\<close>
  shows \<open>qregister_chain (qregister_pair F G) (qregister_chain qSnd H) = qregister_chain G H\<close>
  by (metis qregister_chain_pair_Snd assms qregister_chain_assoc)


lemma qregister_chain_unit_right[simp]: \<open>qregister F \<Longrightarrow> qregister_chain F qvariable_unit = qvariable_unit\<close>
  by (simp add: qvariable_unit_def)
lemma qregister_chain_unit_left[simp]: \<open>qregister F \<Longrightarrow> qregister_chain qvariable_unit F = qvariable_unit\<close>
  by (simp add: qvariable_unit_def)


(* TODO: move to bounded operators *)
lemma Abs_ell2_inverse_finite[simp]: \<open>Rep_ell2 (Abs_ell2 \<psi>) = \<psi>\<close> for \<psi> :: \<open>_::finite \<Rightarrow> complex\<close>
  by (simp add: Abs_ell2_inverse)

lemma explicit_cblinfun_Rep_ket: \<open>Rep_ell2 (explicit_cblinfun m *\<^sub>V ket a) b = m b a\<close> for m :: "_ :: finite \<Rightarrow> _ :: finite \<Rightarrow> _"
  by simp


lemma non_cregister'[simp]: \<open>\<not> cregister non_cregister\<close>
  by (simp add: non_cregister)

lemma qregister_of_cregister_non_register: \<open>qregister_of_cregister non_cregister = non_qregister\<close>
proof -
  define t where \<open>t = non_cregister\<close>
  show \<open>qregister_of_cregister t = non_qregister\<close>
    apply (transfer fixing: t)
    apply (simp add: t_def)
    using non_qregister_raw_def by fastforce
qed

lemma qregister_of_cregister_compatible: \<open>ccompatible x y \<longleftrightarrow> qcompatible (qregister_of_cregister x) (qregister_of_cregister y)\<close>
  sorry
lemma qregister_of_cregister_pair: \<open>qregister_of_cregister (cregister_pair x y) = qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)\<close>
  sorry
lemma qregister_of_cregister_chain: \<open>qregister_of_cregister (cregister_chain x y) = qregister_chain (qregister_of_cregister x) (qregister_of_cregister y)\<close>
  sorry


lemma getter_pair: 
  assumes \<open>cregister F\<close> \<open>cregister G\<close>
  shows \<open>getter (cregister_pair F G) = (\<lambda>m. (getter F m, getter G m))\<close>
  sorry

lemma setter_pair:
  assumes \<open>cregister F\<close> \<open>cregister G\<close>
  shows \<open>setter (cregister_pair F G) = (\<lambda>(x,y). setter F x o setter G y)\<close>
  sorry

lemma getter_chain:
  assumes \<open>cregister F\<close>
  shows \<open>getter (cregister_chain F G) = getter G o getter F\<close>
  sorry

lemma butterfly_tensor: \<open>butterfly (a \<otimes> b) (c \<otimes> d) = butterfly a c \<otimes> butterfly b d\<close>
  sorry

lemma clinear_tensorOp_left[simp]: \<open>clinear (\<lambda>x. x \<otimes> y)\<close> for y :: \<open>(_,_) cblinfun\<close>
  sorry

lemma clinear_tensorOp_right[simp]: \<open>clinear (\<lambda>y. x \<otimes> y)\<close> for x :: \<open>(_,_) cblinfun\<close>
  sorry

lemma bounded_clinear_apply_qregister[simp]: \<open>bounded_clinear (apply_qregister F)\<close>
  apply transfer
  apply (auto simp: non_qregister_raw_def[abs_def])
  sorry

lemma clinear_apply_qregister[simp]: \<open>clinear (apply_qregister F)\<close>
  using bounded_clinear.clinear bounded_clinear_apply_qregister by blast

(* lemma qregister_chain_pair:
  shows "qregister_pair (qregister_chain F G) (qregister_chain F H) = qregister_chain F (qregister_pair G H)"
  sorry *)

lemma rew1: \<open>qregister_le F G \<Longrightarrow> apply_qregister F x = apply_qregister G (apply_qregister (qregister_conversion F G) x)\<close>
  apply (subst qregister_chain_conversion[where F=F and G=G, symmetric])
  by auto

lemma lepairI: \<open>qregister_le F H \<Longrightarrow> qregister_le G H \<Longrightarrow> qcompatible F G \<Longrightarrow> qregister_le (qregister_pair F G) H\<close>
  unfolding qregister_le_def
  sorry

lemma lepairI1: \<open>qregister_le F G \<Longrightarrow> qcompatible G H \<Longrightarrow> qregister_le F (qregister_pair G H)\<close>
  sorry
lemma lepairI2: \<open>qregister_le F H \<Longrightarrow> qcompatible G H \<Longrightarrow> qregister_le F (qregister_pair G H)\<close>
  sorry
lemma lerefl: \<open>qregister F \<Longrightarrow> qregister_le F F\<close>
  unfolding qregister_le_def by simp

lemma qregister_conversion_chain: 
  assumes \<open>qregister_le F G\<close> \<open>qregister_le G H\<close>
  shows \<open>qregister_chain (qregister_conversion G H) (qregister_conversion F G) = qregister_conversion F H\<close>
  using assms unfolding qregister_le_def apply (transfer fixing: F G H) apply transfer
  by (auto intro!: ext qregister_conversion_raw_register simp: f_inv_into_f range_subsetD)

lemma tensor_ext2: 
  assumes \<open>\<And>x y. apply_qregister F (x\<otimes>y) = apply_qregister G (x\<otimes>y)\<close>
  shows \<open>F = G\<close>
  sorry

lemma tensor_ext3: 
  assumes \<open>\<And>x y z. apply_qregister F (x\<otimes>y\<otimes>z) = apply_qregister G (x\<otimes>y\<otimes>z)\<close>
  shows \<open>F = G\<close>
  sorry

lemma qcompatible_Abs_qregister[simp]:
  assumes \<open>qregister_raw F\<close> \<open>qregister_raw G\<close>
  (* assumes \<open>qcommuting_raw F G\<close> *)
  shows \<open>qcompatible (Abs_qregister F) (Abs_qregister G) \<longleftrightarrow> qcommuting_raw F G\<close>
  using assms by (simp add: eq_onp_same_args qcompatible.abs_eq qcompatible_raw_def qcommuting_raw_def)

lemma qcompatible_Abs_qregister_id_tensor_left[simp]:
  shows \<open>qcommuting_raw (\<lambda>x. id_cblinfun \<otimes> f x) (\<lambda>x. g x \<otimes> id_cblinfun)\<close>
  by (auto simp: qcommuting_raw_def)

lemma qcompatible_Abs_qregister_id_tensor_right[simp]:
  shows \<open>qcommuting_raw (\<lambda>x. g x \<otimes> id_cblinfun) (\<lambda>x. id_cblinfun \<otimes> f x)\<close>
  by (auto simp: qcommuting_raw_def)

lemma qcompatible_Abs_qregister_id_tensor_idid_tensor_left[simp]:
  shows \<open>qcommuting_raw (\<lambda>x. id_cblinfun \<otimes> f x) (\<lambda>x. id_cblinfun \<otimes> g x) \<longleftrightarrow> qcommuting_raw f g\<close>
  sorry

lemma qcompatible_Abs_qregister_id_tensor_idid_tensor_right[simp]:
  shows \<open>qcommuting_raw (\<lambda>x. f x \<otimes> id_cblinfun) (\<lambda>x. g x \<otimes> id_cblinfun) \<longleftrightarrow> qcommuting_raw f g\<close>
  sorry

lemma qregister_raw_tensor_left[simp]:
  shows \<open>qregister_raw (\<lambda>x. id_cblinfun \<otimes> F x) \<longleftrightarrow> qregister_raw F\<close>
  sorry

lemma qregister_raw_tensor_right[intro!, simp]:
  shows \<open>qregister_raw (\<lambda>x. F x \<otimes> id_cblinfun) \<longleftrightarrow> qregister_raw F\<close>
  sorry

lemma qregister_raw_id'[simp]: \<open>qregister_raw (\<lambda>x. x)\<close>
  by (metis eq_id_iff qregister_raw_id)

lemma permute_and_tensor1_cblinfun_ket[simp]: \<open>Rep_ell2 (permute_and_tensor1_cblinfun f R A *\<^sub>V ket a) b = 
  (if R b a then Rep_ell2 (A *\<^sub>V ket (f a)) (f b) else 0)\<close> for a b :: \<open>_::finite\<close>
  by (simp add: permute_and_tensor1_cblinfun_def)

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

definition permute_and_tensor1_mat where \<open>permute_and_tensor1_mat d f R m =
  mat d d (\<lambda>(i,j). if R i j then m $$ (f i, f j) else 0)\<close>

definition permute_and_tensor1_mat' :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a::enum ell2)\<close> where 
 (* [code del]: \<open>permute_and_tensor1_mat' f R m = cblinfun_of_mat (mat CARD('a) CARD('a) (\<lambda>(i,j). if R i j then m $$ (f i, f j) else 0))\<close> *)
 [code del]: \<open>permute_and_tensor1_mat' d f R m = cblinfun_of_mat (permute_and_tensor1_mat d f R m)\<close>

(* TODO move *)
lemma cblinfun_of_mat_invalid: 
  assumes \<open>M \<notin> carrier_mat (cdimension TYPE('b::{basis_enum,complex_normed_vector})) (cdimension TYPE('a::{basis_enum,complex_normed_vector}))\<close>
  shows \<open>(cblinfun_of_mat M :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = 0\<close>
  apply (transfer fixing: M)
  using assms by simp

(* lemma mat_of_cblinfun_permute_and_tensor1_mat'[code]:
  \<open>(permute_and_tensor1_mat' d f R m :: 'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) 
    = (if d=CARD('a) then cblinfun_of_mat (mat d d (\<lambda>(i,j). if R i j then m $$ (f i, f j) else 0)) else 0)\<close>
  apply (cases \<open>d = CARD('a)\<close>)
   apply (auto simp add: permute_and_tensor1_mat'_def cblinfun_of_mat_inverse permute_and_tensor1_mat_def)
  apply (subst cblinfun_of_mat_invalid)
  by (auto simp: mat_of_cblinfun_zero)
 *)

lemma mat_of_cblinfun_permute_and_tensor1_mat'[code]:
  \<open>mat_of_cblinfun (permute_and_tensor1_mat' d f R m :: 'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) 
    = (if d=CARD('a) then mat d d (\<lambda>(i,j). if R i j then m $$ (f i, f j) else 0) else zero_mat CARD('a) CARD('a))\<close>
  apply (cases \<open>d = CARD('a)\<close>)
   apply (auto simp add: permute_and_tensor1_mat'_def cblinfun_of_mat_inverse permute_and_tensor1_mat_def)
  apply (subst cblinfun_of_mat_invalid)
  by (auto simp: mat_of_cblinfun_zero)

lemma mat_of_cblinfun_permute_and_tensor1_cblinfun[code]:
  fixes f :: \<open>'b::eenum \<Rightarrow> 'a::eenum\<close>
  shows \<open>mat_of_cblinfun (permute_and_tensor1_cblinfun f R a) = 
      permute_and_tensor1_mat CARD('b) (\<lambda>i. enum_index (f (enum_nth i)))
      (\<lambda>i j. R (enum_nth i) (enum_nth j)) (mat_of_cblinfun a)\<close>
  apply (simp add: mat_of_cblinfun_explicit_cblinfun permute_and_tensor1_cblinfun_def
      permute_and_tensor1_mat_def cblinfun_of_mat_inverse)
  apply (rule cong_mat, simp, simp)
  by (simp add: mat_of_cblinfun_ell2_component enum_idx_correct)

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

(* definition \<open>cblinfun_of_mat' = cblinfun_of_mat\<close>
lemma [code]: \<open>mat_of_cblinfun (cblinfun_of_mat' x :: 'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'b::{basis_enum,complex_normed_vector})
   = (if x \<in> carrier_mat (cdimension TYPE('a)) (cdimension TYPE('b)) (length (canonical_basis :: 'b list)) then x else zero_mat CARD('a) CARD('b))\<close>
  unfolding cblinfun_of_mat'_def
  apply (subst cblinfun_of_mat_inverse)
  apply (auto simp flip: canonical_basis_length_ell2)
  
  by auto *)

(* lemma permute_and_tensor1_cblinfun_prep_code:
  fixes f :: \<open>'b::eenum \<Rightarrow> 'a::eenum\<close>
  shows \<open>permute_and_tensor1_cblinfun f R a = 
      cblinfun_of_mat' (permute_and_tensor1_mat CARD('b) (\<lambda>i. enum_index (f (enum_nth i)))
      (\<lambda>i j. R (enum_nth i) (enum_nth j)) (mat_of_cblinfun a))\<close>
  by (metis cblinfun_of_mat'_def mat_of_cblinfun_inverse mat_of_cblinfun_permute_and_tensor1_cblinfun) *)

(* definition reorder_cblinfun :: \<open>('d \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> ('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2)\<close> where
  \<open>reorder_cblinfun r c A = explicit_cblinfun (\<lambda>i j. Rep_ell2 (A *\<^sub>V ket (c j)) (r i))\<close>

abbreviation "reorder_cblinfun2 f \<equiv> reorder_cblinfun f f"

lemma reorder_cblinfun_ket[simp]: \<open>Rep_ell2 (reorder_cblinfun r c A *\<^sub>V ket a) b = Rep_ell2 (A *\<^sub>V ket (c a)) (r b)\<close> for a b :: \<open>_::finite\<close>
  by (simp add: reorder_cblinfun_def) *)

lemma clinear_permute_and_tensor1_cblinfun[simp]: \<open>clinear (permute_and_tensor1_cblinfun r c)\<close> for r c :: \<open>_::finite \<Rightarrow> _\<close>
proof (rule clinearI)
  show \<open>permute_and_tensor1_cblinfun r c (A + B) = permute_and_tensor1_cblinfun r c A + permute_and_tensor1_cblinfun r c B\<close> for A B
    apply (rule equal_ket)
    by (auto simp: plus_ell2.rep_eq cblinfun.add_left simp flip: Rep_ell2_inject)
  show \<open>permute_and_tensor1_cblinfun r c (s *\<^sub>C A) = s *\<^sub>C permute_and_tensor1_cblinfun r c A\<close> for s A
    apply (rule equal_ket)
    by (auto simp: scaleC_ell2.rep_eq simp flip: Rep_ell2_inject)
qed

(* lemma clinear_reorder_cblinfun[simp]: \<open>clinear (reorder_cblinfun r c)\<close> for r c :: \<open>_::finite \<Rightarrow> _\<close>
proof (rule clinearI)
  show \<open>reorder_cblinfun r c (A + B) = reorder_cblinfun r c A + reorder_cblinfun r c B\<close> for A B
    apply (rule equal_ket)
    by (auto simp: plus_ell2.rep_eq cblinfun.add_left simp flip: Rep_ell2_inject)
  show \<open>reorder_cblinfun r c (s *\<^sub>C A) = s *\<^sub>C reorder_cblinfun r c A\<close> for s A
    apply (rule equal_ket)
    by (auto simp: scaleC_ell2.rep_eq simp flip: Rep_ell2_inject)
qed *)

lemma permute_and_tensor1_cblinfun_butterfly: 
  fixes f :: \<open>_::finite \<Rightarrow> _::finite\<close>
  assumes [simp]: \<open>bij f\<close> \<open>\<And>x y. R x y\<close>
  shows \<open>permute_and_tensor1_cblinfun f R (butterket a b) = butterket (inv f a) (inv f b)\<close>
proof (rule equal_ket, rule Rep_ell2_inject[THEN iffD1], rule ext)
  fix i j
  have \<open>Rep_ell2 (permute_and_tensor1_cblinfun f R (butterket a b) \<cdot> ket i) j = 
          Rep_ell2 ((ket b \<bullet>\<^sub>C ket (f i)) *\<^sub>C ket a) (f j)\<close>
    by auto
  also have \<open>\<dots> = (if b=f i then 1 else 0) * (if a=f j then 1 else 0)\<close>
    by (auto simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = (if inv f b=i then 1 else 0) * (if inv f a=j then 1 else 0)\<close>
    by (smt (verit, del_insts) assms(1) assms(2) bij_inv_eq_iff)
  also have \<open>\<dots> = Rep_ell2 ((ket (inv f b) \<bullet>\<^sub>C ket i) *\<^sub>C ket (inv f a)) j\<close>
    by (simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = Rep_ell2 (butterket (inv f a) (inv f b) \<cdot> ket i) j\<close>
    by auto
  finally show \<open>Rep_ell2 (permute_and_tensor1_cblinfun f R (butterket a b) \<cdot> ket i) j
                   = Rep_ell2 (butterket (inv f a) (inv f b) \<cdot> ket i) j\<close>
    by -
qed

(* lemma reorder_cblinfun_butterfly: 
  fixes r c :: \<open>_::finite \<Rightarrow> _::finite\<close>
  assumes \<open>bij r\<close> \<open>bij c\<close>
  shows \<open>reorder_cblinfun r c (butterket a b) = butterket (inv r a) (inv c b)\<close>
proof (rule equal_ket, rule Rep_ell2_inject[THEN iffD1], rule ext)
  fix i j
  have \<open>Rep_ell2 (reorder_cblinfun r c (butterket a b) \<cdot> ket i) j = Rep_ell2 ((ket b \<bullet>\<^sub>C ket (c i)) *\<^sub>C ket a) (r j)\<close>
    by auto
  also have \<open>\<dots> = (if b=c i then 1 else 0) * (if a=r j then 1 else 0)\<close>
    by (simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = (if inv c b=i then 1 else 0) * (if inv r a=j then 1 else 0)\<close>
    by (smt (verit, del_insts) assms(1) assms(2) bij_inv_eq_iff)
  also have \<open>\<dots> = Rep_ell2 ((ket (inv c b) \<bullet>\<^sub>C ket i) *\<^sub>C ket (inv r a)) j\<close>
    by (simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = Rep_ell2 (butterket (inv r a) (inv c b) \<cdot> ket i) j\<close>
    by auto
  finally show \<open>Rep_ell2 (reorder_cblinfun r c (butterket a b) \<cdot> ket i) j = Rep_ell2 (butterket (inv r a) (inv c b) \<cdot> ket i) j\<close>
    by -
qed

lemma reorder_cblinfun2_butterfly: 
  fixes f :: \<open>_::finite \<Rightarrow> _::finite\<close>
  assumes \<open>bij f\<close>
  shows \<open>reorder_cblinfun2 f (butterket a b) = butterket (inv f a) (inv f b)\<close>
  by (simp add: assms reorder_cblinfun_butterfly) *)

(* definition reorder_mat :: \<open>nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex mat \<Rightarrow> complex mat\<close> where 
  \<open>reorder_mat n m r c A = Matrix.mat n m (\<lambda>(i, j). A $$ (r i, c j))\<close> *)

(* TODO: to bounded operators *)
declare enum_idx_correct[simp]

(* lemma mat_of_cblinfun_reorder[code]: 
  fixes r :: \<open>'a::enum \<Rightarrow> 'c::enum\<close> and c :: \<open>'b::enum \<Rightarrow> 'd::enum\<close>
  shows \<open>mat_of_cblinfun (reorder_cblinfun r c A) = reorder_mat CARD('a) CARD('b)
(\<lambda>i. enum_idx (r (enum_class.enum ! i))) (\<lambda>j. enum_idx (c (enum_class.enum ! j))) (mat_of_cblinfun A)\<close>
proof -
  have aux: \<open>Rep_ell2 \<psi> i = vec_of_basis_enum \<psi> $ (enum_idx i)\<close> if \<open>enum_idx i < CARD('z)\<close> 
    for \<psi> :: \<open>'z::enum ell2\<close> and i
    apply (subst vec_of_basis_enum_ell2_component)
    using that by auto

  show ?thesis
    apply (subst reorder_cblinfun_def)
    apply (subst mat_of_cblinfun_explicit_cblinfun)
    apply (subst aux)
     apply (simp add: card_UNIV_length_enum enum_idx_bound)
    apply (subst mat_of_cblinfun_cblinfun_apply)
    apply (subst vec_of_basis_enum_ket)
    apply (subst mat_entry_explicit)
    by (auto simp add: card_UNIV_length_enum enum_idx_bound reorder_mat_def)
qed *)

lemma enum_idx_correct': \<open>enum_idx (enum_class.enum ! i :: 'a::enum) = i\<close> if \<open>i < CARD('a)\<close>
  sorry

(* definition \<open>enum_idx_enum_nth_code n (_::'a::enum itself) i = (if i < n then i else 
    Code.abort STR ''enum_idx_enum_nth_code: index out of bounds'' (\<lambda>_. enum_idx (enum_class.enum ! i :: 'a)))\<close>

lemma enum_idx_enum_nth_code: \<open>enum_idx (enum_class.enum ! i :: 'a::enum) = enum_idx_enum_nth_code CARD('a) TYPE('a) i\<close>
  unfolding enum_idx_enum_nth_code_def
  apply (cases \<open>i < CARD('a)\<close>)
   apply (subst enum_idx_correct', simp, simp)
  by auto

lemma enum_idx_pair: \<open>enum_idx (a,b) = enum_idx a * CARD('b) + enum_idx b\<close> for a :: \<open>'a::enum\<close> and b :: \<open>'b::enum\<close>
proof -
  let ?enumab = \<open>Enum.enum :: ('a \<times> 'b) list\<close>
  let ?enuma = \<open>Enum.enum :: 'a list\<close>
  let ?enumb = \<open>Enum.enum :: 'b list\<close>
  have bound: \<open>i < CARD('a) \<Longrightarrow> j < CARD('b) \<Longrightarrow> i * CARD('b) + j < CARD('a) * CARD('b)\<close> for i j
    sorry
  have *: \<open>?enumab ! (i * CARD('b) + j) = (?enuma ! i, ?enumb ! j)\<close> 
    if \<open>i < CARD('a)\<close> \<open>j < CARD('b)\<close> for i j
    unfolding enum_prod_def 
    apply (subst List.product_nth)
    using that bound by (auto simp flip: card_UNIV_length_enum)
  note ** = *[where i=\<open>enum_idx a\<close> and j=\<open>enum_idx b\<close>, simplified, symmetric]
  show ?thesis
    apply (subst ** )
    using enum_idx_bound[of a] enum_idx_bound[of b]
    by (auto simp: bound enum_idx_correct' simp flip: card_UNIV_length_enum)
qed

lemma enum_idx_fst: \<open>enum_idx (fst ab) = enum_idx ab div CARD('b)\<close> for ab :: \<open>'a::enum \<times> 'b::enum\<close>
  apply (cases ab, hypsubst_thin)
  apply (subst enum_idx_pair)
  using enum_idx_bound
  by (auto intro!: div_less simp flip: card_UNIV_length_enum)

lemma enum_idx_snd: \<open>enum_idx (snd ab) = enum_idx ab mod CARD('b)\<close> for ab :: \<open>'a::enum \<times> 'b::enum\<close>
  apply (cases ab, hypsubst_thin)
  apply (subst enum_idx_pair)
  using enum_idx_bound
  by (auto intro!: mod_less[symmetric] simp flip: card_UNIV_length_enum)
 *)

lemma prod_eqI': \<open>x = fst z \<Longrightarrow> y = snd z \<Longrightarrow> (x,y) = z\<close>
  by auto

lemma [code]: \<open>vec_of_ell2 (Abs_ell2 f) = vec CARD('a) (\<lambda>n. f (enum_nth n))\<close> for f :: \<open>'a::eenum \<Rightarrow> complex\<close>
  by (auto simp: vec_of_ell2_def vec_eq_iff vec_of_basis_enum_ell2_component)

lemma [code]: \<open>Rep_ell2 \<psi> i = vec_of_ell2 \<psi> $ (enum_index i)\<close> for i :: \<open>'a::eenum\<close>
  by (auto simp: vec_of_ell2_def vec_eq_iff vec_of_basis_enum_ell2_component)

(* experiment fixes a :: \<open>bool qvariable\<close> and b :: \<open>bit qvariable\<close> and c :: \<open>3 qvariable\<close> and d :: \<open>3 qvariable\<close>
  assumes xxx[variable]: \<open>qregister \<lbrakk>a,b,c,d\<rbrakk>\<close> begin
 *)

thm if_distrib[of fst]

lemma permute_and_tensor1_mat_cong[cong]: 
  assumes \<open>d = d'\<close>
  assumes \<open>\<And>i. i < d' \<Longrightarrow> f i = f' i\<close>
  assumes \<open>\<And>i j. i < d' \<Longrightarrow> j < d' \<Longrightarrow> R i j = R' i j\<close>
  assumes \<open>m = m'\<close>
  shows \<open>(permute_and_tensor1_mat' d f R m :: 'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) = permute_and_tensor1_mat' d' f' R' m'\<close>
  unfolding permute_and_tensor1_mat_def permute_and_tensor1_mat'_def 
  apply (rule arg_cong[of _ _ cblinfun_of_mat])
  apply (rule cong_mat)
  using assms by auto

lemma enum_nth_injective: \<open>i < CARD('a) \<Longrightarrow> j < CARD('a) \<Longrightarrow> (enum_nth i :: 'a::eenum) = enum_nth j \<longleftrightarrow> i = j\<close>
  by (metis enum_index_nth)

lemma div_leq_simp: \<open>(i div n < m) \<longleftrightarrow> i < n*m\<close> if \<open>n \<noteq> 0\<close> for n m :: nat
  by (simp add: div_less_iff_less_mult ordered_field_class.sign_simps(5) that zero_less_iff_neq_zero)

lemmas prepare_for_code_new =

  qregister_of_cregister_Fst[symmetric] qregister_of_cregister_Snd[symmetric]
  qregister_of_cregister_pair[symmetric] qregister_of_cregister_chain[symmetric]
  apply_qregister_of_cregister permute_and_tensor1_cblinfun_code_prep
  same_outside_cregister_def
  
  case_prod_beta if_distrib[of fst] if_distrib[of snd] prod_eq_iff

  div_leq_simp mod_mod_cancel

  getter_pair getter_chain setter_chain setter_pair setter_Fst setter_Snd

  enum_index_prod_def fst_enum_nth snd_enum_nth enum_index_nth if_distrib[of enum_index]
  enum_nth_injective


lemmas prepare_for_code_remove =
  qregister_of_cregister_Fst qregister_of_cregister_Snd
  qregister_of_cregister_pair qregister_of_cregister_chain

lemma Test
proof -
  fix a b c

  have t[variable]: \<open>qregister (\<lbrakk>a,b,c\<rbrakk> :: (bit*bit*bit) qvariable)\<close> sorry

  have le: \<open>\<lbrakk>a,c \<le> a,b,c\<rbrakk>\<close>
    by (auto intro!: lepairI lerefl simp: lepairI1 lepairI2 lepairI lerefl)

  define CNOT' where \<open>CNOT' = apply_qregister \<lbrakk>a,c \<mapsto> a,b,c\<rbrakk> CNOT\<close>

  have \<open>apply_qregister \<lbrakk>a,c\<rbrakk> CNOT = apply_qregister \<lbrakk>a,b,c\<rbrakk> CNOT'\<close>
    apply (subst rew1[where G=\<open>\<lbrakk>a,b,c\<rbrakk>\<close>])
     apply (fact le)
    by (simp add: CNOT'_def)

  have \<open>CNOT' *\<^sub>V ket (1,1,1) = (ket (1,1,0) :: (bit*bit*bit) ell2)\<close>
    unfolding CNOT'_def
    using if_weak_cong[cong del] apply fail?

    using [[show_consts]]
    apply (simp 
      del: prepare_for_code_remove
      add: prepare_for_code_new
      )

    by normalization


  oops
