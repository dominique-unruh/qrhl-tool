(* 

This file contains some legacy fixes for making qrhl-tool compatible
with current version of Tensor_Product and Bounded_Operators. Should
be removed eventually.

*)

theory BOLegacy
  imports 

    (* This should not be imported here, but in QRHL_Code. But if we import it there, 
       we run into this bug: 
       https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2019-June/msg00063.html *)
    Hilbert_Space_Tensor_Product.Tensor_Product_Code

    Complex_Bounded_Operators.Complex_L2 Hilbert_Space_Tensor_Product.Hilbert_Space_Tensor_Product

    Registers.Quantum (* Imported because otherwise instantiations in QRHL_Code for bit will happen that make it impossible to merge Registers.Quantum with that theory.
And we include it already here so that out simpset removals here won't be overwritten in a merge *)

    Extended_Sorry
begin

(* Hiding constants/syntax that were overwritten by Jordan_Normal_Form *)
hide_const (open) Lattice.sup
hide_const (open) Lattice.inf
hide_const (open) Order.top
hide_const (open) card_UNIV
hide_const (open) Real_Vector_Spaces.span
no_notation "Order.bottom" ("\<bottom>\<index>")
no_notation "Order.top" ("\<top>\<index>")
no_notation "Lattice.meet" (infixl "\<sqinter>\<index>" 70)
no_notation "Lattice.join" (infixl "\<squnion>\<index>" 65)
hide_const (open) Order.bottom Order.top
hide_const (open) Quantum.hadamard
hide_const (open) Quantum.CNOT
hide_const (open) Quantum.pauliX
hide_const (open) Quantum.pauliZ

syntax (output) "_forced_parentheses" :: \<open>'a \<Rightarrow> 'a\<close> ("'(_')")

unbundle lattice_syntax
unbundle cblinfun_syntax

(* Needed to make the terms below print with parentheses. If not, the result of printing cannot be parsed back. *)
translations "A *\<^sub>S _forced_parentheses (B \<sqinter> C)" \<leftharpoondown> "A *\<^sub>S (B \<sqinter> C)"
translations "_forced_parentheses (A *\<^sub>S B) \<sqinter> C" \<leftharpoondown> "(A *\<^sub>S B) \<sqinter> C"
term \<open>A *\<^sub>S (B \<sqinter> C)\<close>
term \<open>(A *\<^sub>S B) \<sqinter> C\<close>

lemma inf_assoc_subspace[simp]: "A \<sqinter> B \<sqinter> C = A \<sqinter> (B \<sqinter> C)" 
  for A B C :: "_ ell2 ccsubspace"
  by (fact inf.assoc)

lemma inf_left_commute[simp]: "A \<sqinter> (B \<sqinter> C) = B \<sqinter> (A \<sqinter> C)" for A B C :: "_ ell2 ccsubspace"
  using inf.left_commute by auto

declare tensor_ell2_ket[simp del]

notation tensor_ell2 (infixr "\<otimes>\<^sub>l" 70)

type_synonym ('a,'b) bounded = "('a,'b) cblinfun"
type_synonym ('a,'b) l2bounded = "('a ell2, 'b ell2) bounded"
type_synonym 'a subspace = "'a ell2 ccsubspace"

abbreviation "ell2_to_bounded :: 'a::chilbert_space \<Rightarrow> ('b::{CARD_1,enum} ell2,'a) bounded
    == vector_to_cblinfun"
abbreviation "complex_to_C1 :: complex \<Rightarrow> 'a::{CARD_1,enum} ell2 == of_complex"
abbreviation "C1_to_complex == (one_dim_iso :: _ \<Rightarrow> complex)"

abbreviation (input) "applyOp == cblinfun_apply"
abbreviation (input) "applyOpSpace == cblinfun_image"
abbreviation (input) "timesOp == cblinfun_compose"

consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)

adhoc_overloading
  cdot \<rightleftharpoons> "\<lambda>x. timesOp x" "\<lambda>x. cblinfun_apply x" "\<lambda>x. applyOpSpace x"

lemma equal_span':
  fixes f g :: "'a::cbanach \<Rightarrow> 'b::cbanach"
  assumes "bounded_clinear f"
    and "bounded_clinear g"
  assumes "\<And>x. x\<in>G \<Longrightarrow> f x = g x"
  assumes "x\<in>closure (cspan G)"
  shows "f x = g x"
  using assms by (rule bounded_clinear_eq_on_closure)

(* TODO remove (seems to be a [simp] rule already) *)
lemma bot_plus[simp]: "sup bot x = x" 
  for x :: "'a::complex_normed_vector ccsubspace"
  by simp

abbreviation (input) \<open>idOp \<equiv> id_cblinfun\<close>

(* declare cblinfun.scaleC_left[simp] *)
(* declare cblinfun.scaleC_right[simp] *)

(* Giving it a name to make adding/removing [simp] easier *)
lemmas le_Inf_iff_subspace[simp] = le_Inf_iff[where 'a=\<open>_::chilbert_space ccsubspace\<close>]

type_synonym 'a clinear_space = \<open>'a ccsubspace\<close>

abbreviation (input) \<open>isProjector \<equiv> is_Proj\<close>

notation ket ("|_\<rangle>")

lemma Proj_on_image [simp]: \<open>Proj S *\<^sub>S S = S\<close>
  by (metis Proj_idempotent Proj_range cblinfun_compose_image)

lemma proj_ket_is_0[simp]: \<open>proj (ket x) *\<^sub>S ccspan {ket y} = 0\<close> if \<open>x \<noteq> y\<close>
  by (cheat proj_ket_is_0)

abbreviation \<open>comm_op \<equiv> swap_ell2\<close>
definition \<open>assoc_op = assoc_ell2*\<close>

lemma unitary_assoc_op[iff]: \<open>unitary assoc_op\<close>
  by (simp add: assoc_op_def)

definition remove_qvar_unit_op :: "(('a*unit) ell2,'a ell2) cblinfun" where
  \<open>remove_qvar_unit_op = (tensor_ell2_right 1)*\<close>

abbreviation \<open>addState \<equiv> tensor_ell2_right\<close>


lemma basis_enum_of_vec_tensor_ell2:
  \<open>(basis_enum_of_vec x :: 'a ell2) \<otimes>\<^sub>l (basis_enum_of_vec y :: 'b ell2) = basis_enum_of_vec (tensor_state_jnf x y)\<close>
  if \<open>dim_vec x = CARD('a::enum)\<close> and \<open>dim_vec y = CARD('b::enum)\<close> for x y
  using that
  by (metis (full_types) basis_enum_of_vec_inverse canonical_basis_length_ell2
      vec_of_basis_enum_inverse vec_of_basis_enum_tensor_state)


lemma tensor_ccsubspace_code[code]:
 "tensor_ccsubspace (SPAN A :: 'a::enum ell2 ccsubspace) (SPAN B :: 'b::enum ell2 ccsubspace)
    = SPAN [tensor_state_jnf a b. a<-filter (\<lambda>v. dim_vec v = CARD('a)) A, b<-filter (\<lambda>v. dim_vec v = CARD('b)) B]"
proof -
  define AA BB where \<open>AA = filter (\<lambda>v. dim_vec v = CARD('a)) A\<close> and \<open>BB = filter (\<lambda>v. dim_vec v = CARD('b)) B\<close>

  have \<open>tensor_ccsubspace (SPAN A :: 'a::enum ell2 ccsubspace) (SPAN B :: 'b::enum ell2 ccsubspace)
    = ccspan (basis_enum_of_vec ` set AA) \<otimes>\<^sub>S ccspan (basis_enum_of_vec ` set BB)\<close>
    by (simp add: SPAN_def AA_def BB_def filter_set)
  also have \<open>\<dots> = ccspan {x \<otimes>\<^sub>l y |x y. x \<in> basis_enum_of_vec ` set AA \<and> y \<in> basis_enum_of_vec ` set BB}\<close>
    by (simp add: tensor_ccsubspace_ccspan)
  also have \<open>\<dots> = ccspan {basis_enum_of_vec x \<otimes>\<^sub>l basis_enum_of_vec y |x y. x \<in> set AA \<and> y \<in> set BB}\<close>
    apply (rule arg_cong[where f=ccspan])
    by blast
  also have \<open>\<dots> = ccspan {basis_enum_of_vec (tensor_state_jnf x y) |x y. x \<in> set AA \<and> y \<in> set BB}\<close>
    apply (rule arg_cong[where f=ccspan])
    using basis_enum_of_vec_tensor_ell2
    by (force intro!: simp: AA_def BB_def)
  also have \<open>\<dots> = ccspan (basis_enum_of_vec ` (\<Union>x\<in>set AA. tensor_state_jnf x ` set BB))\<close>
    apply (rule arg_cong[where f=ccspan])
    by auto
  also have \<open>\<dots> = ccspan (basis_enum_of_vec `
      Set.filter (\<lambda>v. dim_vec v = CARD('a) * CARD('b)) (\<Union>x\<in>set AA. tensor_state_jnf x ` set BB))\<close>
    by (auto intro!: arg_cong[where f=ccspan] arg_cong[where f=\<open>image _\<close>] Set_filter_unchanged[symmetric] simp: AA_def BB_def)
  also have \<open>\<dots> = SPAN [tensor_state_jnf a b. a<-AA, b<-BB]\<close>
    by (simp add: SPAN_def)
  finally show ?thesis
    by (simp add: AA_def BB_def)
qed


lemma mat_of_cblinfun_tensor_ell2_right_index:
  includes jnf_syntax and no vec_syntax
  fixes \<psi> :: \<open>'a::enum ell2\<close>
  assumes [simp]: \<open>i < CARD('b) * CARD('a)\<close>
  assumes [simp]: \<open>j < CARD('b)\<close>
  shows \<open>mat_of_cblinfun (tensor_ell2_right \<psi> :: ('b::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L _)) $$ (i,j) = 
            (let (i1,i2) = tensor_unpack CARD('b) CARD('a) i in
                  of_bool (i1=j) * vec_of_basis_enum \<psi> $ i2)\<close>
proof -
  define i1 i2
    where "i1 = fst (tensor_unpack CARD('b) CARD('a) i)"
      and "i2 = snd (tensor_unpack CARD('b) CARD('a) i)"
  have [simp]: "i1 < CARD('b)" "i2 < CARD('a)" 
    using assms i1_def tensor_unpack_bound1 apply presburger
    using assms i2_def tensor_unpack_bound2 by blast

  have \<open>mat_of_cblinfun (tensor_ell2_right \<psi> :: ('b::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L _)) $$ (i,j) 
       = Rep_ell2 ((tensor_ell2_right \<psi> :: ('b::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L _)) *\<^sub>V ket (Enum.enum!j)) (Enum.enum ! i)\<close>
    by (simp add: mat_of_cblinfun_ell2_component)
  also have \<open>\<dots> = Rep_ell2 (ket(enum_class.enum ! j :: 'b) \<otimes>\<^sub>l \<psi>) (enum_class.enum ! i1, enum_class.enum ! i2)\<close>
    by (simp add: tensor_op_ell2 enum_prod_nth_tensor_unpack[where i=i] Let_def case_prod_beta flip: tensor_ell2_ket i1_def i2_def)
  also have \<open>\<dots> = of_bool ((enum_class.enum ! i1 :: 'b) = enum_class.enum ! j) * (ket (enum_class.enum ! i2) \<bullet>\<^sub>C \<psi>)\<close>
    by (simp add: cinner_ket flip: cinner_ket_left tensor_ell2_ket)
  also have \<open>\<dots> = of_bool (i1 = j) * (ket (enum_class.enum ! i2) \<bullet>\<^sub>C \<psi>)\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>x. of_bool x * _\<close>])
    apply (rule enum_inj)
    by simp_all
  also have \<open>\<dots> = of_bool (i1=j) * vec_of_basis_enum \<psi> $ i2\<close>
    by (simp add: vec_of_basis_enum_ell2_component cinner_ket_left)
  finally show ?thesis
    by (simp add: Let_def i1_def i2_def split!: prod.split)
qed

lemma mat_of_cblinfun_tensor_ell2_right[code]:
  includes jnf_syntax and no vec_syntax
  fixes \<psi> :: \<open>'a::enum ell2\<close>
  shows \<open>mat_of_cblinfun (tensor_ell2_right \<psi> :: ('b::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L _)) = 
           tensor_op_jnf (1\<^sub>m CARD('b)) (mat_of_cols (CARD('a)) [vec_of_ell2 \<psi>])\<close>
    (is \<open>?lhs = ?rhs\<close>)
proof (rule eq_matI, simp_all add: canonical_basis_length)
  fix i j assume i_leq: \<open>i < CARD('b) * CARD('a)\<close> and j_leq: \<open>j < CARD('b)\<close>
  define i1 i2
    where "i1 = fst (tensor_unpack CARD('b) CARD('a) i)"
      and "i2 = snd (tensor_unpack CARD('b) CARD('a) i)"
  then have [simp]: \<open>tensor_unpack CARD('b) CARD('a) i = (i1,i2)\<close>
    by force
  have [simp]: \<open>tensor_unpack CARD('b) (Suc 0) j = (j,0)\<close>
    by (simp add: tensor_unpack_def)

  have i1_leq: "i1 < CARD('b)" and i2_leq: "i2 < CARD('a)" 
    using i_leq i1_def tensor_unpack_bound1 apply presburger
    using i_leq i2_def tensor_unpack_bound2 by blast

  have \<open>?lhs $$ (i, j) = of_bool (i1 = j) * vec_of_ell2 \<psi> $ i2\<close>
    apply (subst mat_of_cblinfun_tensor_ell2_right_index)
    by (simp_all add: i_leq j_leq vec_of_ell2_def)
  also have \<open>\<dots> = of_bool (i1=j) * mat_of_cols CARD('a) [vec_of_ell2 \<psi>] $$ (i2, 0)\<close>
    by (simp add: i2_leq mat_of_cols_Cons_index_0)
  also have \<open>\<dots> = 1\<^sub>m CARD('b) $$ (i1, j) * mat_of_cols CARD('a) [vec_of_ell2 \<psi>] $$ (i2, 0)\<close>
    by (simp add: index_one_mat i1_leq j_leq)
  also have \<open>\<dots> = ?rhs $$ (i, j)\<close>
    by (simp add: tensor_op_jnf_def case_prod_beta Let_def canonical_basis_length i_leq j_leq)
  finally show \<open>?lhs $$ (i,j) = ?rhs $$ (i,j)\<close>
    by -
qed

lemma conjugate_1[simp]: \<open>conjugate (1 :: 'a :: conjugatable_field) = 1\<close>
  by (metis conjugate_dist_mul conjugate_id mult.commute verit_prod_simplify(1))

lemma tensor_op_jnf_id_right[simp]: \<open>tensor_op_jnf a (1\<^sub>m 1 :: 'a::{monoid_mult,zero} mat) = a\<close>
  by (auto simp: tensor_op_jnf_def tensor_unpack_def)

lemma mat_adjoint_one[simp]: \<open>mat_adjoint (1\<^sub>m n) = 1\<^sub>m n\<close>
    apply (rule eq_matI)
  by (auto intro!: simp: mat_adjoint_def mat_of_cols_Cons_index_0 mat_of_rows_index)

declare mat_of_cblinfun_tensor_op[code]


lemma remove_qvar_unit_op_code[code]: \<open>mat_of_cblinfun (remove_qvar_unit_op :: (_ \<Rightarrow>\<^sub>C\<^sub>L 'a::enum ell2)) = 1\<^sub>m (CARD('a))\<close>
proof -
  have *: \<open>mat_of_cols 1 [vec_of_basis_enum (1::unit ell2)] = 1\<^sub>m 1\<close>
    apply (rule eq_matI)
    by (auto intro!: simp: vec_of_basis_enum_1 mat_of_cols_Cons_index_0)
  have \<open>mat_of_cblinfun (remove_qvar_unit_op :: (_ \<Rightarrow>\<^sub>C\<^sub>L 'a::enum ell2))
    = mat_adjoint (tensor_op_jnf (1\<^sub>m CARD('a)) (1\<^sub>m 1))\<close>
    using * by (simp add: remove_qvar_unit_op_def mat_of_cblinfun_adj mat_of_cblinfun_tensor_ell2_right vec_of_ell2_def)
  also have \<open>\<dots> = mat_adjoint (1\<^sub>m CARD('a))\<close>
    apply (subst tensor_op_jnf_id_right)
    by simp
  also have \<open>\<dots> = 1\<^sub>m CARD('a)\<close>
    by simp
  finally show ?thesis
    by -
qed

(* Something is broken which gets fixed by this. Check occasionally whether Teleport.thy works if this line is removed. If so, this line can be removed again. *)
declare finite'_code[code del]

declare tensor_op_adjoint[simp]

end
