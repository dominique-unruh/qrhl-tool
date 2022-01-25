(* 

This file contains some legacy fixes for making qrhl-tool compatible
with current version of Tensor_Product and Bounded_Operators. Should
be removed eventually.

*)

theory BOLegacy
  imports 

    Complex_Bounded_Operators.Complex_L2 "HOL-Library.Adhoc_Overloading"
    Tensor_Product.Hilbert_Space_Tensor_Product

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

lemma inf_assoc_subspace[simp]: "A \<sqinter> B \<sqinter> C = A \<sqinter> (B \<sqinter> C)" 
  for A B C :: "_ ell2 ccsubspace"
  by (fact inf.assoc)

lemma inf_left_commute[simp]: "A \<sqinter> (B \<sqinter> C) = B \<sqinter> (A \<sqinter> C)" for A B C :: "_ ell2 ccsubspace"
  using inf.left_commute by auto

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

unbundle no_notation_blinfun_apply
unbundle no_blinfun_notation
unbundle cblinfun_notation

consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)

adhoc_overloading
  cdot timesOp cblinfun_apply applyOpSpace

lemma equal_span':
  fixes f g :: "'a::cbanach \<Rightarrow> 'b::cbanach"
  assumes "bounded_clinear f"
    and "bounded_clinear g"
  assumes "\<And>x. x\<in>G \<Longrightarrow> f x = g x"
  assumes "x\<in>closure (cspan G)"
  shows "f x = g x"
  using assms bounded_clinear_eq_on
  by metis 

(* TODO remove (seems to be a [simp] rule already) *)
lemma bot_plus[simp]: "sup bot x = x" 
  for x :: "'a::complex_normed_vector ccsubspace"
  by simp

abbreviation (input) \<open>idOp \<equiv> id_cblinfun\<close>

declare cblinfun.scaleC_left[simp]
declare cblinfun.scaleC_right[simp]

(* Giving it a name to make adding/removing [simp] easier *)
lemmas le_Inf_iff_subspace[simp] = le_Inf_iff[where 'a=\<open>_::chilbert_space ccsubspace\<close>]

type_synonym 'a clinear_space = \<open>'a ccsubspace\<close>

abbreviation (input) \<open>isProjector \<equiv> is_Proj\<close>

definition tensorSpace where \<open>tensorSpace S T = (tensor_op (Proj S) (Proj T)) *\<^sub>S \<top>\<close>

abbreviation (input) \<open>tensorOp \<equiv> tensor_op\<close>
abbreviation (input) \<open>tensorVec \<equiv> tensor_ell2\<close>

consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr "\<otimes>" 71)
adhoc_overloading tensor tensorOp tensorSpace tensorVec

abbreviation (input) \<open>comm_op \<equiv> swap_ell2\<close>
definition \<open>assoc_op \<equiv> assoc_ell2*\<close>
abbreviation (input) \<open>remove_qvar_unit_op \<equiv> (tensor_ell2_right (1::unit ell2))*\<close>
abbreviation (input) \<open>addState \<equiv> tensor_ell2_right\<close>

lemmas ket_product = tensor_ell2_ket[symmetric]
lemma span_tensor: "ccspan G \<otimes> ccspan H = ccspan {g\<otimes>h|g h. g\<in>G \<and> h\<in>H}" sorry
lemmas adj_comm_op = adjoint_swap_ell2
lemmas tensorOp_applyOp_distr = tensor_op_ell2
lemma assoc_op_apply_tensor[simp]: "assoc_op *\<^sub>V (\<psi> \<otimes> (\<phi> \<otimes> \<tau>)) = (\<psi> \<otimes> \<phi>) \<otimes> \<tau>"
  by (simp add: assoc_ell2'_tensor assoc_op_def)
lemma assoc_op_adj_apply_tensor[simp]: "assoc_op* *\<^sub>V ((\<psi>\<otimes>\<phi>)\<otimes>\<tau>) = \<psi>\<otimes>(\<phi>\<otimes>\<tau>)"
  by (simp add: assoc_ell2_tensor assoc_op_def)
lemmas comm_op_apply_tensor = swap_ell2_tensor
lemma comm_op_swap[simp]: "comm_op o\<^sub>C\<^sub>L (A\<otimes>B) o\<^sub>C\<^sub>L comm_op = B\<otimes>A"
  for A::"('a ell2,'b ell2) cblinfun" and B::"('c ell2,'d ell2) cblinfun"
  sorry
lemmas unitary_comm_op = unitary_swap_ell2
lemma addState_times_scalar[simp]: "addState (a *\<^sub>C \<psi>) = a *\<^sub>C addState \<psi>"
  for a::complex and \<psi>::"'a ell2"
  by (simp add: cblinfun_eqI tensor_ell2_right.rep_eq tensor_ell2_scaleC2)
lemma cinner_tensor: "\<langle>\<gamma> \<otimes> \<psi>, \<delta> \<otimes> \<phi>\<rangle> = \<langle>\<psi>, \<phi>\<rangle> * \<langle>\<gamma>, \<delta>\<rangle>" for \<gamma> \<psi> \<delta> \<phi> :: \<open>_ ell2\<close>
  by simp

lemma addState_adj_times_addState[simp]: 
  includes cblinfun_notation no_blinfun_notation
  fixes \<psi> \<phi> :: "'a ell2"
  shows "addState \<psi>* o\<^sub>C\<^sub>L addState \<phi> = \<langle>\<psi>, \<phi>\<rangle> *\<^sub>C (id_cblinfun::('b ell2,'b ell2) cblinfun)"
proof -
  have "\<langle>\<gamma>, (addState \<psi>* o\<^sub>C\<^sub>L addState \<phi>) *\<^sub>V \<delta>\<rangle> = \<langle>\<gamma>, (\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C id_cblinfun) *\<^sub>V \<delta>\<rangle>" for \<gamma> \<delta> :: "'b ell2"
    apply (simp add: cblinfun_compose_image cinner_adj_right)
    apply (transfer fixing: \<psi> \<phi> \<delta> \<gamma>)
    by (simp add: cinner_tensor)
  hence "(addState \<psi>* o\<^sub>C\<^sub>L addState \<phi>) *\<^sub>V \<delta> = (\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C id_cblinfun) *\<^sub>V \<delta>" for \<delta> :: "'b ell2"
    by (metis (no_types, lifting) adjoint_eqI cinner_adj_left double_adj)
  thus ?thesis
    by (rule cblinfun_eqI)
qed

lemmas id_tensor_id = tensor_id
lemmas comm_op_times_comm_op = swap_ell2_selfinv
lemma unitary_assoc_op[simp]: "unitary assoc_op"
  by (simp add: assoc_op_def)

lemmas tensor_scalar_mult1[simp] = tensor_op_scaleC_left
lemmas tensor_scalar_mult1_ell2[simp] = tensor_ell2_scaleC1
lemmas tensor_scalar_mult2[simp] = tensor_op_scaleC_right
lemmas tensor_scalar_mult2_ell2[simp] = tensor_ell2_scaleC2
lemmas tensor_times[simp] = comp_tensor_op
lemmas tensor_adjoint[simp] = tensor_op_adjoint

lemma tensor_unitary[simp]: 
  assumes "unitary U" and "unitary V"
  shows "unitary (U\<otimes>V)"
  using assms unfolding unitary_def by simp

lemma tensor_isometry[simp]: 
  assumes "isometry U" and "isometry V"
  shows "isometry (U\<otimes>V)"
  using assms unfolding isometry_def by simp
lemma [simp]: "norm \<psi>=1 \<Longrightarrow> isometry (addState \<psi>)"
  unfolding isometry_def by (simp add: cnorm_eq_1)

end
