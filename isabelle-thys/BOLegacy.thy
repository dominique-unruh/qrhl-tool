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
    Tensor_Product2.Tensor_Product_Code

    Complex_Bounded_Operators.Complex_L2 "HOL-Library.Adhoc_Overloading" Tensor_Product2.Tensor_Product Tensor_Product2.ToDo_Tensor

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

unbundle no_notation_blinfun_apply
unbundle no_blinfun_notation
unbundle cblinfun_notation

consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)

adhoc_overloading
  cdot "\<lambda>x. timesOp x" "\<lambda>x. cblinfun_apply x" "\<lambda>x. applyOpSpace x"

lemma equal_span':
  fixes f g :: "'a::cbanach \<Rightarrow> 'b::cbanach"
  assumes "bounded_clinear f"
    and "bounded_clinear g"
  assumes "\<And>x. x\<in>G \<Longrightarrow> f x = g x"
  assumes "x\<in>closure (cspan G)"
  shows "f x = g x"
  using assms by (rule bounded_clinear_eq_on)

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

end
