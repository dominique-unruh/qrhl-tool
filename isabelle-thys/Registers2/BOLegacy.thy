(* 

This file contains some legacy fixes for making qrhl-tool compatible
with current version of Tensor_Product and Bounded_Operators. Should
be removed eventually.

*)

theory BOLegacy
  imports 
    Complex_Bounded_Operators.Complex_L2

    (* TODO: Still needed here? *)
    Registers.Quantum (* Imported because otherwise instantiations in QRHL_Code for bit will happen that make it impossible to merge Registers.Quantum with that theory.
And we include it already here so that out simpset removals here won't be overwritten in a merge *)
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
no_notation Group.monoid.mult (infixl "\<otimes>\<index>" 70)
no_notation m_inv ("inv\<index> _" [81] 80)
(* hide_const (open) Quantum.hadamard
hide_const (open) Quantum.CNOT
hide_const (open) Quantum.pauliX
hide_const (open) Quantum.pauliZ *)

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

(* notation tensor_ell2 (infixr "\<otimes>\<^sub>l" 70) *)

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

abbreviation (input) "addState == tensor_ell2_right"
abbreviation (input) \<open>comm_op == swap_ell2\<close>
abbreviation (input) \<open>assoc_op == assoc_ell2*\<close>

lemmas ket_product = tensor_ell2_ket[symmetric]

unbundle no blinfun_apply_syntax
(* unbundle no_blinfun_notation *)
unbundle cblinfun_syntax

consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)

adhoc_overloading
  cdot "\<lambda>x. timesOp x" "\<lambda>x. cblinfun_apply x" "\<lambda>x. applyOpSpace x"

consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<otimes>" 70)

adhoc_overloading
  tensor \<open>\<lambda>x. tensor_ell2 x\<close> \<open>\<lambda>x. tensor_op x\<close> \<open>\<lambda>x. tensor_ccsubspace x\<close>

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

lemma proj_ket_is_0[simp]: \<open>proj (ket x) *\<^sub>S ccspan {ket y} = 0\<close> if \<open>x \<noteq> y\<close>
  using that by (simp add: cblinfun_image_ccspan cinner_ket flip: butterfly_eq_proj)

end
