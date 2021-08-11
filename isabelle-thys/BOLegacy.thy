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
    Tensor_Product.Tensor_Product_Code

    Bounded_Operators.Complex_L2 "HOL-Library.Adhoc_Overloading" Tensor_Product.Tensor_Product Tensor_Product.ToDo_Tensor

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

end
