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

    Bounded_Operators.Bounded_Operators Bounded_Operators.Complex_L2 "HOL-Library.Adhoc_Overloading" Tensor_Product.Tensor_Product Tensor_Product.ToDo_Tensor

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


type_synonym ('a,'b) bounded = "('a,'b) cblinfun"
type_synonym ('a,'b) l2bounded = "('a ell2, 'b ell2) bounded"
type_synonym 'a subspace = "'a ell2 clinear_space"

abbreviation "ell2_to_bounded :: 'a::chilbert_space \<Rightarrow> ('b::{CARD_1,enum} ell2,'a) bounded
    == vector_to_cblinfun"
abbreviation "complex_to_C1 :: complex \<Rightarrow> 'a::{CARD_1,enum} ell2 == of_complex"
abbreviation "C1_to_complex == (one_dim_isom :: _ \<Rightarrow> complex)"

abbreviation "applyOp == cblinfun_apply"

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
  assumes "x\<in>closure (complex_vector.span G)"
  shows "f x = g x"
  using assms equal_span_applyOpSpace
  by metis 


end
