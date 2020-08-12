(* 

This file contains some legacy fixes for making qrhl-tool compatible
with current version of Tensor_Product and Bounded_Operators. Should
be removed eventually.

*)

theory BOLegacy
imports Bounded_Operators.Bounded_Operators Bounded_Operators.Complex_L2 "HOL-Library.Adhoc_Overloading" Tensor_Product.Tensor_Product Tensor_Product.ToDo_Tensor
begin

type_synonym ('a,'b) bounded = "('a,'b) cblinfun"
type_synonym ('a,'b) l2bounded = "('a ell2, 'b ell2) bounded"
type_synonym 'a subspace = "'a ell2 clinear_space"

abbreviation "ell2_to_bounded :: 'a::chilbert_space \<Rightarrow> ('b::{CARD_1,enum} ell2,'a) bounded
    == vector_to_cblinfun"
abbreviation "complex_to_C1 :: complex \<Rightarrow> 'a::{CARD_1,enum} ell2 == of_complex"
abbreviation "C1_to_complex == one_dim_to_complex"

abbreviation "applyOp == cblinfun_apply"

unbundle no_notation_blinfun_apply
unbundle no_blinfun_notation
unbundle cblinfun_notation

consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)

adhoc_overloading
  cdot timesOp cblinfun_apply applyOpSpace

lemma equal_span':
  fixes f g :: "'a::cbanach \<Rightarrow> 'b::cbanach"
  assumes "cbounded_linear f"
    and "cbounded_linear g"
  assumes "\<And>x. x\<in>G \<Longrightarrow> f x = g x"
  assumes "x\<in>closure (complex_vector.span G)"
  shows "f x = g x"
  using assms equal_span_applyOpSpace
  by metis 


end
