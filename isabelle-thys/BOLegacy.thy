(* 

This file contains some legacy fixes for making qrhl-tool compatible
with current version of Tensor_Product and Bounded_Operators. Should
be removed eventually.

*)

theory BOLegacy
imports Bounded_Operators.Bounded_Operators Bounded_Operators.Complex_L2 "HOL-Library.Adhoc_Overloading" Tensor_Product.Tensor_Product Bounded_Operators.ToDo Tensor_Product.ToDo_Tensor
begin

type_synonym ('a,'b) l2bounded = "('a ell2, 'b ell2) bounded"
type_synonym 'a subspace = "'a ell2 linear_space"

declare ortho_involution[simp]

abbreviation "applyOp == times_bounded_vec"

unbundle bounded_notation

consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)

adhoc_overloading
  cdot timesOp applyOp applyOpSpace

lemma [simp]: "isProjector (Proj S)"
  by (rule Proj_isProjector)

end
