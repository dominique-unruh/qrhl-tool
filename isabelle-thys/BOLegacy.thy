(* 

This file contains some legacy fixes for making qrhl-tool compatible
with current version of Tensor_Product and Bounded_Operators. Should
be removed eventually.

*)

theory BOLegacy
imports Bounded_Operators.Bounded_Operators Bounded_Operators.Complex_L2 "HOL-Library.Adhoc_Overloading" Tensor_Product.Tensor_Product Bounded_Operators.ToDo Tensor_Product.ToDo_Tensor
begin

abbreviation "ell2_to_bounded :: 'a::chilbert_space \<Rightarrow> ('b::{CARD_1,enum} ell2,'a) bounded
== vector_to_bounded"
abbreviation "complex_to_C1 :: complex \<Rightarrow> 'a::{CARD_1,enum} ell2 == of_complex"
abbreviation "C1_to_complex == one_dim_to_complex"

(* (* TODO use vector_to_bounded instead *)
lemma ell2_to_bounded_times_vec[simp]:
  includes bounded_notation
  shows "ell2_to_bounded \<phi> *\<^sub>v \<gamma> = one_dim_to_complex \<gamma> *\<^sub>C \<phi>"
  apply transfer by (rule refl)

(* TODO use vector_to_bounded instead *)
lemma ell2_to_bounded_adj_times_vec[simp]:
  includes bounded_notation
  shows "ell2_to_bounded \<psi>* *\<^sub>v \<phi> = complex_to_C1 (cinner \<psi> \<phi>)"
proof -
  have "one_dim_to_complex (ell2_to_bounded \<psi>* *\<^sub>v \<phi> :: 'a ell2) = cinner 1 (ell2_to_bounded \<psi>* *\<^sub>v \<phi> :: 'a ell2)"
    by (simp add: one_dim_to_complex_def)
  also have "\<dots> = cinner (ell2_to_bounded \<psi> *\<^sub>v (1::'a ell2)) \<phi>"
    by (metis adjoint_I adjoint_twice)
  also have "\<dots> = \<langle>\<psi>, \<phi>\<rangle>"
    by simp
  finally have "one_dim_to_complex (ell2_to_bounded \<psi>* *\<^sub>v \<phi> :: 'a ell2) = \<langle>\<psi>, \<phi>\<rangle>" by -
  thus ?thesis
    by (metis one_dim_to_complex_inverse)
qed

(* TODO use vector_to_bounded instead *)
lemma ell2_to_bounded_adj_times_ell2_to_bounded[simp]:
  includes bounded_notation
  shows "ell2_to_bounded \<psi>* *\<^sub>o ell2_to_bounded \<phi> = cinner \<psi> \<phi> *\<^sub>C idOp"
proof -
  have "one_dim_to_complex ((ell2_to_bounded \<psi>* *\<^sub>o ell2_to_bounded \<phi>) *\<^sub>v \<gamma>) = one_dim_to_complex ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>v \<gamma>)" 
    for \<gamma> :: "'c::{CARD_1,enum} ell2"
    by (simp add: times_applyOp)
  hence "((ell2_to_bounded \<psi>* *\<^sub>o ell2_to_bounded \<phi>) *\<^sub>v \<gamma>) = ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>v \<gamma>)" 
    for \<gamma> :: "'c::{CARD_1,enum} ell2"
    using one_dim_to_complex_inverse by metis
  thus ?thesis
    using  bounded_ext[where A = "ell2_to_bounded \<psi>* *\<^sub>o ell2_to_bounded \<phi>"
        and B = "\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C idOp"]
    by auto
qed *)


(* lemma ortho_bot[simp]: "- bot = (top::'a::chilbert_space linear_space)"
  apply transfer by auto

lemma ortho_top[simp]: "- top = (bot::'a::chilbert_space linear_space)"
  apply transfer by auto *)

(* lemma cinner_1_C1: "cinner 1 \<psi> = C1_to_complex \<psi>"
  by (simp add: one_dim_to_complex_def) *)

(* lemma cinner_adjoint:
  includes bounded_notation
  shows "cinner \<psi> (A *\<^sub>v \<phi>) = cinner (A* *\<^sub>v \<psi>) \<phi>"
  by (rule adjoint_I[symmetric])

lemma cinner_adjoint':
  includes bounded_notation
  shows "cinner (A *\<^sub>v \<phi>) \<psi> = cinner \<phi> (A* *\<^sub>v \<psi>)"
  by (simp add: cinner_adjoint) *)

(* lemma demorgan_inf: "- ((A::_::orthocomplemented_lattice) \<sqinter> B) = - A \<squnion> - B"
  by simp

lemma demorgan_sup: "- ((A::_::orthocomplemented_lattice) \<squnion> B) = - A \<sqinter> - B"
  by simp *)

type_synonym ('a,'b) l2bounded = "('a ell2, 'b ell2) bounded"
type_synonym 'a subspace = "'a ell2 linear_space"

(* declare ortho_involution[simp] *)

abbreviation "applyOp == times_bounded_vec"

unbundle bounded_notation

consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)

adhoc_overloading
  cdot timesOp times_bounded_vec applyOpSpace

(* lemma [simp]: "isProjector (Proj S)"
  by (rule Proj_isProjector) *)

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
