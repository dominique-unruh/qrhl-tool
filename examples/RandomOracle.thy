theory RandomOracle
  imports 
(* QRHL *)
"../src/main/isabelle/QRHL"
begin

section \<open>Specification\<close>

typedecl x
typedecl y
typedecl r
instance x :: finite sorry
instance y :: finite sorry
instance r :: finite sorry

(* class xor =
  fixes xor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
class uoracle_compat = xor + 
  assumes uoracle_compat1: "\<exists>z. xor z y = x"
  assumes uoracle_compat2: "xor z y = xor z' y \<Longrightarrow> z = z'" *)



(* (* TODO: move to QRHL *)
axiomatization Uoracle :: "('x\<Rightarrow>'y) \<Rightarrow> ('x*'y,'x*'y) bounded"
  where unitary_Uoracle[simp]: "unitary (Uoracle f)"
  for f :: "'x \<Rightarrow> 'y" *)

(* definition "Uoracle f = classical_operator (Some o (\<lambda>(x,y::_::uoracle_compat). (x, xor y (f x))))" *)



(* lemma "unitary (Uoracle f)"
  unfolding Uoracle_def
proof (rule unitary_classical_operator)
  define f' where "f' = (\<lambda>(x, y). (x, xor y (f x)))"
  have "surj f'"
    unfolding surj_def
    unfolding f'_def case_prod_unfold
    apply auto by (metis uoracle_compat1) 
  have "inj f'"
    apply (rule injI)
    unfolding f'_def case_prod_unfold
    using uoracle_compat2 apply auto by blast
  show [unfolded f'_def]: "bij f'"
    by (simp add: \<open>inj f'\<close> \<open>surj f'\<close> bij_betw_imageI)    
qed *)

axiomatization \<pi> :: "r \<Rightarrow> y"
  where bij_pi: "bij \<pi>"

section \<open>Lemmas\<close>

lemma l1: "isometry (A*) \<Longrightarrow> A \<cdot> (A* \<cdot> B) = B" for B :: "(_,_) bounded"
  by (metis adjUU adjoint_twice timesOp_assoc times_idOp2)
lemma l2: "(A \<otimes> B) \<cdot> ((A' \<otimes> B') \<cdot> C) = ((A\<cdot>A') \<otimes> (B\<cdot>B')) \<cdot> C" for A A' B B' C :: "(_,_) bounded"
  by (subst timesOp_assoc[symmetric], auto)
lemma l3: "isometry A \<Longrightarrow> A* \<cdot> (A \<cdot> B) = B" for B :: "(_,_) bounded"
  by (metis adjUU timesOp_assoc times_idOp2)

lemma Uora_twice:
  assumes [simp]: "declared_qvars \<lbrakk>x1,y1,x2,y2,qglobA1,qglobA2\<rbrakk>"
  assumes heq: "h1=h2"
  shows "(Uoracle h2*\<guillemotright>\<lbrakk>x2, y2\<rbrakk> \<cdot> (Uoracle h1*\<guillemotright>\<lbrakk>x1, y1\<rbrakk> \<cdot> \<lbrakk>qglobA1, x1, y1\<rbrakk> \<equiv>\<qq> \<lbrakk>qglobA2, x2, y2\<rbrakk>)) =
         \<lbrakk>qglobA1, x1, y1\<rbrakk> \<equiv>\<qq> \<lbrakk>qglobA2, x2, y2\<rbrakk>"
  apply (rewrite at "_* \<guillemotright> \<lbrakk>x1,y1\<rbrakk>" reorder_variables_hint_def[symmetric, where R="\<lbrakk>qglobA1,x1,y1\<rbrakk>"])
  apply (rewrite at "_* \<guillemotright> \<lbrakk>x2,y2\<rbrakk>" reorder_variables_hint_def[symmetric, where R="\<lbrakk>qglobA2,x2,y2\<rbrakk>"])
  by (simp add: l1 l2 l3 heq timesOp_assoc)

end
