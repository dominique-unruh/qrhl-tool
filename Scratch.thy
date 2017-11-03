theory Scratch
  imports QRHL_Protocol
begin

fun powerIso :: "('a,'a) isometry \<Rightarrow> nat \<Rightarrow> ('a,'a) isometry" where 
  "powerIso U 0 = idIso"
| "powerIso U (Suc i) = U \<cdot> powerIso U i"

declare [[coercion "\<lambda>b::bit. if b=0 then (0::nat) else 1"]]

consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infix "\<otimes>" 71)
adhoc_overloading tensor tensorIso

axiomatization where Qeq_div_div[simp]: 
  "((quantum_equality_full idIso X1 idIso X2 \<div> \<psi>@X1) \<div> \<psi>@X2) = top" for \<psi> :: "'a state"

axiomatization where Qeq_mult1[simp]:
  "U\<^sub>@Q1 \<cdot> quantum_equality_full U1 Q1 U2 Q2 = quantum_equality_full (U1\<cdot>U*) Q1 U2 Q2"
 for U::"('a,'a) isometry" and U2 :: "('b,'c) isometry"  

axiomatization where Qeq_mult2[simp]:
  "U\<^sub>@Q2 \<cdot> quantum_equality_full U1 Q1 U2 Q2 = quantum_equality_full U1 Q1 (U2\<cdot>U*) Q2"
 for U::"('a,'a) isometry" and U1 :: "('b,'c) isometry"  

axiomatization where
  CNOT_CNOT[simp]: "CNOT \<cdot> CNOT = idIso"
and H_H[simp]: "H \<cdot> H = idIso"
and X_X[simp]: "X \<cdot> X = idIso"
and Y_Y[simp]: "Y \<cdot> Y = idIso"
and Z_Z[simp]: "Z \<cdot> Z = idIso"

lemmas inf_assoc[simp] = inf.assoc[symmetric]

declare imp_conjL[simp]

axiomatization where 
  mult_inf_distrib[simp]: "U \<cdot> (B \<sqinter> C) = (U \<cdot> B) \<sqinter> (U \<cdot> C)" 
for U :: "('a,'b) isometry" and B C :: "'a subspace"
(* TODO: declare all isometries as unitary for simplicity *)

axiomatization where idIso_adjoint[simp]: "idIso* = idIso"
and image_id[simp]: "imageIso idIso = top"
and idIso_mult_subspace[simp]: "idIso \<cdot> V = V"
and idIso_mult_iso1[simp]: "idIso \<cdot> U = U"
and idIso_mult_iso2[simp]: "U \<cdot> idIso = U"
for V :: "'a subspace" and U :: "('a,'b) isometry"
(* and id_lift[simp]: "idIso\<^sub>@Q = idIso" for Q :: "'q qvariables" *)

lemma bij_add_const[simp]: "bij (\<lambda>x. x+(y::_::ab_group_add))" 
  apply (rule bijI') apply simp
  apply (rename_tac z) apply (rule_tac x="z-y" in exI)
  by auto

lemma bit_plus_1_eq[simp]: "(a+1=b) = (a\<noteq>b)" for a b :: bit
  by auto


axiomatization where qeq_collect:
 "quantum_equality_full U Q1 V Q2 = quantum_equality_full (V*\<cdot>U) Q1 idIso Q2"
for U :: "('a,'b) isometry" and V :: "('c,'b) isometry"

lemma qeq_collect_guarded[simp]:
assumes "NO_MATCH idIso V"
  shows "quantum_equality_full U Q1 V Q2 = quantum_equality_full (V*\<cdot>U) Q1 idIso Q2"
  using qeq_collect by auto
  
axiomatization where mult_INF[simp]: "U \<cdot> (INF x. V x) = (INF x. U \<cdot> V x)" 
  for V :: "'a \<Rightarrow> 'b subspace" and U :: "('b,'c) isometry"

axiomatization where leq_INF[simp]: "A \<le> (INF x. V x)" 
  for V :: "'a \<Rightarrow> 'b subspace"

lemma "
\<lbrakk>q1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2\<rbrakk> \<le> H\<^sub>@\<lbrakk>q2\<rbrakk> \<cdot> (INF x. powerIso H (if x = 0 then 0 else 1)*\<^sub>@\<lbrakk>q2\<rbrakk> \<cdot> (\<CC>\<ll>\<aa>[x = 0] + quantum_equality_full H \<lbrakk>q1\<rbrakk> idIso \<lbrakk>q2\<rbrakk>) \<sqinter> (powerIso H (if x = 0 then 0 else 1)*\<^sub>@\<lbrakk>q2\<rbrakk> \<cdot> (\<CC>\<ll>\<aa>[x = 1] + \<lbrakk>q1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2\<rbrakk>)) \<sqinter> (powerIso H (if x = 0 then 0 else 1)*\<^sub>@\<lbrakk>q2\<rbrakk> \<cdot> imageIso (powerIso H (if x = 0 then 0 else 1))\<^sub>@\<lbrakk>q2\<rbrakk>))
" for z b1 b2 :: bit
  apply simp
  oops

end
