theory Test
  imports QRHL                 
begin

  
  
  term "1"
  term "a\<longleftrightarrow>b"
ML \<open>
@{term "inf"};;
@{type_name bit}
\<close>
  
lemma "weight (uniform (UNIV::bit set)) = (1::real)"
  apply simp

ML {*  
            let val ct = @{cterm "x=y --> undefined x=undefined y"}
              val thm = Simplifier.rewrite @{context} ct
          in Thm.string_of_thm @{context} thm |> YXML.content_of end
*}
  
  ML {* Sign.string_of_term *}
  
ML {*
val ct = @{cterm "b1 = b2 \<longrightarrow> undefined b1 = undefined undefined b2"}
 (* |> Thm.cterm_of @{context} *)
val t = ct |> Thm.term_of
val T = Thm.typ_of_cterm ct
val thm = Simplifier.rewrite @{context} ct
*}
  
lemma "undefined (k1 = s2 \<and> c1 = c2 \<and> m1 = m2 \<and> cglobA1 = cglobA2 \<and> b1 = b2 \<longrightarrow> \<lbrakk>qglobA1\<rbrakk> \<equiv>\<qq> \<lbrakk>qglobA2\<rbrakk> \<le> \<CC>\<ll>\<aa>[G k1 = G s2 \<and> cglobA1 = cglobA2 \<and> b1 = b2])
"
  apply simp
    
  lemma "(INF b2 b1 a2 a1. \<CC>\<ll>\<aa>[\<not> (a1 = a2 \<and> b1 = b2)] + \<CC>\<ll>\<aa>[a1 \<le> a2 \<and> b1 = 0 \<and> b2 = 0]) \<sqinter>
 \<CC>\<ll>\<aa>[a1 = a2 \<and> b1 = b2 \<and> c1 = c2] = undefined"
    apply simp
  
axiomatization "tensorIso" :: "('a,'b) isometry \<Rightarrow> ('c,'d) isometry \<Rightarrow> ('a*'c,'b*'d) isometry"
axiomatization where idIso_tensor_idIso[simp]: "tensorIso idIso idIso = idIso"
axiomatization "assoc_op" :: "('a*'b*'c, ('a*'b)*'c) isometry"
axiomatization "assoc_op'" :: "(('a*'b)*'c, 'a*'b*'c) isometry"
axiomatization "comm_op" :: "('a*'b, 'b*'a) isometry"
  
consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infix "\<otimes>" 71)
adhoc_overloading tensor tensorIso
  
axiomatization "addState" :: "'a state \<Rightarrow> ('b,'b*'a) isometry"
axiomatization where (* TODO: some disjointness conditions *)
  quantum_eq_add_state: "quantum_equality_full U Q V R \<sqinter> span {\<psi>}\<^sub>@T
             = quantum_equality_full (tensorIso U idIso) (qvariables_concat Q T) (addState \<psi> \<cdot> V) R"
    for U :: "('a,'c) isometry" and V :: "('b,'c) isometry" and \<psi> :: "'d state"
    and Q :: "'a qvariables"    and R :: "'b qvariables"    and T :: "'d qvariables"

axiomatization where qvariables_concat[simp]: "qvariables_concat \<lbrakk>q\<rbrakk> Q = qvariable_cons q Q" (* TODO: should be by definition of qvariables_cons *)
    for q :: "'a qvariable" and Q :: "'b qvariables"
    
context fixes C1 A2 A1 B1 :: "bit qvariable" begin
    
  
lemma "\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> span {EPR}\<^sub>@\<lbrakk>A1, B1\<rbrakk> \<le> quantum_equality_full idIso \<lbrakk>C1,A1,B1\<rbrakk> (addState EPR) \<lbrakk>A2\<rbrakk>"
  apply (subst quantum_eq_add_state)
    by simp
      
term "quantum_equality_full idIso \<lbrakk>C1,A1,B1\<rbrakk> ((H \<otimes> idIso) \<cdot> assoc_op' \<cdot> (CNOT \<otimes> idIso) \<cdot> assoc_op \<cdot> addState EPR) \<lbrakk>A2\<rbrakk>"
    
term \<open>
Qeq[C1=A2] \<sqinter> (lift (span {EPR}) \<lbrakk>A1,B1\<rbrakk>)
\<close>
  
term \<open> \<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<le> (\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> liftSpace (span (insert EPR bot)) \<lbrakk>A1, B1\<rbrakk>) \<div> EPR@\<lbrakk>A1, B1\<rbrakk>
\<close>
  
lemma
  assumes "variable_name C1 = ''C1''"
  assumes "variable_name A2 = ''A2''"
  assumes "variable_name A1 = ''A1''"
  assumes "variable_name B1 = ''B1''"
  (* assumes "colocal (\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) \<lbrakk>A1, B1\<rbrakk>" *)
shows \<open>
\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<le> (\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> span {EPR}\<^sub>@\<lbrakk>A1, B1\<rbrakk>) \<div> EPR@\<lbrakk>A1, B1\<rbrakk>
\<close>
  apply (simp add: assms)
    
lemma plus_Cla[simp]: "Cla[a] + Cla[b] = Cla[a \<or> b]"
  unfolding classical_subspace_def unfolding sup_subspace_def[symmetric] by auto

lemma [simp]: "A \<cdot> (B + C) = (A\<cdot>B) + (A\<cdot>C)" for B :: "'a subspace" sorry
lemma [simp]: "A \<cdot> (B \<sqinter> C) = (A\<cdot>B) \<sqinter> (A\<cdot>C)" for B :: "'a subspace" sorry
lemma [simp]: "U \<cdot> (INF z. B z) = (INF z. U \<cdot> B z)" sorry
lemma [simp]: "(INF z. A z) \<sqinter> B = (INF z. A z \<sqinter> B)" for B :: "_ :: complete_lattice"
  by (simp add: INF_inf_const2)  
lemma [simp]: "(A \<le> (INF z. B z)) = (\<forall>z. A \<le> B z)" for A :: "_ :: complete_lattice"
  by (simp add: le_Inf_iff)
lemma INF_div[simp]: "(INF z. A z) \<div> \<psi>@Q = (INF z. A z \<div> \<psi>@Q)" sorry
(* lemma [simp]: "(INF z. B z) + C = (INF z. B z + C)" for C :: "'a subspace" WRONG *)
lemma [simp]: "unitary U \<Longrightarrow> U \<cdot> Cla[b] = Cla[b]" apply (cases b) by auto

    
    
    
    
    
    
  
lemma
  assumes "colocal (\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) \<lbrakk>A1, B1\<rbrakk>"
shows \<open>


\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<le> (CNOT\<^sub>@\<lbrakk>C1, A1\<rbrakk> \<cdot> (H\<^sub>@\<lbrakk>C1\<rbrakk> \<cdot> (INF x. (INF xa. (\<CC>\<ll>\<aa>[x \<noteq> 1] + X\<^sub>@\<lbrakk>B1\<rbrakk> \<cdot> ((\<CC>\<ll>\<aa>[xa \<noteq> 1] + Z\<^sub>@\<lbrakk>B1\<rbrakk> \<cdot> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) \<sqinter> (\<CC>\<ll>\<aa>[xa = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>))) \<sqinter> (\<CC>\<ll>\<aa>[x = 1] + (\<CC>\<ll>\<aa>[xa \<noteq> 1] + Z\<^sub>@\<lbrakk>B1\<rbrakk> \<cdot> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) \<sqinter> (\<CC>\<ll>\<aa>[xa = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>)) \<sqinter> span {|xa\<rangle>}\<^sub>@\<lbrakk>B1\<rbrakk> + ortho (span {|xa\<rangle>}\<^sub>@\<lbrakk>B1\<rbrakk>)) \<sqinter> span {|x\<rangle>}\<^sub>@\<lbrakk>A1\<rbrakk> + ortho (span {|x\<rangle>}\<^sub>@\<lbrakk>A1\<rbrakk>)))) \<div> EPR@\<lbrakk>A1, B1\<rbrakk>

\<close>
  apply (auto simp: assms)