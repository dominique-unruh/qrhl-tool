theory Test
  imports QRHL                 
begin

lemma plus_Cla[simp]: "Cla[a] + Cla[b] = Cla[a \<or> b]"
  unfolding classical_subspace_def unfolding sup_subspace_def[symmetric] by auto

lemma [simp]: "A \<cdot> (B + C) = (A\<cdot>B) + (A\<cdot>C)" for B :: "'a subspace" sorry
lemma [simp]: "A \<cdot> (B \<sqinter> C) = (A\<cdot>B) \<sqinter> (A\<cdot>C)" for B :: "'a subspace" sorry
lemma [simp]: "U \<cdot> (INF z. B z) = (INF z. U \<cdot> B z)" sorry
lemma [simp]: "(INF z. A z) \<sqinter> B = (INF z. A z \<sqinter> B)" for B :: "_ :: complete_lattice"
  by (simp add: INF_inf_const2)  
lemma [simp]: "(A \<le> (INF z. B z)) = (\<forall>z. A \<le> B z)" for A :: "_ :: complete_lattice"
  by (simp add: le_Inf_iff)
lemma [simp]: "(INF z. A z) \<div> \<psi>@Q = (INF z. A z \<div> \<psi>@Q)" sorry
(* lemma [simp]: "(INF z. B z) + C = (INF z. B z + C)" for C :: "'a subspace" WRONG *)
lemma [simp]: "unitary U \<Longrightarrow> U \<cdot> Cla[b] = Cla[b]" apply (cases b) by auto

  
lemma \<open>

\<lbrakk>A1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<le>

(CNOT\<^sub>@\<lbrakk>C1, A1\<rbrakk> \<cdot> (H\<^sub>@\<lbrakk>C1\<rbrakk> \<cdot> (INF x. (INF xa. (\<CC>\<ll>\<aa>[x \<noteq> 1] + X\<^sub>@\<lbrakk>B1\<rbrakk> \<cdot> ((\<CC>\<ll>\<aa>[xa \<noteq> 1] + Z\<^sub>@\<lbrakk>B1\<rbrakk> \<cdot> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) \<sqinter> (\<CC>\<ll>\<aa>[xa = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>)))
                                       \<sqinter> (\<CC>\<ll>\<aa>[x = 1] + (\<CC>\<ll>\<aa>[xa \<noteq> 1] + Z\<^sub>@\<lbrakk>B1\<rbrakk> \<cdot> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) \<sqinter> (\<CC>\<ll>\<aa>[xa = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>))
                                       \<sqinter> span {|xa\<rangle>}\<^sub>@\<lbrakk>B1\<rbrakk>
                                       + ortho (span {|xa\<rangle>}\<^sub>@\<lbrakk>B1\<rbrakk>))
                                 \<sqinter> span {|x\<rangle>}\<^sub>@\<lbrakk>A1\<rbrakk>
                                 + ortho (span {|x\<rangle>}\<^sub>@\<lbrakk>A1\<rbrakk>))))
    \<div> EPR@\<lbrakk>A1, B1\<rbrakk>

\<close>
 apply simp