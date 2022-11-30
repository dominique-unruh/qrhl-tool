theory Teleport
  imports QRHL.QRHL
begin

lemma assoc_op_lift_aux:
  fixes U Q R S
  assumes "distinct_qvars (variable_concat Q R)" and "distinct_qvars (variable_concat R S)" and "distinct_qvars (variable_concat Q S)"
  defines "V == assoc_op* o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L assoc_op"
  shows
    "U\<guillemotright>(variable_concat (variable_concat Q R) S) = V\<guillemotright>(variable_concat Q (variable_concat R S))"
  using assms by (metis (no_types, lifting) V_def double_adj distinct_qvars_split2 distinct_qvars_swap
      qvar_trafo_adj qvar_trafo_assoc_op qvar_trafo_l2bounded)

lemma assoc_replace: 
  assumes "A o\<^sub>C\<^sub>L B = C"
  shows "D o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L B = D o\<^sub>C\<^sub>L C"
  by (simp add: cblinfun_compose_assoc assms) 

lemma teleport_goal1:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows \<open>quantum_equality_full (addState EPR*) \<lbrakk>C1, A1, B1\<rbrakk> id_cblinfun \<lbrakk>A2\<rbrakk> \<le> CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> *\<^sub>S hadamard\<guillemotright>\<lbrakk>C1\<rbrakk> *\<^sub>S quantum_equality_full (addState EPR* o\<^sub>C\<^sub>L (assoc_op* o\<^sub>C\<^sub>L (CNOT \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L (assoc_op o\<^sub>C\<^sub>L hadamard \<otimes>\<^sub>o id_cblinfun)))) \<lbrakk>C1, A1, B1\<rbrakk> id_cblinfun \<lbrakk>A2\<rbrakk>\<close>
proof -
  have hadamard: "(hadamard \<otimes> id_cblinfun) o\<^sub>C\<^sub>L (hadamard \<otimes>\<^sub>o id_cblinfun) = id_cblinfun" by simp
  have CNOT: "(CNOT \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (CNOT \<otimes>\<^sub>o id_cblinfun) = id_cblinfun" by simp
  show ?thesis
    by (simp add: distinct_qvars_split1 distinct_qvars_split2 cblinfun_compose_assoc[symmetric] assoc_op_lift_aux
        lift_extendR[where U=hadamard and R="\<lbrakk>A1,B1\<rbrakk>"] lift_extendR[where U=CNOT and R="\<lbrakk>B1\<rbrakk>"]
        assoc_replace[OF hadamard] assoc_replace[OF unitaryD2] assoc_replace[OF CNOT] assoc_replace[OF isometryD])
qed

lemma teleport_goal2_a0c0:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows \<open>(proj |0\<rangle>\<guillemotright>\<lbrakk>C1\<rbrakk> o\<^sub>C\<^sub>L proj |0\<rangle>\<guillemotright>\<lbrakk>A1\<rbrakk>) *\<^sub>S quantum_equality_full id_cblinfun \<lbrakk>C1, A1, B1\<rbrakk> (hadamard \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op* o\<^sub>C\<^sub>L CNOT \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op o\<^sub>C\<^sub>L addState EPR) \<lbrakk>A2\<rbrakk> \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>\<close>
  apply (simp add: prepare_for_code)
  by eval


lemma teleport_goal2_a0c1:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows \<open>(pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> o\<^sub>C\<^sub>L proj |1\<rangle>\<guillemotright>\<lbrakk>C1\<rbrakk> o\<^sub>C\<^sub>L proj |0\<rangle>\<guillemotright>\<lbrakk>A1\<rbrakk>) *\<^sub>S quantum_equality_full id_cblinfun \<lbrakk>C1, A1, B1\<rbrakk> (hadamard \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op* o\<^sub>C\<^sub>L CNOT \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op o\<^sub>C\<^sub>L addState EPR) \<lbrakk>A2\<rbrakk> \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>\<close>
  apply (simp add: prepare_for_code)
  by eval

lemma teleport_goal2_a1c0:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows \<open>(pauliX\<guillemotright>\<lbrakk>B1\<rbrakk> o\<^sub>C\<^sub>L proj |0\<rangle>\<guillemotright>\<lbrakk>C1\<rbrakk> o\<^sub>C\<^sub>L proj |1\<rangle>\<guillemotright>\<lbrakk>A1\<rbrakk>) *\<^sub>S quantum_equality_full id_cblinfun \<lbrakk>C1, A1, B1\<rbrakk> (hadamard \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op* o\<^sub>C\<^sub>L CNOT \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op o\<^sub>C\<^sub>L addState EPR) \<lbrakk>A2\<rbrakk> \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>\<close>
  apply (simp add: prepare_for_code)
  by eval

lemma teleport_goal2_a1c1:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows \<open>(pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> o\<^sub>C\<^sub>L pauliX\<guillemotright>\<lbrakk>B1\<rbrakk> o\<^sub>C\<^sub>L proj |1\<rangle>\<guillemotright>\<lbrakk>C1\<rbrakk> o\<^sub>C\<^sub>L proj |1\<rangle>\<guillemotright>\<lbrakk>A1\<rbrakk>) *\<^sub>S quantum_equality_full id_cblinfun \<lbrakk>C1, A1, B1\<rbrakk> (hadamard \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op* o\<^sub>C\<^sub>L CNOT \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op o\<^sub>C\<^sub>L addState EPR) \<lbrakk>A2\<rbrakk> \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>\<close>
  apply (simp add: prepare_for_code)
  by eval

end
