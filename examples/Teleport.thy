theory Teleport
  imports QRHL.QRHL
begin

(* lemma assoc_op_lift_aux:
  fixes U Q R S
  assumes [register]: \<open>qregister \<lbrakk>Q, R, S\<rbrakk>\<close>
  defines "V == assoc_op* o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L assoc_op"
  shows "U \<guillemotright> \<lbrakk>\<lbrakk>Q,R\<rbrakk>,S\<rbrakk> = V \<guillemotright> \<lbrakk>Q,\<lbrakk>R,S\<rbrakk>\<rbrakk>"
 *)

(* lemma assoc_replace: 
  assumes "A o\<^sub>C\<^sub>L B = C"
  shows "D o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L B = D o\<^sub>C\<^sub>L C"
  by (simp add: cblinfun_compose_assoc assms)  *)

lemma teleport_goal1:
  assumes [register]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows \<open>quantum_equality_full (addState EPR*) \<lbrakk>C1, A1, B1\<rbrakk> id_cblinfun \<lbrakk>A2\<rbrakk> 
    \<le> CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> *\<^sub>S hadamard\<guillemotright>\<lbrakk>C1\<rbrakk> *\<^sub>S quantum_equality_full (addState EPR* o\<^sub>C\<^sub>L (assoc_op* o\<^sub>C\<^sub>L (CNOT \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L (assoc_op o\<^sub>C\<^sub>L hadamard \<otimes>\<^sub>o id_cblinfun)))) \<lbrakk>C1, A1, B1\<rbrakk> id_cblinfun \<lbrakk>A2\<rbrakk>\<close>
(* TODO: Find a simpler proof (add automation) *)
proof -
  have hadamard: "(hadamard \<otimes> id_cblinfun) o\<^sub>C\<^sub>L (hadamard \<otimes>\<^sub>o id_cblinfun) = id_cblinfun" by simp
  have CNOT: "(CNOT \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (CNOT \<otimes>\<^sub>o id_cblinfun) = id_cblinfun" by simp
  have 1: \<open>apply_qregister C1 hadamard = hadamard \<guillemotright> \<lbrakk>C1 \<mapsto> \<lbrakk>C1, A1, B1\<rbrakk>\<rbrakk> \<guillemotright> \<lbrakk>C1, A1, B1\<rbrakk>\<close>
    apply (subst qregister_chain_apply[unfolded o_def, symmetric, THEN fun_cong])
    apply (subst qregister_chain_conversion)
    by (auto intro!: qregister_le_pair_rightI2 qregister_le_pair_rightI1 intro!: qregister_le_refl qregister_le_pair_leftI)
  have 2: \<open>apply_qregister \<lbrakk>C1, A1\<rbrakk>\<^sub>q CNOT = CNOT \<guillemotright> \<lbrakk>\<lbrakk>C1, A1\<rbrakk>\<^sub>q \<mapsto> \<lbrakk>C1, A1, B1\<rbrakk>\<rbrakk> \<guillemotright> \<lbrakk>C1, A1, B1\<rbrakk>\<close>
    apply (subst qregister_chain_apply[unfolded o_def, symmetric, THEN fun_cong])
    apply (subst qregister_chain_conversion)
    apply (rule qregister_le_pair_leftI, simp)
    apply (rule qregister_le_pair_rightI1, simp, simp)
    apply (rule qregister_le_pair_rightI2, simp)
     apply (rule qregister_le_pair_rightI1, simp, simp)
    by simp
  have 3: \<open>(addState EPR* o\<^sub>C\<^sub>L (assoc_op* o\<^sub>C\<^sub>L (CNOT \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L (assoc_op o\<^sub>C\<^sub>L hadamard \<otimes>\<^sub>o id_cblinfun))) o\<^sub>C\<^sub>L
         apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q hadamard o\<^sub>C\<^sub>L
         apply_qregister \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q CNOT) = (addState EPR*)\<close>
    apply prepare_for_code
    by eval
  show ?thesis
    unfolding 1 2
    by (simp add: 3)
qed

lemma teleport_goal2_a0c0:
  assumes [register]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows \<open>(proj |0\<rangle>\<guillemotright>\<lbrakk>C1\<rbrakk> o\<^sub>C\<^sub>L proj |0\<rangle>\<guillemotright>\<lbrakk>A1\<rbrakk>) *\<^sub>S quantum_equality_full id_cblinfun \<lbrakk>C1, A1, B1\<rbrakk> (hadamard \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op* o\<^sub>C\<^sub>L CNOT \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op o\<^sub>C\<^sub>L addState EPR) \<lbrakk>A2\<rbrakk> \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>\<close>
  apply prepare_for_code
  by eval


lemma teleport_goal2_a0c1:
  assumes [register]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows \<open>(pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> o\<^sub>C\<^sub>L proj |1\<rangle>\<guillemotright>\<lbrakk>C1\<rbrakk> o\<^sub>C\<^sub>L proj |0\<rangle>\<guillemotright>\<lbrakk>A1\<rbrakk>) *\<^sub>S quantum_equality_full id_cblinfun \<lbrakk>C1, A1, B1\<rbrakk> (hadamard \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op* o\<^sub>C\<^sub>L CNOT \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op o\<^sub>C\<^sub>L addState EPR) \<lbrakk>A2\<rbrakk> \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>\<close>
  apply prepare_for_code
  by eval

lemma teleport_goal2_a1c0:
  assumes [register]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows \<open>(pauliX\<guillemotright>\<lbrakk>B1\<rbrakk> o\<^sub>C\<^sub>L proj |0\<rangle>\<guillemotright>\<lbrakk>C1\<rbrakk> o\<^sub>C\<^sub>L proj |1\<rangle>\<guillemotright>\<lbrakk>A1\<rbrakk>) *\<^sub>S quantum_equality_full id_cblinfun \<lbrakk>C1, A1, B1\<rbrakk> (hadamard \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op* o\<^sub>C\<^sub>L CNOT \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op o\<^sub>C\<^sub>L addState EPR) \<lbrakk>A2\<rbrakk> \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>\<close>
  apply prepare_for_code
  by eval

lemma teleport_goal2_a1c1:
  assumes [register]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows \<open>(pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> o\<^sub>C\<^sub>L pauliX\<guillemotright>\<lbrakk>B1\<rbrakk> o\<^sub>C\<^sub>L proj |1\<rangle>\<guillemotright>\<lbrakk>C1\<rbrakk> o\<^sub>C\<^sub>L proj |1\<rangle>\<guillemotright>\<lbrakk>A1\<rbrakk>) *\<^sub>S quantum_equality_full id_cblinfun \<lbrakk>C1, A1, B1\<rbrakk> (hadamard \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op* o\<^sub>C\<^sub>L CNOT \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L assoc_op o\<^sub>C\<^sub>L addState EPR) \<lbrakk>A2\<rbrakk> \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>\<close>
  apply prepare_for_code
  by eval

end
