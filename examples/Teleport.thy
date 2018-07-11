theory Teleport
  imports QRHL
begin

lemma assoc_op_lift_aux:
  fixes U :: "(('c \<times> 'd) \<times> 'e, ('c \<times> 'd) \<times> 'e) bounded" and Q R S
  assumes "distinct_qvars (variable_concat Q R)" and "distinct_qvars (variable_concat R S)" and "distinct_qvars (variable_concat Q S)"
  defines "V == assoc_op* \<cdot> U \<cdot> assoc_op"
  shows
    "U\<guillemotright>(variable_concat (variable_concat Q R) S) = V\<guillemotright>(variable_concat Q (variable_concat R S))"
  using assms by (metis (no_types, lifting) V_def adjoint_twice distinct_qvars_split2 distinct_qvars_swap qvar_trafo_adj qvar_trafo_assoc_op qvar_trafo_bounded)

lemma assoc_replace: 
  fixes A B C D :: "(_,_) bounded"
  assumes "A \<cdot> B = C"
  shows "D \<cdot> A \<cdot> B = D \<cdot> C"
  by (simp add: timesOp_assoc assms) 

lemma teleport_goal1:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows
    "quantum_equality_full (addState EPR*) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>
      \<le> CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> (hadamard\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> 
          quantum_equality_full (addState EPR* \<cdot> (assoc_op* \<cdot> (CNOT \<otimes> idOp \<cdot> (assoc_op \<cdot> hadamard \<otimes> idOp)))) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>)"
proof -
  have hadamard: "hadamard \<otimes> idOp \<cdot> hadamard \<otimes> idOp = idOp" by simp
  have CNOT: "CNOT \<otimes> idOp \<cdot> CNOT \<otimes> idOp = idOp" by simp
  show ?thesis
    by (simp add: distinct_qvars_split1 distinct_qvars_split2 timesOp_assoc[symmetric] assoc_op_lift_aux
        lift_extendR[where U=hadamard and R="\<lbrakk>A1,B1\<rbrakk>"] lift_extendR[where U=CNOT and R="\<lbrakk>B1\<rbrakk>"]
        assoc_replace[OF hadamard] assoc_replace[OF UadjU] assoc_replace[OF CNOT] assoc_replace[OF adjUU])
qed

lemma teleport_goal2_a0c0:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows "Proj (span {ket 0})\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> Proj (span {ket 0})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
                 quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (hadamard \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op 
                                     \<cdot> addState EPR) \<lbrakk>A2\<rbrakk>
       \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>"
  apply (simp add: prepare_for_code)
  by eval


lemma teleport_goal2_a0c1:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows "pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> Proj (span {ket 1})\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> Proj (span {ket 0})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
                 quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (hadamard \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op 
                                     \<cdot> addState EPR) \<lbrakk>A2\<rbrakk>
       \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>"
proof -
  show ?thesis
    apply (simp add: prepare_for_code)
    by eval
qed

lemma teleport_goal2_a1c0:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows "pauliX\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> Proj (span {ket 0})\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> Proj (span {ket 1})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
                 quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (hadamard \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op 
                                     \<cdot> addState EPR) \<lbrakk>A2\<rbrakk>
       \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>"
  apply (simp add: prepare_for_code)
  by eval

lemma teleport_goal2_a1c1:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows "pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> pauliX\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> Proj (span {ket 1})\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> Proj (span {ket 1})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
                 quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (hadamard \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op 
                                     \<cdot> addState EPR) \<lbrakk>A2\<rbrakk>
       \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>"
  apply (simp add: prepare_for_code)
  by eval

end


