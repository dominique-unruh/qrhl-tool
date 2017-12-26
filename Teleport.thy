theory Teleport
  imports QRHL_Protocol
begin

lemma assoc_op_lift_aux:
  fixes U :: "(('c \<times> 'd) \<times> 'e, ('c \<times> 'd) \<times> 'e) bounded" and Q R S
  assumes "distinct_qvars (qvariable_concat Q R)" and "distinct_qvars (qvariable_concat R S)" and "distinct_qvars (qvariable_concat Q S)"
  defines "V == assoc_op* \<cdot> U \<cdot> assoc_op"
  shows
    "U\<guillemotright>(qvariable_concat (qvariable_concat Q R) S) = V\<guillemotright>(qvariable_concat Q (qvariable_concat R S))"
  using assms by (metis (no_types, lifting) V_def adjoint_twice distinct_qvars_split2 distinct_qvars_swap qvar_trafo_adj qvar_trafo_assoc_op qvar_trafo_bounded)

lemma assoc_replace: 
  fixes A B C D :: "(_,_) bounded"
  assumes "A \<cdot> B = C"
  shows "D \<cdot> A \<cdot> B = D \<cdot> C"
  by (simp add: timesOp_assoc assms) 

lemma teleport_goal1:
  assumes[simp]: "distinct_qvars \<lbrakk>C1,A1\<rbrakk> \<and> distinct_qvars \<lbrakk>A1,B1\<rbrakk> \<and> distinct_qvars \<lbrakk>C1,B1\<rbrakk> \<and> distinct_qvars \<lbrakk>A1, C1\<rbrakk> \<and> distinct_qvars \<lbrakk>B1, C1\<rbrakk>
                  \<and> distinct_qvars \<lbrakk>C1, A2\<rbrakk> \<and> distinct_qvars \<lbrakk>A1, A2\<rbrakk> \<and> distinct_qvars \<lbrakk>B1, A2\<rbrakk> \<and> distinct_qvars \<lbrakk>B1, A1\<rbrakk>"
  shows
    "quantum_equality_full (addState EPR*) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>
      \<le> CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> (H\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> quantum_equality_full (addState EPR* \<cdot> (assoc_op* \<cdot> (CNOT \<otimes> idOp \<cdot> (assoc_op \<cdot> H \<otimes> idOp)))) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>)"
proof -
  have H: "H \<otimes> idOp \<cdot> H \<otimes> idOp = idOp" by simp
  have CNOT: "CNOT \<otimes> idOp \<cdot> CNOT \<otimes> idOp = idOp" by simp
  show ?thesis
    by (simp add: distinct_qvars_split1 distinct_qvars_split2 timesOp_assoc[symmetric] assoc_op_lift_aux
        lift_extendR[where U=H and R="\<lbrakk>A1,B1\<rbrakk>"] lift_extendR[where U=CNOT and R="\<lbrakk>B1\<rbrakk>"]
        assoc_replace[OF H] assoc_replace[OF UadjU] assoc_replace[OF CNOT] assoc_replace[OF adjUU])
qed

lemma teleport_goal2_a0c0:
  fixes C1 A1 B1 A2 :: "bit qvariable"
  assumes qvars[simp]: "distinct_qvars \<lbrakk>C1,A1,B1,A2\<rbrakk>"
  shows "Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> (Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
                 quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op 
                                     \<cdot> addState (state_to_vector EPR)) \<lbrakk>A2\<rbrakk>)
       \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>"
proof -
  have                              "distinct_qvars \<lbrakk>A1,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>B1,A1\<rbrakk>"                             and "distinct_qvars \<lbrakk>B1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>B1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>C1,A1\<rbrakk>" and "distinct_qvars \<lbrakk>C1,B1\<rbrakk>"                             and "distinct_qvars \<lbrakk>C1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>A2,A1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro: distinct_qvars_swap)
  note colocals = this distinct_qvars_split1 distinct_qvars_split2
  show ?thesis
    apply (auto simp: prepare_for_code colocals assoc_right)
    by eval
qed

lemma teleport_goal2_a0c1:
  fixes C1 A1 B1 A2 :: "bit qvariable"
  assumes qvars[simp]: "distinct_qvars \<lbrakk>C1,A1,B1,A2\<rbrakk>"
  shows "Z\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> (Proj (span {basis_vector 1})\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> (Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
                 quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op 
                                     \<cdot> addState (state_to_vector EPR)) \<lbrakk>A2\<rbrakk>))
       \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>"
proof -
  have                               "distinct_qvars \<lbrakk>A1,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>B1,A1\<rbrakk>"                              and "distinct_qvars \<lbrakk>B1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>B1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>C1,A1\<rbrakk>" and "distinct_qvars \<lbrakk>C1,B1\<rbrakk>"                              and "distinct_qvars \<lbrakk>C1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>A2,A1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro: distinct_qvars_swap)
  note colocals = this distinct_qvars_split1 distinct_qvars_split2
  show ?thesis
    apply (auto simp: prepare_for_code colocals assoc_right)
    by eval
qed

lemma teleport_goal2_a1c0:
  fixes C1 A1 B1 A2 :: "bit qvariable"
  assumes qvars[simp]: "distinct_qvars \<lbrakk>C1,A1,B1,A2\<rbrakk>"
  shows "X\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> (Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> (Proj (span {basis_vector 1})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
                 quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op 
                                     \<cdot> addState (state_to_vector EPR)) \<lbrakk>A2\<rbrakk>))
       \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>"
proof -
  have                               "distinct_qvars \<lbrakk>A1,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>B1,A1\<rbrakk>"                              and "distinct_qvars \<lbrakk>B1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>B1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>C1,A1\<rbrakk>" and "distinct_qvars \<lbrakk>C1,B1\<rbrakk>"                              and "distinct_qvars \<lbrakk>C1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>A2,A1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro: distinct_qvars_swap)
  note colocals = this distinct_qvars_split1 distinct_qvars_split2
  show ?thesis
    apply (auto simp: prepare_for_code colocals assoc_right)
    by eval
qed

lemma teleport_goal2_a1c1:
  fixes C1 A1 B1 A2 :: "bit qvariable"
  assumes qvars[simp]: "distinct_qvars \<lbrakk>C1,A1,B1,A2\<rbrakk>"
  shows "Z\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> (X\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> (Proj (span {basis_vector 1})\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> (Proj (span {basis_vector 1})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
                 quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op 
                                     \<cdot> addState (state_to_vector EPR)) \<lbrakk>A2\<rbrakk>)))
       \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>"
proof -
  have                               "distinct_qvars \<lbrakk>A1,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>B1,A1\<rbrakk>"                              and "distinct_qvars \<lbrakk>B1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>B1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>C1,A1\<rbrakk>" and "distinct_qvars \<lbrakk>C1,B1\<rbrakk>"                              and "distinct_qvars \<lbrakk>C1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>A2,A1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro: distinct_qvars_swap)
  note colocals = this distinct_qvars_split1 distinct_qvars_split2
  show ?thesis
    apply (auto simp: prepare_for_code colocals assoc_right)
    by eval
qed

end


