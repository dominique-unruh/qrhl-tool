theory EPR
  imports QRHL.QRHL
begin

declare ETTS.rep_in_S[simp del]
declare ETTS.rep_inverse[simp del]
declare ETTS.Abs_inverse[simp del]

lemma joint_measure_aux:
  fixes q1 :: "(bit, qu \<times> qu) qregister" and r1 :: "(bit, qu \<times> qu) qregister" and q2 :: "(bit, qu \<times> qu) qregister" and r2 :: "(bit, qu \<times> qu) qregister"
  assumes [simp]: \<open>declared_qvars \<lbrakk>q1, r1, q2, r2\<rbrakk>\<close>
  shows "\<forall>a b. \<lbrakk>q1, r1\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>q2, r2\<rbrakk>\<^sub>q \<le> apply_qregister_space \<lbrakk>q1, r1\<rbrakk>\<^sub>q (ccspan {|(a::bit, b::bit)\<rangle>}) \<sqinter> apply_qregister_space \<lbrakk>q2, r2\<rbrakk>\<^sub>q (ccspan {|(a, b)\<rangle>}) \<squnion> - apply_qregister_space \<lbrakk>q1, r1\<rbrakk>\<^sub>q (ccspan {|(a, b)\<rangle>}) \<squnion> - apply_qregister_space \<lbrakk>q2, r2\<rbrakk>\<^sub>q (ccspan {|(a, b)\<rangle>})"
  sorry

(* lemma final_goal_old: (* TODO remove *)
  assumes [register]: "declared_qvars \<lbrakk>q1,r1,q2,r2\<rbrakk>"
  shows \<open>\<lbrakk>q2, r2\<rbrakk> =\<^sub>\<qq> EPR \<sqinter> \<lbrakk>q1, r1\<rbrakk> =\<^sub>\<qq> EPR \<le> hadamard\<guillemotright>\<lbrakk>r2\<rbrakk> *\<^sub>S hadamard\<guillemotright>\<lbrakk>q1\<rbrakk> *\<^sub>S \<lbrakk>q1, r1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2, r2\<rbrakk>\<close>
  apply prepare_for_code
  by eval *)

(* TODO: Make more pretty *)
lemma final_goal:
  fixes q :: "(bit, qu) qregister" and r :: "(bit, qu) qregister"
  assumes [register]: \<open>declared_qvars \<lbrakk>q, r\<rbrakk>\<close>
  shows \<open>apply_qregister_space \<lbrakk>qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q (ccspan {EPR}) \<sqinter> apply_qregister_space \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q (ccspan {EPR}) \<le> apply_qregister (qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q r) hadamard *\<^sub>S apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q) hadamard *\<^sub>S \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q\<close>
  apply prepare_for_code
  by eval

end
