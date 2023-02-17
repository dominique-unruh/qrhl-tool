theory EPR
  imports QRHL.QRHL
begin

(* TODO: Make more pretty *)
lemma joint_measure_aux:
  fixes q :: "(bit, qu) qregister" and r :: "(bit, qu) qregister"
  assumes [register]: \<open>qregister \<lbrakk>q, r\<rbrakk>\<close>
  shows "\<forall>a b. \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q \<le> apply_qregister_space \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q (ccspan {|(a::bit, b::bit)\<rangle>}) \<sqinter> apply_qregister_space \<lbrakk>qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q (ccspan {|(a, b)\<rangle>}) \<squnion> apply_qregister_space \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q (- ccspan {|(a, b)\<rangle>}) \<squnion> apply_qregister_space \<lbrakk>qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q (- ccspan {|(a, b)\<rangle>})"
  (* apply translate_to_index_registers (* TODO remove *) *)
  apply prepare_for_code
  by eval

(* TODO: Make more pretty *)
lemma final_goal:
  fixes q :: "(bit, qu) qregister" and r :: "(bit, qu) qregister"
  assumes [register]: \<open>declared_qvars \<lbrakk>q, r\<rbrakk>\<close>
  shows \<open>apply_qregister_space \<lbrakk>qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q (ccspan {EPR}) \<sqinter> apply_qregister_space \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q (ccspan {EPR}) \<le> apply_qregister (qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q r) hadamard *\<^sub>S apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q) hadamard *\<^sub>S \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q\<close>
  apply prepare_for_code
  by eval

end
