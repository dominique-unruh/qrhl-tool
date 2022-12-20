theory Test_QRHL_Core
  imports  UnitTest "QRHL.QRHL_Core"
begin

experiment
  fixes q :: "(bit, qu) qregister" and r :: "(bit, qu) qregister"
  assumes [register]: \<open>declared_qvars \<lbrakk>q, r\<rbrakk>\<close>
begin

abbreviation \<open>q1 \<equiv> qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q\<close> 
abbreviation \<open>q2 \<equiv> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q q\<close>
abbreviation \<open>r1 \<equiv> qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q r\<close> 
abbreviation \<open>r2 \<equiv> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q r\<close>

(* Checks if translate_to_index_registers_conv works with indexed-registers, too. *)
ML \<open>
assert_aconv_conv (translate_to_index_registers_conv \<^context>)
  \<^cterm>\<open>\<lbrakk>q1, r1\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>q2, r2\<rbrakk>\<^sub>q\<close>
  \<^term>\<open>apply_qregister_space \<lbrakk>q1, r1, q2, r2\<rbrakk>\<^sub>q
      (quantum_equality_full (apply_qregister qregister_id id_cblinfun) \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
                             (apply_qregister qregister_id id_cblinfun) \<lbrakk>\<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q)\<close>
\<close>

end

end
