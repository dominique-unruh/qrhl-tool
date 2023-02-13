theory Test_QRHL_Core
  imports UnitTest "QRHL.QRHL_Core"
begin

experiment
  fixes q :: "(bit, qu) qregister" and r :: "(bit, qu) qregister"
  assumes [register]: \<open>declared_qvars \<lbrakk>q, r\<rbrakk>\<close>
begin

abbreviation \<open>q1 \<equiv> qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q\<close> 
abbreviation \<open>q2 \<equiv> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q q\<close>
abbreviation \<open>r1 \<equiv> qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q r\<close> 
abbreviation \<open>r2 \<equiv> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q r\<close>

ML \<open>
fun translate_to_index_registers_conv_with_opts ctxt = Prog_Variables.translate_to_index_registers_conv ctxt Prog_Variables.translate_to_index_registers_conv_default_options
\<close>

(* Checks if translate_to_index_registers_conv works with indexed-registers, too. *)
ML \<open>
assert_aconv_conv true (translate_to_index_registers_conv_with_opts \<^context>)
  \<^cterm>\<open>\<lbrakk>q1, r1\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>q2, r2\<rbrakk>\<^sub>q\<close>
  \<^term>\<open>apply_qregister_space \<lbrakk>q1, r1, q2, r2\<rbrakk>\<^sub>q
      (\<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>\<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q)\<close>
\<close>

ML \<open>
assert_aconv_conv true (translate_to_index_registers_conv_with_opts \<^context>)
  \<^cterm>\<open>apply_qregister_space q Z \<div> ket 0\<guillemotright>\<lbrakk>q\<rbrakk>\<^sub>q\<close>
  \<^term>\<open>apply_qregister_space (qregister_chain q qregister_id)
      (apply_qregister_space qregister_id Z \<div> |0\<rangle>\<guillemotright>qregister_id)\<close>
\<close>

end

end
