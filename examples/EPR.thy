theory EPR
  imports QRHL.QRHL
begin

lemma joint_measure_aux:
  assumes [simp]: "declared_qvars \<lbrakk>q1,r1,q2,r2\<rbrakk>"
  shows "\<forall>(a::bit) (b::bit). \<lbrakk>q1, r1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2, r2\<rbrakk> \<le> ccspan {ket (a, b)}\<guillemotright>\<lbrakk>q1, r1\<rbrakk> \<sqinter> ccspan {ket (a, b)}\<guillemotright>\<lbrakk>q2, r2\<rbrakk> \<squnion> (- ccspan {ket (a, b)})\<guillemotright>\<lbrakk>q1, r1\<rbrakk> \<squnion> (- ccspan {ket (a, b)})\<guillemotright>\<lbrakk>q2, r2\<rbrakk>"
  apply (simp add: prepare_for_code)
  by eval

lemma final_goal:
  assumes [simp]: "declared_qvars \<lbrakk>q1,r1,q2,r2\<rbrakk>"
    shows "ccspan {EPR}\<guillemotright>\<lbrakk>q2, r2\<rbrakk> \<sqinter> ccspan {EPR}\<guillemotright>\<lbrakk>q1, r1\<rbrakk> \<le> hadamard\<guillemotright>\<lbrakk>r2\<rbrakk> \<cdot> (hadamard\<guillemotright>\<lbrakk>q1\<rbrakk> \<cdot> \<lbrakk>q1, r1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2, r2\<rbrakk>)"
  apply (simp add: prepare_for_code)
  by eval

end
