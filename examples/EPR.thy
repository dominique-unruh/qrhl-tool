theory EPR
  imports QRHL.QRHL
begin

lemma joint_measure_aux:
  assumes [simp,register]: "declared_qvars \<lbrakk>q1,r1,q2,r2\<rbrakk>"
  shows \<open>\<forall>(a::bit) (b::bit). \<lbrakk>q1, r1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2, r2\<rbrakk> \<le> \<lbrakk>q1, r1\<rbrakk> =\<^sub>\<qq> |(a, b)\<rangle> \<sqinter> \<lbrakk>q2, r2\<rbrakk> =\<^sub>\<qq> |(a, b)\<rangle> \<squnion> \<lbrakk>q1, r1\<rbrakk> \<in>\<^sub>\<qq> (- ccspan { |(a, b)\<rangle> }) \<squnion> \<lbrakk>q2, r2\<rbrakk> \<in>\<^sub>\<qq> (- ccspan { |(a, b)\<rangle> })\<close>
  apply prepare_for_code
  by eval

lemma final_goal:
  assumes [simp,register]: "declared_qvars \<lbrakk>q1,r1,q2,r2\<rbrakk>"
  shows \<open>\<lbrakk>q2, r2\<rbrakk> =\<^sub>\<qq> EPR \<sqinter> \<lbrakk>q1, r1\<rbrakk> =\<^sub>\<qq> EPR \<le> hadamard\<guillemotright>\<lbrakk>r2\<rbrakk> *\<^sub>S hadamard\<guillemotright>\<lbrakk>q1\<rbrakk> *\<^sub>S \<lbrakk>q1, r1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2, r2\<rbrakk>\<close>
  apply prepare_for_code
  by eval

end
