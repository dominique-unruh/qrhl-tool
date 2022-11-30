theory Code_Example
  imports QRHL.QRHL
begin

lemma 
  assumes[simp]: "declared_qvars \<lbrakk>q1,q2\<rbrakk>"
  shows \<open>\<lbrakk>q1, q2\<rbrakk> =\<^sub>\<qq> EPR  \<le>  \<lbrakk>q1, q2\<rbrakk> \<in>\<^sub>\<qq> ccspan { |(0, 0)\<rangle>, |(1, 1)\<rangle> }\<close>
  apply (simp add: prepare_for_code)
  by eval

lemma 
  assumes[simp]: "declared_qvars \<lbrakk>q1,q2\<rbrakk>"
  shows \<open>\<lbrakk>q1, q2\<rbrakk> =\<^sub>\<qq> EPR  \<le>  \<lbrakk>q2, q1\<rbrakk> \<in>\<^sub>\<qq> ccspan { |(0, 0)\<rangle>, |(1, 1)\<rangle> }\<close>
  apply (simp add: prepare_for_code)
  by eval

lemma 
  assumes[simp]: "declared_qvars \<lbrakk>q1,q2\<rbrakk>"
  shows \<open>\<lbrakk>q1, q2\<rbrakk> =\<^sub>\<qq> |(0::bit, 0::bit)\<rangle>  \<le>  \<lbrakk>q1\<rbrakk> =\<^sub>\<qq> |0\<rangle>\<close>
  apply (simp add: prepare_for_code)
  by eval

lemma
  assumes[simp]: "declared_qvars \<lbrakk>q1,q2\<rbrakk>"
  shows \<open>(CNOT\<guillemotright>\<lbrakk>q1, q2\<rbrakk> o\<^sub>C\<^sub>L hadamard\<guillemotright>\<lbrakk>q1\<rbrakk>)  *\<^sub>S  \<lbrakk>q1, q2\<rbrakk> =\<^sub>\<qq> |(0, 0)\<rangle>  \<le>  \<lbrakk>q1, q2\<rbrakk> =\<^sub>\<qq> EPR\<close>
  apply (simp add: prepare_for_code)
  by eval

end
