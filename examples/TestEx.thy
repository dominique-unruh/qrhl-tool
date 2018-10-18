theory TestEx
  imports QRHL.QRHL
begin

lemma aux:
  assumes [simp]: "declared_qvars \<lbrakk>q1,q2\<rbrakk>"
  shows "(\<forall>x::bit. \<lbrakk>q1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2\<rbrakk> \<le> \<lbrakk>q1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2\<rbrakk> \<sqinter> (Complex_L2.span {ket x}\<guillemotright>\<lbrakk>q1\<rbrakk> \<sqinter> Complex_L2.span {ket x}\<guillemotright>\<lbrakk>q2\<rbrakk>) + ortho (Complex_L2.span {ket x})\<guillemotright>\<lbrakk>q1\<rbrakk> + ortho (Complex_L2.span {ket x})\<guillemotright>\<lbrakk>q2\<rbrakk>)"
  apply (simp add: prepare_for_code)
  by eval

end