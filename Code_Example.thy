theory Code_Example
  imports QRHL
begin

lemma 
  assumes[simp]: "declared_qvars \<lbrakk>q1,q2\<rbrakk>"
  shows "span {EPR} \<guillemotright> \<lbrakk>q1,q2\<rbrakk> \<le> span {ket (0,0), ket (1,1)} \<guillemotright> \<lbrakk>q1,q2\<rbrakk>"
  apply (auto simp: prepare_for_code)
  by eval

lemma 
  assumes[simp]: "declared_qvars \<lbrakk>q1,q2\<rbrakk>"
  shows "span {EPR} \<guillemotright> \<lbrakk>q1,q2\<rbrakk> \<le> span {ket (0,0), ket (1,1)} \<guillemotright> \<lbrakk>q2,q1\<rbrakk>"
  apply (auto simp: prepare_for_code)
  by eval

lemma 
  assumes[simp]: "declared_qvars \<lbrakk>q1,q2\<rbrakk>"
  shows "span {ket (0::bit,0::bit)} \<guillemotright> \<lbrakk>q1,q2\<rbrakk> \<le> span {ket (0)} \<guillemotright> \<lbrakk>q1\<rbrakk>"
  apply (auto simp: prepare_for_code)
  by eval

end
