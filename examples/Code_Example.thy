theory Code_Example
  imports QRHL.QRHL
begin

lemma 
  assumes[simp]: "declared_qvars \<lbrakk>q1,q2\<rbrakk>"
  shows "Span {EPR} \<guillemotright> \<lbrakk>q1,q2\<rbrakk> \<le> Span {ket (0,0), ket (1,1)} \<guillemotright> \<lbrakk>q1,q2\<rbrakk>"
  apply (simp add: prepare_for_code)
  by eval

lemma 
  assumes[simp]: "declared_qvars \<lbrakk>q1,q2\<rbrakk>"
  shows "Span {EPR} \<guillemotright> \<lbrakk>q1,q2\<rbrakk> \<le> Span {ket (0,0), ket (1,1)} \<guillemotright> \<lbrakk>q2,q1\<rbrakk>"
  apply (simp add: prepare_for_code)
  by eval

lemma 
  assumes[simp]: "declared_qvars \<lbrakk>q1,q2\<rbrakk>"
  shows "Span {ket (0::bit,0::bit)} \<guillemotright> \<lbrakk>q1,q2\<rbrakk> \<le> Span {ket (0)} \<guillemotright> \<lbrakk>q1\<rbrakk>"
  apply (simp add: prepare_for_code)
  by eval

lemma
  assumes[simp]: "declared_qvars \<lbrakk>q1,q2\<rbrakk>"
  shows "CNOT\<guillemotright>\<lbrakk>q1,q2\<rbrakk> \<cdot> hadamard\<guillemotright>\<lbrakk>q1\<rbrakk> \<cdot> Span {ket (0,0)}\<guillemotright>\<lbrakk>q1,q2\<rbrakk> \<le> Span {EPR}\<guillemotright>\<lbrakk>q1,q2\<rbrakk>"
  apply (simp add: prepare_for_code)
  by eval

end
