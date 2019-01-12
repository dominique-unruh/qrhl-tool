theory TestEx 
  imports QRHL.QRHL 
begin

lemma xxxx:
  assumes [simp]: "declared_qvars \<lbrakk>q1,r1,q2,r2\<rbrakk>"
  shows "(\<Sqinter>z::bit*bit. let ebar = mproj computational_basis z\<guillemotright>\<lbrakk>q1, r1\<rbrakk> \<cdot> \<top>; fbar = mproj computational_basis z\<guillemotright>\<lbrakk>q2, r2\<rbrakk> \<cdot> \<top> in \<CC>\<ll>\<aa>[z = z] \<sqinter> ebar \<sqinter> fbar + ortho ebar + ortho fbar) = Cla[True]"
  apply (simp add: prepare_for_code)
  by eval

end
