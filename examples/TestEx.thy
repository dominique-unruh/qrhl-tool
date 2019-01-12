theory TestEx 
  imports QRHL.QRHL 
begin

lemma xxx:
  assumes [simp]: "declared_qvars \<lbrakk>q1,r1,q2,r2\<rbrakk>"
  shows "(span{ket 0}\<guillemotright>\<lbrakk>q1\<rbrakk>) = top"
  apply (simp add: prepare_for_code)
  by eval

(* TODO should work! *)
lemma xxx:
  assumes [simp]: "declared_qvars \<lbrakk>q1,r1,q2,r2\<rbrakk>"
  shows "(\<Sqinter>z. let ebar = mproj computational_basis z\<guillemotright>\<lbrakk>q1, r1\<rbrakk> \<cdot> \<top>; fbar = mproj computational_basis z\<guillemotright>\<lbrakk>q2, r2\<rbrakk> \<cdot> \<top> in \<CC>\<ll>\<aa>[z = z] \<sqinter> ebar \<sqinter> fbar + ortho ebar + ortho fbar) = Cla[True]"
  apply (simp add: prepare_for_code)
  by eval

definition "x == 10"

end
