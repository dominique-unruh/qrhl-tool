theory Teleport_Terse
  imports QRHL.QRHL
begin

lemma teleport_terse:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows "\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<le> \<CC>\<ll>\<aa>[norm EPR = 1] \<sqinter> (\<CC>\<ll>\<aa>[isometry CNOT] \<sqinter> ((CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk>)* \<cdot> (\<CC>\<ll>\<aa>[isometry hadamard] \<sqinter> ((hadamard\<guillemotright>\<lbrakk>C1\<rbrakk>)* \<cdot> ((let meas = computational_basis in \<CC>\<ll>\<aa>[mtotal meas] \<sqinter> (\<Sqinter>z. (let meas = computational_basis in \<CC>\<ll>\<aa>[mtotal meas] \<sqinter> (\<Sqinter>za. (\<CC>\<ll>\<aa>[z \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliX] \<sqinter> ((pauliX\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> ((\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> ((pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> (pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) \<sqinter> (pauliX\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[z = 1] + (\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> ((pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> (pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>)) \<sqinter> (mproj meas za\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> \<top>) + ortho (mproj meas za\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> \<top>))) \<sqinter> (mproj meas z\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> \<top>) + ortho (mproj meas z\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> \<top>))) \<sqinter> (hadamard\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> \<top>))) \<sqinter> (CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> \<top>)))) \<div> EPR\<guillemotright>\<lbrakk>A1, B1\<rbrakk>"
  apply (simp add: prepare_for_code)
  by eval

end
