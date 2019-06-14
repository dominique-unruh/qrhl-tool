theory Teleport_Terse
  imports QRHL.QRHL "../isabelle-thys/Code_Hacks"
begin

(* lemma teleport_terse:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows "\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<le> \<CC>\<ll>\<aa>[norm EPR = 1] \<sqinter> (\<CC>\<ll>\<aa>[isometry CNOT] \<sqinter> ((CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk>)* \<cdot> (\<CC>\<ll>\<aa>[isometry hadamard] \<sqinter> ((hadamard\<guillemotright>\<lbrakk>C1\<rbrakk>)* \<cdot> ((let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>z. let P = mproj M z\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> \<top> in (let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>za. let P = mproj M za\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> \<top> in (\<CC>\<ll>\<aa>[z \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliX] \<sqinter> ((pauliX\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> ((\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> ((pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> (pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) \<sqinter> (pauliX\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[z = 1] + (\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> ((pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> (pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>)) \<sqinter> P + ortho P)) \<sqinter> P + ortho P)) \<sqinter> (hadamard\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> \<top>))) \<sqinter> (CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> \<top>)))) \<div> EPR\<guillemotright>\<lbrakk>A1, B1\<rbrakk>"
  apply (simp add: prepare_for_code)
  using [[show_sorts]]
  (* apply (rule mark_for_let_simprocE) *)
  (* apply simp *)
  by eval *)

 
ML \<open>
fun let_simproc _ ctxt ct =
  SOME ((Conv.rewr_conv @{thm mark_for_let_simproc_def}
         then_conv 
         fixup_code_conv ctxt)
        ct)
\<close>


local_setup \<open>
fn ctxt => ctxt addsimprocs [Simplifier.make_simproc ctxt "let" {lhss=[\<^term>\<open>mark_for_let_simproc x\<close>], proc=let_simproc}]
\<close>


lemma teleport_terse:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows "\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<le> \<CC>\<ll>\<aa>[norm EPR = 1] \<sqinter> (\<CC>\<ll>\<aa>[isometry CNOT] \<sqinter> ((CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk>)* \<cdot> (\<CC>\<ll>\<aa>[isometry hadamard] \<sqinter> ((hadamard\<guillemotright>\<lbrakk>C1\<rbrakk>)* \<cdot> ((let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>z. let P = mproj M z\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> \<top> in (let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>za. let P = mproj M za\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> \<top> in (\<CC>\<ll>\<aa>[z \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliX] \<sqinter> ((pauliX\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> ((\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> ((pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> (pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) \<sqinter> (pauliX\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[z = 1] + (\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> ((pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> (pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>)) \<sqinter> P + ortho P)) \<sqinter> P + ortho P)) \<sqinter> (hadamard\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> \<top>))) \<sqinter> (CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> \<top>)))) \<div> EPR\<guillemotright>\<lbrakk>A1, B1\<rbrakk>"
  apply (simp add: prepare_for_code)
  using [[show_sorts]]
  apply (tactic \<open>CONVERSION (Conv.arg_conv (fixup_code_conv \<^context>)) 1\<close>) 
  using [[ML_source_trace,ML_exception_debugger,ML_exception_trace]]
  apply normalization
  apply eval

end

