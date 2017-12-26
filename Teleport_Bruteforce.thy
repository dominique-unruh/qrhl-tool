theory Teleport_Bruteforce
  imports Teleport (* TODO: Only import QRHL_Protocol *)
begin

lemma [simp]: "isometry (1 / sqrt2 \<cdot> H')" sorry

declare [[code drop: UNIV]]
declare enum_class.UNIV_enum[code]

(* 
(* lemma [code]: "UNIV = set (Enum.enum)" by (fact enum_class.UNIV_enum) *)
definition "test = (INF x::bit. (top::bit subspace))"
export_code test in SML module_name Bla file "test.ML" 
value test

 *)





lemma teleport_bruteforce:
  assumes qvars[simp]: "distinct_qvars \<lbrakk>C1,A1,B1,A2\<rbrakk>"
  shows "\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<le> (\<CC>\<ll>\<aa>[isometry CNOT] \<sqinter> ((CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk>)* \<cdot> (\<CC>\<ll>\<aa>[isometry H] \<sqinter> ((H\<guillemotright>\<lbrakk>C1\<rbrakk>)* \<cdot> (\<CC>\<ll>\<aa>[mtotal computational_basis] \<sqinter> (INF z. \<CC>\<ll>\<aa>[mtotal computational_basis] \<sqinter> (INF za. (\<CC>\<ll>\<aa>[z \<noteq> 1] + \<CC>\<ll>\<aa>[isometry X] \<sqinter> ((X\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> ((\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry Z] \<sqinter> ((Z\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> (Z\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> top)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) \<sqinter> (X\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> top)))) \<sqinter> (\<CC>\<ll>\<aa>[z = 1] + (\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry Z] \<sqinter> ((Z\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> (Z\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> top)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>)) \<sqinter> (mproj computational_basis za\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> top) + ortho (mproj computational_basis za\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> top)) \<sqinter> (mproj computational_basis z\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> top) + ortho (mproj computational_basis z\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> top)) \<sqinter> (H\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> top))) \<sqinter> (CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> top)))) \<div> EPR\<guillemotright>\<lbrakk>A1, B1\<rbrakk>"
proof -
  have                               "distinct_qvars \<lbrakk>A1,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>B1,A1\<rbrakk>"                              and "distinct_qvars \<lbrakk>B1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>B1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>C1,A1\<rbrakk>" and "distinct_qvars \<lbrakk>C1,B1\<rbrakk>"                              and "distinct_qvars \<lbrakk>C1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>A2,A1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro: distinct_qvars_swap)
  note colocals = this distinct_qvars_split1 distinct_qvars_split2
  ML_prf {* val goal = Unsynchronized.ref @{term 7}; fun setgoal x = (goal := x) *}
  show ?thesis
    apply (auto simp: prepare_for_code colocals assoc_right)
    by eval
qed

end