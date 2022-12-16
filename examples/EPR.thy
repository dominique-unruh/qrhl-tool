theory EPR
  imports QRHL.QRHL
begin

declare ETTS.rep_in_S[simp del]
declare ETTS.rep_inverse[simp del]
declare ETTS.Abs_inverse[simp del]

lemma joint_measure_aux:
  fixes q1 :: "(bit, qu \<times> qu) qregister" and r1 :: "(bit, qu \<times> qu) qregister" and q2 :: "(bit, qu \<times> qu) qregister" and r2 :: "(bit, qu \<times> qu) qregister"
  assumes [simp]: \<open>declared_qvars \<lbrakk>q1, r1, q2, r2\<rbrakk>\<close>
  shows "\<forall>a b. \<lbrakk>q1, r1\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>q2, r2\<rbrakk>\<^sub>q \<le> apply_qregister_space \<lbrakk>q1, r1\<rbrakk>\<^sub>q (ccspan {|(a::bit, b::bit)\<rangle>}) \<sqinter> apply_qregister_space \<lbrakk>q2, r2\<rbrakk>\<^sub>q (ccspan {|(a, b)\<rangle>}) \<squnion> - apply_qregister_space \<lbrakk>q1, r1\<rbrakk>\<^sub>q (ccspan {|(a, b)\<rangle>}) \<squnion> - apply_qregister_space \<lbrakk>q2, r2\<rbrakk>\<^sub>q (ccspan {|(a, b)\<rangle>})"
  sorry

(* lemma joint_measure_aux:
  fixes q1 :: "(bit, qu \<times> qu) qregister" and r2 :: "(bit, qu \<times> qu) qregister" and q2 :: "(bit, qu \<times> qu) qregister" and r :: "(bit, qu) qregister" and q :: "(bit, qu) qregister" and r1 :: "(bit, qu \<times> qu) qregister"
  assumes [simp]: \<open>declared_qvars \<lbrakk>q, r1, r2, r, q1, q2\<rbrakk>\<close>
  shows "\<lbrakk>q1::(bit, qu \<times> qu) qregister, r1::(bit, qu \<times> qu) qregister\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>q2, r2\<rbrakk>\<^sub>q \<le> \<CC>\<ll>\<aa>[((\<lambda>m. computational_basis)::cl \<times> cl \<Rightarrow> (bit \<times> bit, _) measurement) = (\<lambda>m. computational_basis)] \<sqinter> qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q \<lbrakk>q::(bit, qu) qregister, r::(bit, qu) qregister\<rbrakk>\<^sub>q \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q \<lbrakk>q, r\<rbrakk>\<^sub>q \<sqinter> (\<Sqinter>z. \<CC>\<ll>\<aa>[z = z] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q \<lbrakk>q, r\<rbrakk>\<^sub>q) (mproj computational_basis z) *\<^sub>S \<top>) \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q \<lbrakk>q, r\<rbrakk>\<^sub>q) (mproj computational_basis z) *\<^sub>S \<top>) + - (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q \<lbrakk>q, r\<rbrakk>\<^sub>q) (mproj computational_basis z) *\<^sub>S \<top>) + - (apply_qregister (qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q \<lbrakk>q, r\<rbrakk>\<^sub>q) (mproj computational_basis z) *\<^sub>S \<top>))"
  sorry *)


(* lemma joint_measure_aux:
  assumes [register]: "declared_qvars \<lbrakk>q1,r1,q2,r2\<rbrakk>"
  shows \<open>\<forall>(a::bit) (b::bit). \<lbrakk>q1, r1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2, r2\<rbrakk> \<le> \<lbrakk>q1, r1\<rbrakk> =\<^sub>\<qq> |(a, b)\<rangle> \<sqinter> \<lbrakk>q2, r2\<rbrakk> =\<^sub>\<qq> |(a, b)\<rangle> \<squnion> \<lbrakk>q1, r1\<rbrakk> \<in>\<^sub>\<qq> (- ccspan { |(a, b)\<rangle> }) \<squnion> \<lbrakk>q2, r2\<rbrakk> \<in>\<^sub>\<qq> (- ccspan { |(a, b)\<rangle> })\<close>
(*   apply prepare_for_code
  by eval *)
  sorry *)

lemma final_goal:
  (* fixes q :: "(bit, qu) qregister" and r :: "(bit, qu) qregister" *)
  assumes [register]: \<open>qregister \<lbrakk>q, r\<rbrakk>\<close>
  shows "apply_qregister_space (qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q \<lbrakk>q, r\<rbrakk>\<^sub>q) (ccspan {EPR}) \<le> (apply_qregister (qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q r) hadamard *\<^sub>S apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q) hadamard *\<^sub>S \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q q, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q r\<rbrakk>\<^sub>q) \<div> EPR\<guillemotright>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q \<lbrakk>q, r\<rbrakk>\<^sub>q"
  sorry

term \<open>\<mu>\<close>

(* lemma final_goal:
  assumes [register]: "declared_qvars \<lbrakk>q1,r1,q2,r2\<rbrakk>"
  shows \<open>\<lbrakk>q2, r2\<rbrakk> =\<^sub>\<qq> EPR \<sqinter> \<lbrakk>q1, r1\<rbrakk> =\<^sub>\<qq> EPR \<le> hadamard\<guillemotright>\<lbrakk>r2\<rbrakk> *\<^sub>S hadamard\<guillemotright>\<lbrakk>q1\<rbrakk> *\<^sub>S \<lbrakk>q1, r1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2, r2\<rbrakk>\<close>
  apply prepare_for_code
  by eval *)

end
