theory Teleport_Terse
  imports QRHL.QRHL
begin

lemma [prepare_for_code]: "vec_subspace_of (let x = y in z x) = (let x = y in vec_subspace_of (z x))"
  by auto
lemma [prepare_for_code]: "mat_of_l2bounded (let x = y in z x) = (let x = y in mat_of_l2bounded (z x))"
  by auto
lemma [prepare_for_code]: "vec_of_ell2 (let x = y in z x) = (let x = y in vec_of_ell2 (z x))"
  by auto

lemma [prepare_for_code]: 
  fixes M :: "'a::basis_enum linear_space set"
  shows "vec_subspace_of (Inf M) = Inf_vec_subspace (canonical_basis_length TYPE('a)) (vec_subspace_of ` M)"
  sorry

lemma [prepare_for_code]:
  "vec_subspace_of (inf A B) = inf (vec_subspace_of A) (vec_subspace_of B)"
  sorry

lemma [prepare_for_code]:
  "vec_subspace_of ` range f = range (\<lambda>x. vec_subspace_of (f x))"
  by (fact image_image)

lemma [prepare_for_code]:
  "vec_subspace_of (if x then A else B) = (if x then vec_subspace_of A else vec_subspace_of B)"
  by auto
lemma [prepare_for_code]:
  "mat_of_l2bounded (if x then A else B) = (if x then mat_of_l2bounded A else mat_of_l2bounded B)"
  by auto
lemma [prepare_for_code]:
  "vec_of_ell2 (if x then A else B) = (if x then vec_of_ell2 A else vec_of_ell2 B)"
  by auto

lemma rewrite_mark: "x = undefined \<Longrightarrow> x = undefined" by simp

lemma xxx: "vec_subspace_of (a+b) = undefined" sorry

lemma [prepare_for_code]:
  fixes S :: "'a::basis_enum set"
  shows "vec_subspace_of (Complex_L2.span S) = 
    mk_vec_subspace (canonical_basis_length TYPE('a), vec_of_ell2 ` S)"
  sorry

lemma teleport_terse:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows "\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<le> \<CC>\<ll>\<aa>[norm EPR = 1] \<sqinter> (\<CC>\<ll>\<aa>[isometry CNOT] \<sqinter> ((CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk>)* \<cdot>
 (\<CC>\<ll>\<aa>[isometry hadamard] \<sqinter> ((hadamard\<guillemotright>\<lbrakk>C1\<rbrakk>)* \<cdot> ((let M = computational_basis in
 \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>z. let P = mproj M z\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> \<top> in (let M = computational_basis 
in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>za. let P = mproj M za\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> \<top> in (\<CC>\<ll>\<aa>[z \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliX]
 \<sqinter> ((pauliX\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> ((\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> ((pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> 
\<sqinter> (pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) \<sqinter> (pauliX\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[z = 1] 
+ (\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> ((pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> (pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> 
\<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>)) \<sqinter> P + ortho P)) \<sqinter> P + ortho P)) \<sqinter> (hadamard\<guillemotright>\<lbrakk>C1\<rbrakk>
 \<cdot> \<top>))) \<sqinter> (CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> \<top>)))) \<div> EPR\<guillemotright>\<lbrakk>A1, B1\<rbrakk>"
  apply (simp add: prepare_for_code cong del: if_cong)
  (* apply (rewrite at "vec_subspace_of _" rewrite_mark) *)

  by eval (* Takes forever. *)

end
