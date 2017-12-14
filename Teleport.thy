theory Teleport
  imports QRHL_Protocol
begin

declare[[quick_and_dirty]]

axiomatization tensorIso :: "('a,'b) bounded \<Rightarrow> ('c,'d) bounded \<Rightarrow> ('a*'c,'b*'d) bounded"
axiomatization where idIso_tensor_idIso[simp]: "tensorIso idOp idOp = idOp"
axiomatization assoc_op :: "('a*'b*'c, ('a*'b)*'c) bounded"
  where unitary_assoc_op[simp]: "unitary assoc_op"
(* axiomatization assoc_op' :: "(('a*'b)*'c, 'a*'b*'c) bounded" *)
axiomatization comm_op :: "('a*'b, 'b*'a) bounded"
  where unitary_comm_op[simp]: "unitary comm_op"
  
consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infix "\<otimes>" 71)
adhoc_overloading tensor tensorIso

lemma tensor_times[simp]: "(U1 \<otimes> U2) \<cdot> (V1 \<otimes> V2) = (U1 \<cdot> V1) \<otimes> (U2 \<cdot> V2)" sorry

axiomatization addState :: "'a state \<Rightarrow> ('b,'b*'a) bounded"
axiomatization where (* TODO: some disjointness conditions *)
  quantum_eq_add_state: "quantum_equality_full U Q V R \<sqinter> span {\<psi>}\<guillemotright>T
             = quantum_equality_full (tensorIso U idOp) (qvariable_concat Q T) (addState \<psi> \<cdot> V) R"
    for U :: "('a,'c) bounded" and V :: "('b,'c) bounded" and \<psi> :: "'d state"
    and Q :: "'a qvariables"    and R :: "'b qvariables"    and T :: "'d qvariables"

axiomatization EPR :: "(bit*bit) state" 

lemma aux1: "A \<le> B + C" if "A \<le> B" for A::predicate
  by (simp add: add_increasing2 that) 

axiomatization colocal_op_pred :: "(mem2,mem2) bounded \<Rightarrow> predicate \<Rightarrow> bool"
axiomatization colocal_op_qvars :: "(mem2,mem2) bounded \<Rightarrow> 'a qvariables \<Rightarrow> bool"
(* axiomatization colocal_op_op :: "(mem2,mem2) bounded \<Rightarrow> (mem2,mem2) bounded \<Rightarrow> bool" *)


lemma applyOpSpace_colocal[simp]:
  fixes U :: "(mem2,mem2) bounded" and S :: predicate
  assumes "colocal_op_pred U S"
  shows "U \<cdot> S = S"
  sorry

(*lemma colocal_op_pred_mult2[simp]:
  assumes "colocal_op_op U V" 
  assumes "colocal_op_pred U S"
  shows "colocal_op_pred U (V\<cdot>S)"
  sorry*)

lemma colocal_op_pred_lift1[simp]:
  fixes Q :: "'a qvariables"
  assumes "colocal S Q"
  shows "colocal_op_pred (U\<guillemotright>Q) S"
  sorry
lemma colocal_op_qvars_lift1[simp]:
  fixes Q :: "'a qvariables"
  assumes "colocal Q R"
  shows "colocal_op_qvars (U\<guillemotright>Q) R"
  sorry
lemma colocal_pred_qvars_lift1[simp]:
  fixes Q :: "'a qvariables"
  assumes "colocal Q R"
  shows "colocal_pred_qvars (S\<guillemotright>Q) R"
  sorry

lemma colocal_pred_qvars_mult[simp]:
  assumes "colocal_op_qvars U Q"
  assumes "colocal_pred_qvars S Q"
  shows "colocal_pred_qvars (U\<cdot>S) Q"
  sorry

lemma colocal_quantum_equality_full[simp]:
  assumes "colocal Q1 Q3" and "colocal Q2 Q3"
  shows "colocal (quantum_equality_full U1 Q1 U2 Q2) Q3"
  sorry

lemma colocal_ortho[simp]: "colocal (ortho S) Q = colocal S Q" sorry

(*
lemma 
  assumes "variable_name B1 = ''B1''" and "variable_name C1 = ''C1''" and "variable_name A2 = ''A2''" and "variable_name A1 = ''A1''"
(* "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>C1\<rbrakk>" and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>C1\<rbrakk>" *)
  shows "\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> span {EPR}\<guillemotright>\<lbrakk>A1, B1\<rbrakk> \<le>
  (INF x. (\<CC>\<ll>\<aa>[x = 0] + CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> (H\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> quantum_equality_full Z \<lbrakk>B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>))
        \<sqinter> (\<CC>\<ll>\<aa>[x = 1] + CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> (H\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>))
        \<sqinter> (CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> (H\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> span {basis_vector x}\<guillemotright>\<lbrakk>B1\<rbrakk>))
        + CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> (H\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> ortho (span {basis_vector x}\<guillemotright>\<lbrakk>B1\<rbrakk>)))
   \<sqinter> (CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> (H\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> span {basis_vector 0}\<guillemotright>\<lbrakk>A1\<rbrakk>))
   + CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> (H\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> ortho (span {basis_vector 0}\<guillemotright>\<lbrakk>A1\<rbrakk>))"
  apply (rule aux1)
  apply (auto simp: quantum_eq_add_state assms)

    apply (simp add: applyOpSpace_colocal assms)
    apply (subst applyOpSpace_colocal) back

  (* using assms apply simp *)
     apply (rule colocal_op_pred_lift1)
     apply (rule colocal_quantum_equality_full)
  using assms apply simp
  using assms apply simp

     apply (rule colocal_pred_qvars_mult)
  apply (rule colocal_op_qvars_lift1
  apply simp
  

*)

lemma lift_extendR:
  assumes "colocal Q R"
  shows "U\<guillemotright>Q = (U\<otimes>idOp)\<guillemotright>(qvariable_concat Q R)"
  sorry

lemma lift_extendL:
  assumes "colocal Q R"
  shows "U\<guillemotright>Q = (idOp\<otimes>U)\<guillemotright>(qvariable_concat R Q)"
  sorry

lemma tensor_adjoint[simp]: "adjoint (U\<otimes>V) = (adjoint U) \<otimes> (adjoint V)" sorry

lemma sort_lift[simp]:
  fixes U :: "(('c \<times> 'd) \<times> 'e, ('c \<times> 'd) \<times> 'e) bounded" and Q R S
  assumes "colocal Q R" and "colocal R S" and "colocal Q S"
  defines "V == assoc_op* \<cdot> U \<cdot> assoc_op"
  shows
    "U\<guillemotright>(qvariable_concat (qvariable_concat Q R) S) = V\<guillemotright>(qvariable_concat Q (qvariable_concat R S))"
  sorry

lemma tensor_unitary[simp]: 
  assumes "unitary U" and "unitary V"
  shows "unitary (U\<otimes>V)"
  sorry

lemma colocal_split1: "colocal (qvariable_concat Q R) S = (colocal Q S \<and> colocal R S)" sorry
lemma colocal_split2: "colocal S (qvariable_concat Q R) = (colocal S Q \<and> colocal S R)" for S :: "'a qvariables" sorry

lemma adjUU[simp]: "isometry U \<Longrightarrow> U* \<cdot> U = idOp" unfolding isometry_def by simp
lemma UadjU[simp]: "unitary U \<Longrightarrow> U \<cdot> U* = idOp" unfolding unitary_def by simp

lemma assoc_replace: 
  fixes C :: "(_,_) bounded"
  assumes "A \<cdot> B = C"
  shows "D \<cdot> A \<cdot> B = D \<cdot> C"
  by (simp add: timesOp_assoc[symmetric] assms) 


axiomatization where
  timesOp_assoc_subspace[simp]: "applyOpSpace (timesOp A B) S = applyOpSpace A (applyOpSpace B S)"

(*lemma assoc_replace':
  fixes C :: "_ subspace"
  assumes "A \<cdot> B = C"
  shows "D \<cdot> A \<cdot> B = D \<cdot> C"
  apply (subst timesOp_assoc_subspace)
  unfolding assms by simp*)

lemma teleport_goal1:
  assumes "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk> \<and> colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk> \<and> colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk>"
  shows
    "quantum_equality_full (addState EPR*) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk> \<le> CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> (H\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> quantum_equality_full (addState EPR* \<cdot> (assoc_op* \<cdot> (CNOT \<otimes> idOp \<cdot> (assoc_op \<cdot> H \<otimes> idOp)))) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>)"
proof -
  have H: "H \<otimes> idOp \<cdot> H \<otimes> idOp = idOp" by simp
  have CNOT: "CNOT \<otimes> idOp \<cdot> CNOT \<otimes> idOp = idOp" by simp
  show ?thesis
    by (simp add: colocal_split1 colocal_split2 assms timesOp_assoc
        lift_extendR[where U=H and R="\<lbrakk>A1,B1\<rbrakk>"] lift_extendR[where U=CNOT and R="\<lbrakk>B1\<rbrakk>"]
        assoc_replace[OF H] assoc_replace[OF UadjU] assoc_replace[OF CNOT] assoc_replace[OF adjUU])
qed

axiomatization Proj :: "'a subspace \<Rightarrow> ('a,'a) bounded" where
  isProjector_Proj[simp]: "isProjector (Proj S)"
and imageOp_Proj[simp]: "applyOpSpace (Proj S) top = S"

lemma move_plus:
  assumes "Proj (ortho C) \<cdot> A \<le> B"
  shows "A \<le> B + C"
  sorry

lemma Proj_lift[simp]: "Proj (S\<guillemotright>Q) = (Proj S)\<guillemotright>Q"
  sorry

lemma teleport_goal2:
  assumes "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk> \<and> colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk> \<and> colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk>"
  shows "quantum_equality_full (addState EPR* \<cdot> (assoc_op* \<cdot> (CNOT \<otimes> idOp \<cdot> (assoc_op \<cdot> H \<otimes> idOp)))) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk> 
         \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> span {basis_vector 0}\<guillemotright>\<lbrakk>A1\<rbrakk> + ortho (span {basis_vector 0}\<guillemotright>\<lbrakk>A1\<rbrakk>)"
  sorry (* TODO *)

end
