theory Teleport
  imports QRHL_Protocol
begin


declare[[quick_and_dirty]]


lemma sort_lift: (* TODO remove *)
  fixes U :: "(('c \<times> 'd) \<times> 'e, ('c \<times> 'd) \<times> 'e) bounded" and Q R S
  assumes "distinct_qvars (qvariable_concat Q R)" and "distinct_qvars (qvariable_concat R S)" and "distinct_qvars (qvariable_concat Q S)"
  defines "V == assoc_op* \<cdot> U \<cdot> assoc_op"
  shows
    "U\<guillemotright>(qvariable_concat (qvariable_concat Q R) S) = V\<guillemotright>(qvariable_concat Q (qvariable_concat R S))"
  sorry


(* 
lemma assocify_rule:
  assumes "f (g a b) c = h a (l b c)"
  assumes "g a b = d"
  shows "h a (l b c) = f d c"
  using assms by simp *)

(* find_theorems idOp timesOp
thm assocify_rule[where f=timesOp and g=timesOp and h=timesOp and l=timesOp, OF timesOp_assoc] *)

lemma assoc_replace: 
  fixes A B C D :: "(_,_) bounded"
  assumes "A \<cdot> B = C"
  shows "D \<cdot> A \<cdot> B = D \<cdot> C"
  by (simp add: timesOp_assoc assms) 









(* lemma move_plus_ortho:
  assumes "Proj C \<cdot> A \<le> B"
  shows "A \<le> (B\<sqinter>C) + ortho C"
  apply (rule move_plus)
  using assms Proj_leq by auto *)

(* axiomatization where lift_timesOp[simp]: 
  "distinct_qvars Q \<Longrightarrow> S\<guillemotright>Q \<cdot> T\<guillemotright>Q = (S \<cdot> T)\<guillemotright>Q" for S T :: "('a,'a) bounded"   *)

(* TODO: make proj abbrev instead *)
axiomatization where Proj_span1[simp]: "Proj (span {\<psi>}) = proj \<psi>" 





(* declare sqrt2_def[code del] *)





(* lemma [code]: "mat_of_bounded (addState \<psi> :: ('a::enum,'a*'b::enum) bounded) 
  = matrix_tensor (one_mat (CARD('a))) (mat_of_cols (CARD('b)) [vec_of_vector \<psi>])" *)




(* lemma [code]: "SPAN A = (SPAN B :: 'a::enum subspace) \<longleftrightarrow>
  ((SPAN A::'a subspace) \<le> (SPAN B::'a subspace)) \<and> ((SPAN B::'a subspace) \<le> (SPAN A::'a subspace))" by auto *)

(* lemma [code_abbrev]: "ortho (ortho A + ortho B) = A \<sqinter> B" unfolding subspace_sup_plus[symmetric]  *)


(* 
lemma uminus_bounded_def: "(-A) = (-1) \<cdot> A" for A::"(_,_)bounded" sorry  *)





(* TODO: we have a more general version in QRHL_Code. Which? *)
lemma [code]: "Inf (Set_Monad l :: 'a subspace set) = fold inf l top"
  unfolding Set_Monad_def
  by (simp add: Inf_set_fold)


(* lemma test: "1=(1::nat)"
  by eval
ML_command \<open>
  @{thm test} |> Thm.proof_body_of |> Proofterm.all_oracles_of |> map fst |> map @{print}
\<close> *)






(* TODO needed? *)
lemmas qvar_trafo_adj_assoc_mult[simp] = qvar_trafo_mult[OF qvar_trafo_adj[OF qvar_trafo_assoc_op]] 
    

(* 
(* TODO: proof in paper *)
axiomatization where (* TODO: some disjointness conditions *)
  quantum_eq_add_state: "quantum_equality_full U Q V R \<sqinter> span {\<psi>}\<^sub>@T
             = quantum_equality_full (tensorIso U idIso) (qvariables_concat Q T) (addState \<psi> \<cdot> V) R"
    for U :: "('a,'c) isometry" and V :: "('b,'c) isometry" and \<psi> :: "'d state"
    and Q :: "'a qvariables"    and R :: "'b qvariables"    and T :: "'d qvariables"
  *)

lemma quantum_eq_add_state: (* TODO: recover axiom *)
  fixes C1 A1 B1 A2 :: "bit qvariable"
  assumes qvars[simp]: "distinct_qvars \<lbrakk>C1,A1,B1,A2\<rbrakk>"
  shows "\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> span {EPR}\<guillemotright>\<lbrakk>A1, B1\<rbrakk> \<le> quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (addState (state_to_vector EPR)) \<lbrakk>A2\<rbrakk>"
proof -
   have                             "distinct_qvars \<lbrakk>A1,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>B1,A1\<rbrakk>"                             and "distinct_qvars \<lbrakk>B1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>B1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>C1,A1\<rbrakk>" and "distinct_qvars \<lbrakk>C1,B1\<rbrakk>"                             and "distinct_qvars \<lbrakk>C1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>A2,A1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro: distinct_qvars_swap)
  note colocals = this distinct_qvars_split1 distinct_qvars_split2
  show ?thesis
    apply simp
    apply (auto simp: prepare_for_code colocals)
    by eval
qed

lemma teleport_goal1:
  assumes[simp]: "distinct_qvars \<lbrakk>C1,A1\<rbrakk> \<and> distinct_qvars \<lbrakk>A1,B1\<rbrakk> \<and> distinct_qvars \<lbrakk>C1,B1\<rbrakk> \<and> distinct_qvars \<lbrakk>A1, C1\<rbrakk> \<and> distinct_qvars \<lbrakk>B1, C1\<rbrakk>
                  \<and> distinct_qvars \<lbrakk>C1, A2\<rbrakk> \<and> distinct_qvars \<lbrakk>A1, A2\<rbrakk> \<and> distinct_qvars \<lbrakk>B1, A2\<rbrakk> \<and> distinct_qvars \<lbrakk>B1, A1\<rbrakk>"
  shows
    "quantum_equality_full (addState EPR*) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>
      \<le> CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> (H\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> quantum_equality_full (addState EPR* \<cdot> (assoc_op* \<cdot> (CNOT \<otimes> idOp \<cdot> (assoc_op \<cdot> H \<otimes> idOp)))) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>)"
proof -
  have H: "H \<otimes> idOp \<cdot> H \<otimes> idOp = idOp" by simp
  have CNOT: "CNOT \<otimes> idOp \<cdot> CNOT \<otimes> idOp = idOp" by simp
  show ?thesis
    by (simp add: distinct_qvars_split1 distinct_qvars_split2 timesOp_assoc[symmetric] sort_lift
        lift_extendR[where U=H and R="\<lbrakk>A1,B1\<rbrakk>"] lift_extendR[where U=CNOT and R="\<lbrakk>B1\<rbrakk>"]
        assoc_replace[OF H] assoc_replace[OF UadjU] assoc_replace[OF CNOT] assoc_replace[OF adjUU])
qed

lemma teleport_goal2_a0c0:
  fixes C1 A1 B1 A2 :: "bit qvariable"
  assumes qvars[simp]: "distinct_qvars \<lbrakk>C1,A1,B1,A2\<rbrakk>"
  shows "Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> (Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
                 quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op 
                                     \<cdot> addState (state_to_vector EPR)) \<lbrakk>A2\<rbrakk>)
       \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>"
proof -
  have                              "distinct_qvars \<lbrakk>A1,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>B1,A1\<rbrakk>"                             and "distinct_qvars \<lbrakk>B1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>B1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>C1,A1\<rbrakk>" and "distinct_qvars \<lbrakk>C1,B1\<rbrakk>"                             and "distinct_qvars \<lbrakk>C1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>A2,A1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro: distinct_qvars_swap)
  note colocals = this distinct_qvars_split1 distinct_qvars_split2
  show ?thesis
    apply (auto simp: prepare_for_code colocals assoc_right)
    by eval
qed

lemma teleport_goal2_a0c1:
  fixes C1 A1 B1 A2 :: "bit qvariable"
  assumes qvars[simp]: "distinct_qvars \<lbrakk>C1,A1,B1,A2\<rbrakk>"
  shows "Z\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> (Proj (span {basis_vector 1})\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> (Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
                 quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op 
                                     \<cdot> addState (state_to_vector EPR)) \<lbrakk>A2\<rbrakk>))
       \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>"
proof -
  have                               "distinct_qvars \<lbrakk>A1,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>B1,A1\<rbrakk>"                              and "distinct_qvars \<lbrakk>B1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>B1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>C1,A1\<rbrakk>" and "distinct_qvars \<lbrakk>C1,B1\<rbrakk>"                              and "distinct_qvars \<lbrakk>C1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>A2,A1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro: distinct_qvars_swap)
  note colocals = this distinct_qvars_split1 distinct_qvars_split2
  show ?thesis
    apply (auto simp: prepare_for_code colocals assoc_right)
    by eval
qed

lemma teleport_goal2_a1c0:
  fixes C1 A1 B1 A2 :: "bit qvariable"
  assumes qvars[simp]: "distinct_qvars \<lbrakk>C1,A1,B1,A2\<rbrakk>"
  shows "X\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> (Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> (Proj (span {basis_vector 1})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
                 quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op 
                                     \<cdot> addState (state_to_vector EPR)) \<lbrakk>A2\<rbrakk>))
       \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>"
proof -
  have                               "distinct_qvars \<lbrakk>A1,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>B1,A1\<rbrakk>"                              and "distinct_qvars \<lbrakk>B1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>B1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>C1,A1\<rbrakk>" and "distinct_qvars \<lbrakk>C1,B1\<rbrakk>"                              and "distinct_qvars \<lbrakk>C1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>A2,A1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro: distinct_qvars_swap)
  note colocals = this distinct_qvars_split1 distinct_qvars_split2
  show ?thesis
    apply (auto simp: prepare_for_code colocals assoc_right)
    by eval
qed


lemma teleport_goal2_a1c1:
  fixes C1 A1 B1 A2 :: "bit qvariable"
  assumes qvars[simp]: "distinct_qvars \<lbrakk>C1,A1,B1,A2\<rbrakk>"
  shows "Z\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> (X\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> (Proj (span {basis_vector 1})\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> (Proj (span {basis_vector 1})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
                 quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op 
                                     \<cdot> addState (state_to_vector EPR)) \<lbrakk>A2\<rbrakk>)))
       \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>"
proof -
  have                               "distinct_qvars \<lbrakk>A1,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>A1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>B1,A1\<rbrakk>"                              and "distinct_qvars \<lbrakk>B1,C1\<rbrakk>" and "distinct_qvars \<lbrakk>B1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>C1,A1\<rbrakk>" and "distinct_qvars \<lbrakk>C1,B1\<rbrakk>"                              and "distinct_qvars \<lbrakk>C1,A2\<rbrakk>" 
    and "distinct_qvars \<lbrakk>A2,A1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,B1\<rbrakk>" and "distinct_qvars \<lbrakk>A2,C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro: distinct_qvars_swap)
  note colocals = this distinct_qvars_split1 distinct_qvars_split2
  show ?thesis
    apply (auto simp: prepare_for_code colocals assoc_right)
    by eval
qed


end


