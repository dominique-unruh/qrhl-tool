theory Teleport
  imports QRHL_Protocol
begin

definition "computational_basis_vec n = map (unit_vec n) [0..<n]"
definition "orthogonal_complement_vec n vs = 
  filter (op\<noteq> (zero_vec n)) (drop (length vs) (gram_schmidt n (vs @ computational_basis_vec n)))"

declare[[quick_and_dirty]]

axiomatization where tensor_times[simp]: "(U1 \<otimes> U2) \<cdot> (V1 \<otimes> V2) = (U1 \<cdot> V1) \<otimes> (U2 \<cdot> V2)"
  for V1 :: "('a1,'b1) bounded" and U1 :: "('b1,'c1) bounded"
   and V2 :: "('a2,'b2) bounded" and U2 :: "('b2,'c2) bounded"

axiomatization vector_to_bounded :: "'a vector \<Rightarrow> (unit,'a) bounded"
  where vector_to_bounded_applyOp: "vector_to_bounded (A\<cdot>\<psi>) = A \<cdot> vector_to_bounded \<psi>" for A :: "(_,_)bounded"

lemma vector_to_bounded_scalar_times: "vector_to_bounded (a\<cdot>\<psi>) = a \<cdot> vector_to_bounded \<psi>" for a::complex
  apply (rewrite at "a\<cdot>\<psi>" DEADID.rel_mono_strong[of _ "(a\<cdot>idOp)\<cdot>\<psi>"])
   apply simp
  apply (subst vector_to_bounded_applyOp)
  by simp

(* TODO document *)
definition addState :: "'a vector \<Rightarrow> ('b,'b*'a) bounded" where "addState \<psi> = idOp \<otimes> (vector_to_bounded \<psi>) \<cdot> remove_qvar_unit_op*"

axiomatization EPR :: "(bit*bit) state" 

axiomatization where applyOpSpace_colocal[simp]:
  "colocal U S \<Longrightarrow> U\<noteq>0 \<Longrightarrow> U \<cdot> S = S" for U :: "(mem2,mem2) bounded" and S :: predicate

axiomatization where colocal_op_pred_lift1[simp]:
 "colocal S Q \<Longrightarrow> colocal (U\<guillemotright>Q) S"
for Q :: "'a qvariables" and U :: "('a,'a) bounded" and S :: predicate



axiomatization where colocal_op_qvars_lift1[simp]:
  "distinct_qvars (qvariable_concat Q R) \<Longrightarrow> colocal (U\<guillemotright>Q) R"
for Q R :: "_ qvariables" and U :: "('a,'a) bounded"
  

axiomatization where colocal_pred_qvars_lift1[simp]:
  "distinct_qvars (qvariable_concat Q R) \<Longrightarrow> colocal_pred_qvars (S\<guillemotright>Q) R"
for Q :: "'a qvariables"

axiomatization where colocal_pred_qvars_mult[simp]:
  "colocal_op_qvars U Q \<Longrightarrow> colocal_pred_qvars S Q \<Longrightarrow> colocal_pred_qvars (U\<cdot>S) Q"
 
axiomatization where colocal_ortho[simp]: "colocal (ortho S) Q = colocal S Q"


lemma lift_extendR:
  assumes "distinct_qvars (qvariable_concat Q R)"
  shows "U\<guillemotright>Q = (U\<otimes>idOp)\<guillemotright>(qvariable_concat Q R)"
  by (metis assms qvariable_extension_hint_bounded qvariable_extension_hint_def)

lemma lift_extendL:
  assumes "distinct_qvars (qvariable_concat Q R)"
  shows "U\<guillemotright>Q = (idOp\<otimes>U)\<guillemotright>(qvariable_concat R Q)"
  by (metis assms distinct_qvars_swap lift_idOp lift_tensorOp times_idOp2)
  
axiomatization where tensor_adjoint[simp]: "adjoint (U\<otimes>V) = (adjoint U) \<otimes> (adjoint V)"


lemma sort_lift: (* TODO remove *)
  fixes U :: "(('c \<times> 'd) \<times> 'e, ('c \<times> 'd) \<times> 'e) bounded" and Q R S
  assumes "distinct_qvars (qvariable_concat Q R)" and "distinct_qvars (qvariable_concat R S)" and "distinct_qvars (qvariable_concat Q S)"
  defines "V == assoc_op* \<cdot> U \<cdot> assoc_op"
  shows
    "U\<guillemotright>(qvariable_concat (qvariable_concat Q R) S) = V\<guillemotright>(qvariable_concat Q (qvariable_concat R S))"
  sorry

axiomatization where idOp_tensor_idOp[simp]: "idOp\<otimes>idOp = idOp"

lemma tensor_unitary[simp]: 
  assumes "unitary U" and "unitary V"
  shows "unitary (U\<otimes>V)"
  using assms unfolding unitary_def by simp

(* lemma distinct_qvars_split1: "distinct_qvars (qvariable_concat (qvariable_concat Q R) S) = (distinct_qvars (qvariable_concat Q R) \<and> distinct_qvars (qvariable_concat Q S) \<and> distinct_qvars (qvariable_concat R S))" sorry *)
(* lemma distinct_qvars_split2: "colocal S (qvariable_concat Q R) = (colocal Q R \<and> colocal S Q \<and> colocal S R)" for S :: "'a qvariables"  *)

lemma adjUU[simp]: "isometry U \<Longrightarrow> U* \<cdot> U = idOp" unfolding isometry_def by simp
lemma UadjU[simp]: "unitary U \<Longrightarrow> U \<cdot> U* = idOp" unfolding unitary_def by simp


lemma assoc_replace: 
  fixes A B C D :: "(_,_) bounded"
  assumes "A \<cdot> B = C"
  shows "D \<cdot> A \<cdot> B = D \<cdot> C"
  by (simp add: timesOp_assoc[symmetric] assms) 

(* lemma tensor_id_id[simp]: "idOp \<otimes> idOp = idOp"  *)

axiomatization where
  timesOp_assoc_subspace: "applyOpSpace (timesOp A B) S = applyOpSpace A (applyOpSpace B S)"
for S :: "'a subspace" and B :: "('a,'b) bounded" and A :: "('b,'c) bounded"

lemmas assoc_left = timesOp_assoc timesOp_assoc_subspace[symmetric]
lemmas assoc_right = timesOp_assoc[symmetric] timesOp_assoc_subspace


(* axiomatization eigenspace :: "complex \<Rightarrow> ('a,'a) bounded \<Rightarrow> 'a subspace" *)
axiomatization kernel :: "('a,'b) bounded \<Rightarrow> 'a subspace"
definition eigenspace :: "complex \<Rightarrow> ('a,'a) bounded \<Rightarrow> 'a subspace" where
  "eigenspace a A = kernel (A-a\<cdot>idOp)" 


axiomatization where quantum_equality_full_subspace:
  "distinct_qvars (qvariable_concat Q R) \<Longrightarrow> quantum_equality_full U Q V R = 
                 (eigenspace 1 (comm_op \<cdot> (V*\<cdot>U)\<otimes>(U*\<cdot>V))) \<guillemotright> qvariable_concat Q R"
  for Q :: "'a qvariables" and R :: "'b qvariables"
  and U V :: "(_,'c) bounded"


lemma add_join_qvariables_hint: 
  fixes Q :: "'a qvariables" and R :: "'b qvariables" and A :: "('a,'a) bounded"
  shows "NO_MATCH (a,a) (Q,R) \<Longrightarrow> S\<guillemotright>Q \<sqinter> T\<guillemotright>R = join_qvariables_hint (S\<guillemotright>Q) R \<sqinter> join_qvariables_hint (T\<guillemotright>R) Q"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> S\<guillemotright>Q + T\<guillemotright>R = join_qvariables_hint (S\<guillemotright>Q) R + join_qvariables_hint (T\<guillemotright>R) Q"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> A\<guillemotright>Q \<cdot> T\<guillemotright>R = join_qvariables_hint (A\<guillemotright>Q) R \<cdot> join_qvariables_hint (T\<guillemotright>R) Q"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (S\<guillemotright>Q \<le> T\<guillemotright>R) = (join_qvariables_hint (S\<guillemotright>Q) R \<le> join_qvariables_hint (T\<guillemotright>R) Q)"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (S\<guillemotright>Q = T\<guillemotright>R) = (join_qvariables_hint (S\<guillemotright>Q) R = join_qvariables_hint (T\<guillemotright>R) Q)"
  unfolding join_qvariables_hint_def by simp_all





axiomatization where move_plus:
  "Proj (ortho C) \<cdot> A \<le> B \<Longrightarrow> A \<le> B + C"


lemma move_plus_ortho:
  assumes "Proj C \<cdot> A \<le> B"
  shows "A \<le> (B\<sqinter>C) + ortho C"
  apply (rule move_plus)
  using assms Proj_leq by auto

axiomatization where lift_timesOp[simp]: 
  "distinct_qvars Q \<Longrightarrow> S\<guillemotright>Q \<cdot> T\<guillemotright>Q = (S \<cdot> T)\<guillemotright>Q" for S T :: "('a,'a) bounded"  

axiomatization where Proj_lift[simp]: "Proj (S\<guillemotright>Q) = (Proj S)\<guillemotright>Q"

(* TODO: make proj abbrev instead *)
axiomatization where Proj_span1[simp]: "Proj (span {\<psi>}) = proj \<psi>" 

lemma move_plus_meas_rule:
  fixes Q::"'a qvariables"
  assumes "distinct_qvars Q"
  assumes "(Proj C)\<guillemotright>Q \<cdot> A \<le> B"
  shows "A \<le> (B\<sqinter>C\<guillemotright>Q) + (ortho C)\<guillemotright>Q"
  apply (rule move_plus) 
  apply (auto simp: assms)
  using Proj_leq[of "C\<guillemotright>Q"] by simp



definition [code del]: "SPAN x = spanVector (vector_of_vec ` set x)"
code_datatype SPAN

declare ord_subspace_inst.less_eq_subspace[code del]
declare ord_subspace_inst.less_subspace[code del]

declare sqrt2_def[code del]

definition "vec_tensor (A::'a::times vec) (B::'a vec) =
  vec (dim_vec A*dim_vec B) 
  (\<lambda>r. A $ (r div dim_vec B) *
       B $ (r mod dim_vec B))"

axiomatization where tensorVec_code[code]: "vec_of_vector (\<psi> \<otimes> \<phi>) = vec_tensor (vec_of_vector \<psi>) (vec_of_vector \<phi>)"

derive (eq) ceq vector
derive (no) ccompare vector
derive (monad) set_impl vector (* No clue which is the best. *)                           

(* TODO: don't use enum_len, but cardinality *)
axiomatization where top_as_span[code]: "(top::'a subspace) = SPAN (computational_basis_vec (enum_len TYPE('a::enum)))"
axiomatization where bot_as_span[code]: "(bot::'a::enum subspace) = SPAN []" 
axiomatization where plus_spans[code]: "SPAN A + SPAN B = SPAN (A @ B)" 

axiomatization where one_times_op[simp]: "(1::complex) \<cdot> A = A" for A :: "('a,'a) bounded"
axiomatization where one_times_vec[simp]: "(1::complex) \<cdot> \<psi> = \<psi>" for \<psi> :: "'a vector"

definition[code del]: "EPR' = timesScalarVec sqrt2 (state_to_vector EPR)"
lemma EPR_EPR': "state_to_vector EPR = timesScalarVec (1/sqrt2) EPR'"
  unfolding EPR'_def by simp

axiomatization where vec_of_vector_EPR'[code]: "vec_of_vector EPR' = vec_of_list [1,0,0,1]"

axiomatization where vec_of_vector_timesScalarVec[code]: "vec_of_vector (timesScalarVec a \<psi>) = smult_vec a (vec_of_vector \<psi>)"
(* lemma [code]: "mat_of_bounded (addState \<psi> :: ('a::enum,'a*'b::enum) bounded) 
  = matrix_tensor (one_mat (enum_len TYPE('a))) (mat_of_cols (enum_len TYPE('b)) [vec_of_vector \<psi>])" *)
axiomatization where ortho_SPAN[code]: "ortho (SPAN S :: 'a::enum subspace) = SPAN (orthogonal_complement_vec (enum_len TYPE('a)) S)"
axiomatization where span_Set_Monad[code]: "span (Set_Monad l) = SPAN (map vec_of_vector l)"
axiomatization where tensorSpace_SPAN[code]: "tensorSpace (SPAN A) (SPAN B) = SPAN [vec_tensor a b. a<-A, b<-B]"

(* TODO: don't use enum_len, use CARD('a) *)

lemma [code_post]: 
  shows "Complex a 0 = complex_of_real a"
  and "complex_of_real 0 = 0"
  and "complex_of_real 1 = 1"
  and "complex_of_real (a/b) = complex_of_real a / complex_of_real b"
  and "complex_of_real (numeral n) = numeral n"
  and "complex_of_real (-r) = - complex_of_real r"
  using[[show_consts]]
  using complex_eq_cancel_iff2 by auto

instantiation subspace :: (enum) equal begin
definition [code del]: "equal_subspace (A::'a subspace) B = (A=B)"
instance apply intro_classes unfolding equal_subspace_def by simp
end


definition "is_subspace_of n vs ws =  
  list_all (op= (zero_vec n)) (drop (length ws) (gram_schmidt n (ws @ vs)))"

axiomatization where SPAN_leq[code]: "SPAN A \<le> (SPAN B :: 'a subspace) \<longleftrightarrow> is_subspace_of (CARD('a::enum)) A B" 

axiomatization where applyOpSpace_SPAN[code]: "applyOpSpace A (SPAN S) = SPAN (map (mult_mat_vec (mat_of_bounded A)) S)"

axiomatization where kernel_SPAN[code]: "kernel A = SPAN (find_base_vectors (gauss_jordan_single (mat_of_bounded A)))" 

axiomatization where mat_of_bounded_classical_operator[code]: "(mat_of_bounded (classical_operator f :: ('a,'b)bounded)) = mat (enum_len TYPE('b::enum)) (enum_len TYPE('a::enum))
  (\<lambda>(r,c). if f (Enum.enum!c) = Some (Enum.enum!r) then 1 else 0)" 

lemma [code]: "HOL.equal (A::_ subspace) B = (A\<le>B \<and> B\<le>A)"
  unfolding equal_subspace_def by auto

(* lemma [code]: "SPAN A = (SPAN B :: 'a::enum subspace) \<longleftrightarrow>
  ((SPAN A::'a subspace) \<le> (SPAN B::'a subspace)) \<and> ((SPAN B::'a subspace) \<le> (SPAN A::'a subspace))" by auto *)

lemma [code_abbrev]: "kernel (A-a\<cdot>idOp) = eigenspace a A" 
  unfolding eigenspace_def by simp
(* lemma [code_abbrev]: "ortho (ortho A + ortho B) = A \<sqinter> B" unfolding subspace_sup_plus[symmetric]  *)

axiomatization where kernel_scalar_times[simp]: "a\<noteq>0 \<Longrightarrow> kernel (a\<cdot>A) = kernel A" for a :: complex
axiomatization where kernel_0[simp]: "kernel 0 = top"
axiomatization where kernel_id[simp]: "kernel idOp = 0"
axiomatization where scalar_times_op_add[simp]: "a \<cdot> (A+B) = a\<cdot>A + a\<cdot>B" for a::complex and A B :: "('a,'b) bounded"
lemma [simp]: "a \<cdot> (A-B) = a\<cdot>A - a\<cdot>B" for a::complex and A B :: "('a,'b) bounded"
  by (metis add_diff_cancel_right' diff_add_cancel scalar_times_op_add)

(* TODO: make def of uminus, same for vector *)
lemma uminus_bounded_def: "(-A) = (-1) \<cdot> A" for A::"(_,_)bounded" sorry 

lemma [simp]: "a\<noteq>0 \<Longrightarrow> eigenspace b (a\<cdot>A) = eigenspace (b/a) A"
  unfolding eigenspace_def
  apply (rewrite at "kernel \<hole>" DEADID.rel_mono_strong[where y="a \<cdot> (A - b / a \<cdot> idOp)"])
   apply auto[1]
  by (subst kernel_scalar_times, auto)

lemma [simp]: "eigenspace b 0 = Cla[b=0]"
  unfolding eigenspace_def apply auto
  apply (rewrite at "kernel \<hole>" DEADID.rel_mono_strong[where y="(-b) \<cdot> idOp"])
  by (auto simp: subspace_zero_bot uminus_bounded_def)

axiomatization where scalar_times_adj[simp]: "(a \<cdot> A)* = cnj a \<cdot> (A*)" for A::"('a,'b)bounded"
lemma [simp]: "addState (a \<cdot> \<psi>) = a \<cdot> addState \<psi>" for a::complex and psi::"'a vector"
  unfolding addState_def by (simp add: vector_to_bounded_scalar_times)
lemma [simp]: "cnj sqrt2 = sqrt2"
  unfolding sqrt2_def by simp


lemma [code]: "Inf (Set_Monad l :: 'a subspace set) = fold inf l top"
  unfolding Set_Monad_def
  by (simp add: Inf_set_fold)

lemma [code]: "(A::'a subspace) \<sqinter> B = ortho (ortho A + ortho B)" 
  unfolding subspace_sup_plus[symmetric]
  by (smt inf.absorb2 inf.orderE inf_assoc_subspace inf_sup_ord(1) inf_sup_ord(2) leq_plus_subspace leq_plus_subspace2 ortho_leq ortho_twice subspace_plus_sup subspace_sup_plus)

lemma test: "1=(1::nat)"
  by eval
ML_command \<open>
  @{thm test} |> Thm.proof_body_of |> Proofterm.all_oracles_of |> map fst |> map @{print}
\<close>


lemma span_vector_state: "spanState A = spanVector (state_to_vector ` A)"
  by (simp add: spanState_def spanVector_def) 

lemma span_mult[simp]: "(a::complex)\<noteq>0 \<Longrightarrow> span { a\<cdot>\<psi> } = span {\<psi>::'a vector}"
  by (metis imageOp_proj proj_scalar_mult)


lemma Cla_inf_lift: "distinct_qvars Q \<Longrightarrow> Cla[b] \<sqinter> (S\<guillemotright>Q) = (if b then S else bot)\<guillemotright>Q"
  by auto
lemma Cla_plus_lift: "distinct_qvars Q \<Longrightarrow> Cla[b] + (S\<guillemotright>Q) = (if b then top else S)\<guillemotright>Q"
  by auto

axiomatization where INF_lift: "distinct_qvars Q \<Longrightarrow> (INF x. S x\<guillemotright>Q) = (INF x. S x)\<guillemotright>Q"

lemmas prepare_for_code = H_H' quantum_equality_full_subspace add_join_qvariables_hint INF_lift 
  EPR_EPR' span_vector_state Cla_inf_lift Cla_plus_lift

lemmas qvar_trafo_adj_assoc_mult[simp] = qvar_trafo_mult[OF qvar_trafo_adj[OF qvar_trafo_assoc_op]] 
    

axiomatization where mat_of_bounded_vector_to_bounded[code]: "mat_of_bounded (vector_to_bounded \<psi>) = mat_of_cols (CARD('a)) [vec_of_vector \<psi>]" 
  for \<psi>::"'a::enum vector"

axiomatization where mat_of_bounded_remove_qvar_unit_op[code]:
  "mat_of_bounded (remove_qvar_unit_op::(_,'a::enum) bounded) = mat_of_bounded (idOp::(_,'a) bounded)" 

(* 
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


derive (eq) ceq subspace
derive (no) ccompare subspace
derive (monad) set_impl subspace

  

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
    by (simp add: distinct_qvars_split1 distinct_qvars_split2 timesOp_assoc sort_lift
        lift_extendR[where U=H and R="\<lbrakk>A1,B1\<rbrakk>"] lift_extendR[where U=CNOT and R="\<lbrakk>B1\<rbrakk>"]
        assoc_replace[OF H] assoc_replace[OF UadjU] assoc_replace[OF CNOT] assoc_replace[OF adjUU])
qed



axiomatization where scalar_op_subspace [simp]: 
  "(\<alpha>\<cdot>A)\<cdot>S = \<alpha>\<cdot>(A\<cdot>S)" for \<alpha>::complex and A::"('a,'b)bounded" and S::"'a subspace"
  
  


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


