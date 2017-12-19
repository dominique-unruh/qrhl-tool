theory Teleport
  imports QRHL_Protocol
begin

definition "computational_basis_vec n = map (unit_vec n) [0..<n]"
definition "orthogonal_complement_vec n vs = 
  filter (op\<noteq> (zero_vec n)) (drop (length vs) (gram_schmidt n (vs @ computational_basis_vec n)))"

declare[[quick_and_dirty]]

lemma tensor_times[simp]: "(U1 \<otimes> U2) \<cdot> (V1 \<otimes> V2) = (U1 \<cdot> V1) \<otimes> (U2 \<cdot> V2)"
  for U1 U2 V1 V2 :: "(_,_) bounded"
  sorry

axiomatization addState :: "'a vector \<Rightarrow> ('b,'b*'a) bounded"

axiomatization EPR :: "(bit*bit) state" 

lemma applyOpSpace_colocal[simp]:
  fixes U :: "(mem2,mem2) bounded" and S :: predicate
  assumes "colocal U S"
  shows "U \<cdot> S = S"
  sorry

lemma colocal_op_pred_lift1[simp]:
  fixes Q :: "'a qvariables" and U :: "('a,'a) bounded" and S :: predicate
  assumes "colocal S Q"
  shows "colocal (U\<guillemotright>Q) S"
  sorry

lemma colocal_op_qvars_lift1[simp]:
  fixes Q R :: "_ qvariables" and U :: "('a,'a) bounded"
  assumes "colocal Q R"
  shows "colocal (U\<guillemotright>Q) R"
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


lemma colocal_ortho[simp]: "colocal (ortho S) Q = colocal S Q" sorry



lemma lift_extendR:
  assumes "colocal Q R"
  shows "U\<guillemotright>Q = (U\<otimes>idOp)\<guillemotright>(qvariable_concat Q R)"
  sorry

lemma lift_extendL:
  assumes "colocal Q R"
  shows "U\<guillemotright>Q = (idOp\<otimes>U)\<guillemotright>(qvariable_concat R Q)"
  sorry

lemma tensor_adjoint[simp]: "adjoint (U\<otimes>V) = (adjoint U) \<otimes> (adjoint V)" sorry

lemma sort_lift: (* TODO remove *)
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

lemma colocal_split1: "colocal (qvariable_concat Q R) S = (colocal Q R \<and> colocal Q S \<and> colocal R S)" sorry
lemma colocal_split2: "colocal S (qvariable_concat Q R) = (colocal Q R \<and> colocal S Q \<and> colocal S R)" for S :: "'a qvariables" sorry

lemma adjUU[simp]: "isometry U \<Longrightarrow> U* \<cdot> U = idOp" unfolding isometry_def by simp
lemma UadjU[simp]: "unitary U \<Longrightarrow> U \<cdot> U* = idOp" unfolding unitary_def by simp

lemma assoc_replace: 
  fixes A B C D :: "(_,_) bounded"
  assumes "A \<cdot> B = C"
  shows "D \<cdot> A \<cdot> B = D \<cdot> C"
  by (simp add: timesOp_assoc[symmetric] assms) 

lemma tensor_id_id[simp]: "idOp \<otimes> idOp = idOp" sorry

axiomatization where
  timesOp_assoc_subspace[simp]: "applyOpSpace (timesOp A B) S = applyOpSpace A (applyOpSpace B S)"
for S :: "'a subspace" and B :: "('a,'b) bounded" and A :: "('b,'c) bounded"




axiomatization eigenspace :: "complex \<Rightarrow> ('a,'a) bounded \<Rightarrow> 'a subspace"
axiomatization kernel :: "('a,'b) bounded \<Rightarrow> 'a subspace"

lemma quantum_equality_full_subspace:
  "colocal Q R \<Longrightarrow> quantum_equality_full U Q V R = (eigenspace 1 (comm_op \<cdot> (V*\<cdot>U)\<otimes>(U*\<cdot>V))) \<guillemotright> qvariable_concat Q R"
  for Q :: "'a qvariables" and R :: "'b qvariables"
  and U V :: "(_,'c) bounded"
  using [[show_types,show_sorts,show_consts,show_brackets]]
  sorry

  

(* lemma colocal_sym: "colocal Q R \<Longrightarrow> colocal R Q" for Q :: "'a qvariables" and R :: "'b qvariables" sorry *)

(* definition "reorder_qvars x (Q::'a qvariables) (R::'b qvariables) = x" *)

lemma add_join_qvariables_hint: 
  fixes Q :: "'a qvariables" and R :: "'b qvariables" and A :: "('a,'a) bounded"
  shows "NO_MATCH (a,a) (Q,R) \<Longrightarrow> S\<guillemotright>Q \<sqinter> T\<guillemotright>R = join_qvariables_hint (S\<guillemotright>Q) R \<sqinter> join_qvariables_hint (T\<guillemotright>R) Q"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> S\<guillemotright>Q + T\<guillemotright>R = join_qvariables_hint (S\<guillemotright>Q) R + join_qvariables_hint (T\<guillemotright>R) Q"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> A\<guillemotright>Q \<cdot> T\<guillemotright>R = join_qvariables_hint (A\<guillemotright>Q) R \<cdot> join_qvariables_hint (T\<guillemotright>R) Q"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (S\<guillemotright>Q \<le> T\<guillemotright>R) = (join_qvariables_hint (S\<guillemotright>Q) R \<le> join_qvariables_hint (T\<guillemotright>R) Q)"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (S\<guillemotright>Q = T\<guillemotright>R) = (join_qvariables_hint (S\<guillemotright>Q) R = join_qvariables_hint (T\<guillemotright>R) Q)"
  unfolding join_qvariables_hint_def by simp_all


(* lemma reorder_qvars_subspace:
  fixes Q :: "'a qvariables" and R :: "'b qvariables"
  fixes A1 :: "'a1 qvariable" and A2 :: "'a2 qvariable" and B1 :: "'b1 qvariable" and C1 :: "'c1 qvariable" 
  fixes S S' T S1 T1 S2 T2 S3 T3 S4 T4:: "_ subspace"
  shows "colocal Q R \<Longrightarrow> reorder_qvars (S\<guillemotright>Q) Q R = (S\<otimes>top) \<guillemotright> qvariable_concat Q R" 
  and "colocal Q R \<Longrightarrow> reorder_qvars (T\<guillemotright>R) Q R = (top\<otimes>T) \<guillemotright> qvariable_concat Q R"
  and "colocal Q R \<Longrightarrow> reorder_qvars (S'\<guillemotright>qvariable_concat Q R) (qvariable_concat Q R) R = (S'\<guillemotright>qvariable_concat Q R)"
  and "colocal Q R \<Longrightarrow> reorder_qvars (T\<guillemotright>R) (qvariable_concat Q R) R = (top\<otimes>T) \<guillemotright> qvariable_concat Q R"
  and "colocal Q R \<Longrightarrow> reorder_qvars (S'\<guillemotright>qvariable_concat Q R) (qvariable_concat Q R) Q = (S'\<guillemotright>qvariable_concat Q R)"
  and "colocal Q R \<Longrightarrow> reorder_qvars (S\<guillemotright>Q) (qvariable_concat Q R) Q = (S\<otimes>top) \<guillemotright> qvariable_concat Q R"
  and "colocal Q R \<Longrightarrow> reorder_qvars (S\<guillemotright>Q) Q (qvariable_concat Q R) = (S\<otimes>top) \<guillemotright> qvariable_concat Q R"
  and "colocal Q R \<Longrightarrow> reorder_qvars (S'\<guillemotright>qvariable_concat Q R) Q (qvariable_concat Q R) = (S'\<guillemotright>qvariable_concat Q R)"
  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (S1\<guillemotright>qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>) (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>) (qvariable_concat \<lbrakk>B1, A2\<rbrakk> \<lbrakk>A1\<rbrakk>)
            = (comm_op \<cdot> S1) \<guillemotright> \<lbrakk>A2,C1,A1,B1\<rbrakk>"
  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (T1\<guillemotright>(qvariable_concat \<lbrakk>B1, A2\<rbrakk> \<lbrakk>A1\<rbrakk>)) (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>) (qvariable_concat \<lbrakk>B1, A2\<rbrakk> \<lbrakk>A1\<rbrakk>)
            = (classical_operator (\<lambda>(c1,(b1,a2),a1). Some(a2,c1,a1,b1)) \<cdot> (top::'c1 subspace)\<otimes>T1) \<guillemotright> \<lbrakk>A2,C1,A1,B1\<rbrakk>"
  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (S2\<guillemotright>qvariable_concat \<lbrakk>C1, A2\<rbrakk> \<lbrakk>A1, B1\<rbrakk>) (qvariable_concat \<lbrakk>C1, A2\<rbrakk> \<lbrakk>A1, B1\<rbrakk>) (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)
            = (classical_operator (%((c1,a2),(a1,b1)). Some(c1,a2,a1,b1)) \<cdot> S2) \<guillemotright> \<lbrakk>C1,A2,A1,B1\<rbrakk>"
  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (T2\<guillemotright>qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>) (qvariable_concat \<lbrakk>C1, A2\<rbrakk> \<lbrakk>A1, B1\<rbrakk>) (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)
            = (classical_operator (%((c1,a1,b1),a2). Some(c1,a2,a1,b1)) \<cdot> T2) \<guillemotright> \<lbrakk>C1,A2,A1,B1\<rbrakk>"
  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (S3\<guillemotright>(qvariable_concat \<lbrakk>C1, A2\<rbrakk> \<lbrakk>A1, B1\<rbrakk>)) (qvariable_concat \<lbrakk>C1, A2\<rbrakk> \<lbrakk>A1, B1\<rbrakk>) (qvariable_concat \<lbrakk>B1, A2\<rbrakk> \<lbrakk>C1, A1\<rbrakk>)
    = (classical_operator (%((c1,a2),(a1,b1)). Some(c1,a2,a1,b1)) \<cdot> S3)\<guillemotright>\<lbrakk>C1,A2,A1,B1\<rbrakk>"
  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (T3\<guillemotright>(qvariable_concat \<lbrakk>B1, A2\<rbrakk> \<lbrakk>C1, A1\<rbrakk>)) (qvariable_concat \<lbrakk>C1, A2\<rbrakk> \<lbrakk>A1, B1\<rbrakk>) (qvariable_concat \<lbrakk>B1, A2\<rbrakk> \<lbrakk>C1, A1\<rbrakk>)
    = (classical_operator (%((b1,a2),(c1,a1)). Some(c1,a2,a1,b1)) \<cdot> T3)\<guillemotright>\<lbrakk>C1,A2,A1,B1\<rbrakk>"
  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (S4\<guillemotright>\<lbrakk>A1\<rbrakk>) \<lbrakk>A1\<rbrakk> (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)
    = ((top\<otimes>(S4\<otimes>top))\<otimes>top)\<guillemotright>(qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)"
  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (T4\<guillemotright>(qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)) \<lbrakk>A1\<rbrakk> (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)
    = T4\<guillemotright>(qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)"
  sorry

definition "wrap A B = A \<cdot> B \<cdot> A*" for A B :: "(_,_)bounded"

lemma reorder_qvars_bounded:
  fixes Q :: "'a qvariables" and R :: "'b qvariables"
  fixes A1 :: "'a1 qvariable" and A2 :: "'a2 qvariable" and B1 :: "'b1 qvariable" and C1 :: "'c1 qvariable" 
  fixes S S' T S1 T1 S2 T2 S3 T3 S4 T4 :: "(_,_) bounded"
  shows "colocal Q R \<Longrightarrow> reorder_qvars (S\<guillemotright>Q) Q R = (S\<otimes>idOp) \<guillemotright> qvariable_concat Q R" 
  and "colocal Q R \<Longrightarrow> reorder_qvars (T\<guillemotright>R) Q R = (idOp\<otimes>T) \<guillemotright> qvariable_concat Q R"
  and "colocal Q R \<Longrightarrow> reorder_qvars (S'\<guillemotright>qvariable_concat Q R) (qvariable_concat Q R) R = (S'\<guillemotright>qvariable_concat Q R)"
  and "colocal Q R \<Longrightarrow> reorder_qvars (T\<guillemotright>R) (qvariable_concat Q R) R = (idOp\<otimes>T) \<guillemotright> qvariable_concat Q R"
  and "colocal Q R \<Longrightarrow> reorder_qvars (S'\<guillemotright>qvariable_concat Q R) (qvariable_concat Q R) Q = (S'\<guillemotright>qvariable_concat Q R)"
  and "colocal Q R \<Longrightarrow> reorder_qvars (S\<guillemotright>Q) (qvariable_concat Q R) Q = (S\<otimes>idOp) \<guillemotright> qvariable_concat Q R"
  and "colocal Q R \<Longrightarrow> reorder_qvars (S\<guillemotright>Q) Q (qvariable_concat Q R) = (S\<otimes>idOp) \<guillemotright> qvariable_concat Q R"
  and "colocal Q R \<Longrightarrow> reorder_qvars (S'\<guillemotright>qvariable_concat Q R) Q (qvariable_concat Q R) = (S'\<guillemotright>qvariable_concat Q R)"
(*  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (S1\<guillemotright>qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>) (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>) (qvariable_concat \<lbrakk>B1, A2\<rbrakk> \<lbrakk>A1\<rbrakk>)
            = (comm_op \<cdot> S1) \<guillemotright> \<lbrakk>A2,C1,A1,B1\<rbrakk>"
  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (T1\<guillemotright>(qvariable_concat \<lbrakk>B1, A2\<rbrakk> \<lbrakk>A1\<rbrakk>)) (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>) (qvariable_concat \<lbrakk>B1, A2\<rbrakk> \<lbrakk>A1\<rbrakk>)
            = (classical_operator (\<lambda>(c1,(b1,a2),a1). Some(a2,c1,a1,b1)) \<cdot> (top::'c1 subspace)\<otimes>T1) \<guillemotright> \<lbrakk>A2,C1,A1,B1\<rbrakk>"
  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (S2\<guillemotright>qvariable_concat \<lbrakk>C1, A2\<rbrakk> \<lbrakk>A1, B1\<rbrakk>) (qvariable_concat \<lbrakk>C1, A2\<rbrakk> \<lbrakk>A1, B1\<rbrakk>) (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)
            = (classical_operator (%((c1,a2),(a1,b1)). Some(c1,a2,a1,b1)) \<cdot> S2) \<guillemotright> \<lbrakk>C1,A2,A1,B1\<rbrakk>"
  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (T2\<guillemotright>qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>) (qvariable_concat \<lbrakk>C1, A2\<rbrakk> \<lbrakk>A1, B1\<rbrakk>) (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)
            = (classical_operator (%((c1,a1,b1),a2). Some(c1,a2,a1,b1)) \<cdot> T2) \<guillemotright> \<lbrakk>C1,A2,A1,B1\<rbrakk>" *)
  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (S4\<guillemotright>\<lbrakk>A1\<rbrakk>) \<lbrakk>A1\<rbrakk> (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)
    = ((idOp\<otimes>(S4\<otimes>idOp))\<otimes>idOp)\<guillemotright>(qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)"
  and "colocal \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<Longrightarrow> reorder_qvars (T4\<guillemotright>(qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)) \<lbrakk>A1\<rbrakk> (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)
    = T4\<guillemotright>(qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>)"
  sorry *)




lemma move_plus:
  assumes "Proj (ortho C) \<cdot> A \<le> B"
  shows "A \<le> B + C"
  sorry

lemma move_plus_ortho:
  assumes "Proj C \<cdot> A \<le> B"
  shows "A \<le> (B\<sqinter>C) + ortho C"
  apply (rule move_plus)
  using assms Proj_leq by auto

axiomatization where lift_timesOp[simp]: "distinct_qvars Q \<Longrightarrow> S\<guillemotright>Q \<cdot> T\<guillemotright>Q = (S \<cdot> T)\<guillemotright>Q" for S T :: "('a,'a) bounded"  

lemma Proj_lift[simp]: "Proj (S\<guillemotright>Q) = (Proj S)\<guillemotright>Q"
  sorry
lemma Proj_span1[simp]: "Proj (span {\<psi>}) = proj \<psi>" sorry


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

lemma [code]: "vec_of_vector (\<psi> \<otimes> \<phi>) = vec_tensor (vec_of_vector \<psi>) (vec_of_vector \<phi>)" sorry

derive (eq) ceq vector
derive (no) ccompare vector
derive (monad) set_impl vector (* No clue which is the best. *)                           

lemma top_as_span[code]: "(top::'a subspace) = SPAN (computational_basis_vec (enum_len TYPE('a::enum)))" sorry
lemma bot_as_span[code]: "(bot::'a::enum subspace) = SPAN ([]::complex vec list)" sorry
lemma plus_spans[code]: "SPAN A + SPAN B = SPAN (A @ B)" sorry

definition[code del]: "EPR' = timesScalarVec sqrt2 (state_to_vector EPR)"
lemma EPR_EPR': "state_to_vector EPR = timesScalarVec (1/sqrt2) EPR'" sorry
lemma [code]: "vec_of_vector EPR' = vec_of_list [1,0,0,1]" sorry

lemma [code]: "vec_of_vector (timesScalarVec a \<psi>) = smult_vec a (vec_of_vector \<psi>)" sorry
lemma [code]: "mat_of_bounded (addState \<psi> :: ('a::enum,'a*'b::enum) bounded) 
  = matrix_tensor (one_mat (enum_len TYPE('a))) (mat_of_cols (enum_len TYPE('b)) [vec_of_vector \<psi>])" sorry
lemma [code]: "ortho (SPAN S :: 'a::enum subspace) = SPAN (orthogonal_complement_vec (enum_len TYPE('a)) S)" sorry
lemma [code]: "span (Set_Monad l) = SPAN (map vec_of_vector l)" sorry
lemma [code]: "tensorSpace (SPAN A) (SPAN B) = SPAN [vec_tensor a b. a<-A, b<-B]" sorry
export_code EPR' in SML file "tmp.ML"

(* code_datatype set  *)

value "[(a,b). a<-[1,2,3::nat], b<-[2,3,4::nat] ]"

find_theorems spanVector subspace_as_set

ML {* 
  @{term "complex_of_real"}
*}
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


value "1/2 :: complex"

definition "is_subspace_of n vs ws =  
  list_all (op= (zero_vec n)) (drop (length ws) (gram_schmidt n (ws @ vs)))"
term matrix_X
lemma [code]: "SPAN A \<le> (SPAN B :: 'a subspace) \<longleftrightarrow> is_subspace_of (enum_len TYPE('a::enum)) A B" sorry
lemma [code]: "applyOpSpace A (SPAN S) = SPAN (map (mult_mat_vec (mat_of_bounded A)) S)" sorry
lemma [code]: "kernel A = SPAN (find_base_vectors (gauss_jordan_single (mat_of_bounded A)))" sorry
lemma [code]: "(mat_of_bounded (classical_operator f :: ('a,'b)bounded)) = mat (enum_len TYPE('b::enum)) (enum_len TYPE('a::enum))
  (\<lambda>(r,c). if f (Enum.enum!c) = Some (Enum.enum!r) then 1 else 0)" sorry
lemma [code]: "HOL.equal (A::_ subspace) B = (A\<le>B \<and> B\<le>A)" sorry

(* lemma [code]: "SPAN A = (SPAN B :: 'a::enum subspace) \<longleftrightarrow>
  ((SPAN A::'a subspace) \<le> (SPAN B::'a subspace)) \<and> ((SPAN B::'a subspace) \<le> (SPAN A::'a subspace))" by auto *)

lemma [code_abbrev]: "kernel (A-a\<cdot>idOp) = eigenspace a A" sorry
(* lemma [code_abbrev]: "ortho (ortho A + ortho B) = A \<sqinter> B" unfolding subspace_sup_plus[symmetric] sorry *)

lemma [simp]: "a\<noteq>0 \<Longrightarrow> eigenspace b (a\<cdot>A) = eigenspace (b/a) A" sorry
lemma [simp]: "eigenspace b 0 = Cla[b=0]" sorry
lemma [simp]: "(a \<cdot> A)* = cnj a \<cdot> (A*)" sorry
lemma [simp]: "addState (a \<cdot> \<psi>) = a \<cdot> addState \<psi>" for a::complex and psi::"'a vector" sorry
lemma [simp]: "cnj sqrt2 = sqrt2" sorry

lemma [code]: "Inf (Set_Monad l :: 'a subspace set) = fold inf l top"  sorry
lemma [code]: "(A::'a subspace) \<sqinter> B = ortho (ortho A + ortho B)" unfolding subspace_sup_plus[symmetric] sorry

value "classical_operator (\<lambda>(c1, (b1, a2), a1). Some (a2::bit, c1::bit, a1::bit, b1::bit)) \<cdot>
       top \<otimes> (eigenspace 1 comm_op \<otimes> top \<sqinter> top \<otimes> span {basis_vector 0} + top \<otimes> ortho (span {basis_vector 0}))"

(* lemma [code_post]: "n = length l \<Longrightarrow> vec_impl (Abs_vec_impl (n, IArray l)) = vec_of_list l" sorry *)




value "span { basis_vector (0::bit), (0.123::complex) \<cdot> basis_vector (1::bit)  } \<le> span { (0.123::complex) \<cdot> basis_vector (0::bit), H' \<cdot> basis_vector 1 } "


definition "px = (\<lambda>(x::'a,y::'a). (x,y))"



lemma span_vector_state: "spanState A = spanVector (state_to_vector ` A)"
  by (simp add: spanState_def spanVector_def) 

lemma span_mult[simp]: "(a::complex)\<noteq>0 \<Longrightarrow> span { a\<cdot>\<psi> } = span {\<psi>::'a vector}" sorry

term classical_subspace
lemma Cla_inf_lift: "colocal Q \<lbrakk>\<rbrakk> \<Longrightarrow> Cla[b] \<sqinter> (S\<guillemotright>Q) = (if b then S else bot)\<guillemotright>Q"
  by auto
lemma Cla_plus_lift: "colocal Q \<lbrakk>\<rbrakk> \<Longrightarrow> Cla[b] + (S\<guillemotright>Q) = (if b then top else S)\<guillemotright>Q"
  by auto
lemma INF_lift: "colocal Q \<lbrakk>\<rbrakk> \<Longrightarrow> (INF x. S x\<guillemotright>Q) = (INF x. S x)\<guillemotright>Q" sorry

lemmas prepare_for_code = H_H' quantum_equality_full_subspace add_join_qvariables_hint INF_lift 
  EPR_EPR' span_vector_state Cla_inf_lift Cla_plus_lift

(* lemma colocal_cheat: "NO_MATCH (a,a) (q,r) \<Longrightarrow> colocal \<lbrakk>q\<rbrakk> \<lbrakk>r\<rbrakk>" sorry
lemma colocal_cheat2: "colocal \<lbrakk>q\<rbrakk> \<lbrakk>r\<rbrakk>" sorry *)

lemmas qvar_trafo_adj_assoc_mult[simp] = qvar_trafo_mult[OF qvar_trafo_adj[OF qvar_trafo_assoc_op]] (* TODO: add to simplifier *)


lemma quantum_eq_add_state: (* TODO: recover axiom *)
  fixes C1 A1 B1 A2 :: "bit qvariable"
  assumes qvars[simp]: "distinct_qvars \<lbrakk>C1,A1,B1,A2\<rbrakk>"
  shows "\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> span {EPR}\<guillemotright>\<lbrakk>A1, B1\<rbrakk> \<le> quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (addState (state_to_vector EPR)) \<lbrakk>A2\<rbrakk>"
proof -
   have                         "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk>" and "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>C1\<rbrakk>" and "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A1\<rbrakk>"                        and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>C1\<rbrakk>" and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk>" and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk>"                        and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>A1\<rbrakk>" and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>B1\<rbrakk>" and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: colocal_split1 colocal_split2 intro: distinct_qvars_swap)
  note colocals = this colocal_split1 colocal_split2
  show ?thesis
    apply simp
    apply (auto simp: prepare_for_code colocals)
    by eval
qed


derive (eq) ceq subspace
derive (no) ccompare subspace
derive (monad) set_impl subspace



(*
lemma teleport_brute_force:
  assumes "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk> \<and> colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk> \<and> colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk> \<and> colocal \<lbrakk>A1\<rbrakk> \<lbrakk>A2\<rbrakk> \<and> colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<and> colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A2\<rbrakk>"
  shows "\<forall>x::bit. (x = 1 \<longrightarrow> \<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> span {EPR}\<guillemotright>\<lbrakk>A1, B1\<rbrakk> \<le> (INF x::bit. (\<CC>\<ll>\<aa>[x = 0] + quantum_equality_full (X \<cdot> Z) \<lbrakk>B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>) \<sqinter> (\<CC>\<ll>\<aa>[x = 1] + quantum_equality_full X \<lbrakk>B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>) \<sqinter> span {basis_vector x}\<guillemotright>\<lbrakk>B1\<rbrakk> + ortho (span {basis_vector x})\<guillemotright>\<lbrakk>B1\<rbrakk>) \<sqinter> (CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> span {basis_vector 1}\<guillemotright>\<lbrakk>A1\<rbrakk>) + CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> ortho (span {basis_vector 1})\<guillemotright>\<lbrakk>A1\<rbrakk>) \<and> (x = 0 \<longrightarrow> \<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> span {EPR}\<guillemotright>\<lbrakk>A1, B1\<rbrakk> \<le> (INF x. (\<CC>\<ll>\<aa>[x = 0] + quantum_equality_full Z \<lbrakk>B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>) \<sqinter> (\<CC>\<ll>\<aa>[x = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) \<sqinter> span {basis_vector x}\<guillemotright>\<lbrakk>B1\<rbrakk> + ortho (span {basis_vector x})\<guillemotright>\<lbrakk>B1\<rbrakk>) \<sqinter> (CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> span {basis_vector 0}\<guillemotright>\<lbrakk>A1\<rbrakk>) + CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> ortho (span {basis_vector 0})\<guillemotright>\<lbrakk>A1\<rbrakk>)"
proof -
  have                         "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk>" and "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>C1\<rbrakk>" and "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A1\<rbrakk>"                        and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>C1\<rbrakk>" and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk>" and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk>"                        and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>A1\<rbrakk>" and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>B1\<rbrakk>" and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>C1\<rbrakk>"
    using assms by (auto intro: colocal_sym)
  note colocals = this colocal_split1 colocal_split2
  show ?thesis
    apply (simp add: prepare_for_code colocals)
    using[[show_brackets]]

    apply normalization
    done
qed
*)

lemma [code]: "mat_of_bounded (remove_qvar_unit_op::('a::enum*unit,_)bounded) = one_mat (enum_len TYPE('a))"
  sorry


lemma teleport_goal1:
  assumes[simp]: "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk> \<and> colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk> \<and> colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk>"
  shows
    "quantum_equality_full (addState EPR*) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>
      \<le> CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> (H\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> quantum_equality_full (addState EPR* \<cdot> (assoc_op* \<cdot> (CNOT \<otimes> idOp \<cdot> (assoc_op \<cdot> H \<otimes> idOp)))) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>)"
proof -
  have H: "H \<otimes> idOp \<cdot> H \<otimes> idOp = idOp" by simp
  have CNOT: "CNOT \<otimes> idOp \<cdot> CNOT \<otimes> idOp = idOp" by simp
  show ?thesis
    using [[simproc del: warn_colocal]]
    by (simp add: colocal_split1 colocal_split2 timesOp_assoc sort_lift
        lift_extendR[where U=H and R="\<lbrakk>A1,B1\<rbrakk>"] lift_extendR[where U=CNOT and R="\<lbrakk>B1\<rbrakk>"]
        assoc_replace[OF H] assoc_replace[OF UadjU] assoc_replace[OF CNOT] assoc_replace[OF adjUU])
qed


lemma teleport_goal2:
  assumes "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk> \<and> colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk> \<and> colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk> \<and> colocal \<lbrakk>A1\<rbrakk> \<lbrakk>A2\<rbrakk> \<and> colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<and> colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A2\<rbrakk>"
  shows "quantum_equality_full (addState EPR* \<cdot> (assoc_op* \<cdot> (CNOT \<otimes> idOp \<cdot> (assoc_op \<cdot> H \<otimes> idOp)))) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk> 
         \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> span {basis_vector 0}\<guillemotright>\<lbrakk>A1\<rbrakk> + ortho (span {basis_vector 0}\<guillemotright>\<lbrakk>A1\<rbrakk>)"
proof -
  have                         "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk>" and "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>C1\<rbrakk>" and "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A1\<rbrakk>"                        and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>C1\<rbrakk>" and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk>" and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk>"                        and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>A1\<rbrakk>" and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>B1\<rbrakk>" and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: colocal_split1 colocal_split2 intro: distinct_qvars_swap)
  note colocals = this colocal_split1 colocal_split2
  show ?thesis
    apply (simp add: prepare_for_code colocals)
    (* apply eval *)
    (* apply normalization *)

    oops

    term "(idOp \<cdot> Proj (span {basis_vector a1}) \<cdot> idOp)\<guillemotright>\<lbrakk>C1,A1,B1\<rbrakk> "

lemma
  assumes "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk> \<and> colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk> \<and> colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk> \<and> colocal \<lbrakk>A1\<rbrakk> \<lbrakk>A2\<rbrakk> \<and> colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<and> colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A2\<rbrakk>"
  assumes a1: "a1 = 0"
  shows "Proj (span {basis_vector a1})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
          quantum_equality_full idOp \<lbrakk>C1,A1,B1\<rbrakk>
          ((H \<otimes> idOp) \<cdot> assoc_op* \<cdot> (CNOT \<otimes> idOp) \<cdot> assoc_op \<cdot> addState EPR) \<lbrakk>A2\<rbrakk> \<le>

          quantum_equality_full idOp \<lbrakk>C1,A1,B1\<rbrakk>
          (
(idOp \<otimes> (Proj (span {basis_vector a1}) \<otimes> idOp)) \<cdot> 
(H \<otimes> idOp) \<cdot> assoc_op* \<cdot> (CNOT \<otimes> idOp) \<cdot> assoc_op \<cdot> addState EPR) \<lbrakk>A2\<rbrakk>
"
proof -
  have                         "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk>" and "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>C1\<rbrakk>" and "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A1\<rbrakk>"                        and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>C1\<rbrakk>" and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk>" and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk>"                        and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>A1\<rbrakk>" and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>B1\<rbrakk>" and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: colocal_split1 colocal_split2 intro: distinct_qvars_swap)
  note colocals = this colocal_split1 colocal_split2
  show ?thesis
    unfolding a1
    (* using[[simp_trace_new]] *)
    apply (simp add: prepare_for_code colocals)
    (* apply normalization *)
  find_theorems "(_::(_,_) bounded) \<cdot> quantum_equality_full  _ _ _ _"


  oops

lemma scalar_op_subspace [simp]: 
  fixes \<alpha>::complex and A::"(_,_)bounded" and S::"_ subspace"
  shows "(\<alpha>\<cdot>A)\<cdot>S = \<alpha>\<cdot>(A\<cdot>S)"
  sorry

lemma
  fixes C1 A1 B1 A2 :: "bit qvariable"
  assumes qvars[simp]: "distinct_qvars \<lbrakk>C1,A1,B1,A2\<rbrakk>"
  shows "Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> (Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
      quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op \<cdot> addState (state_to_vector EPR)) \<lbrakk>A2\<rbrakk>) 
        \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>" (is "?lhs \<le> ?rhs")
proof -
   have                         "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk>" and "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>C1\<rbrakk>" and "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A1\<rbrakk>"                        and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>C1\<rbrakk>" and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk>" and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk>"                        and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>A1\<rbrakk>" and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>B1\<rbrakk>" and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>C1\<rbrakk>"
    using assms using [[simproc del: warn_colocal]] by (auto simp: colocal_split1 colocal_split2 intro: distinct_qvars_swap)
  note colocals = this colocal_split1 colocal_split2
  have "quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op \<cdot> addState (state_to_vector EPR)) \<lbrakk>A2\<rbrakk>
      = (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op)\<guillemotright>\<lbrakk>C1,A1,B1\<rbrakk> \<cdot> quantum_equality_full idOp \<lbrakk>C1, A1, B1\<rbrakk> ( addState (state_to_vector EPR)) \<lbrakk>A2\<rbrakk>"
  (is "_ = ?outside0")
    apply (auto simp: prepare_for_code colocals)
    by eval
  have "?outside0 =
 (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op)\<guillemotright>\<lbrakk>C1,A1,B1\<rbrakk> \<cdot> (Qeq[C1=A2] \<sqinter> (lift (span {EPR}) \<lbrakk>A1,B1\<rbrakk>))" (is "_ = ?outside")
    apply (auto simp: prepare_for_code colocals)
    by eval

  have "?lhs = Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> (Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> ?outside)" (is "_ = ?newrhs")
    apply (auto simp: prepare_for_code colocals)
    by eval

  define C1A2 where "C1A2 = map vec_of_list [ [1::complex,0,0,0], [0,1,1,0], [0,0,0,1] ]"

  have "Qeq[C1=A2] = SPAN C1A2\<guillemotright>\<lbrakk>C1, A2\<rbrakk>" 
    unfolding C1A2_def
    apply (auto simp: prepare_for_code colocals)
    by eval

  have "?lhs = Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> (Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
        (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op)\<guillemotright>\<lbrakk>C1,A1,B1\<rbrakk> \<cdot> (SPAN C1A2\<guillemotright>\<lbrakk>C1,A2\<rbrakk> \<sqinter> (lift (span {EPR}) \<lbrakk>A1,B1\<rbrakk>)))"
    apply (auto simp: C1A2_def prepare_for_code colocals)
    by eval

    define C1A2' where "C1A2' = map vec_of_list [ [0::complex,1,1,0] ]"

    have "SPAN C1A2'\<guillemotright>\<lbrakk>C1,A2\<rbrakk> \<sqinter> (lift (span {EPR}) \<lbrakk>A1,B1\<rbrakk>)
= SPAN (map vec_of_list [ [0,0,0,0, 1,0,0,1, 1,0,0,1, 0,0,0,0] ])\<guillemotright>\<lbrakk>A2,C1,A1,B1\<rbrakk>  "
    apply (auto simp: C1A2'_def prepare_for_code colocals)
    by eval

  have "
        (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op)\<guillemotright>\<lbrakk>C1,A1,B1\<rbrakk> \<cdot> ( SPAN (map vec_of_list [ [0,0,0,0, 1,0,0,1, 1,0,0,1, 0,0,0,0] ])\<guillemotright>\<lbrakk>A2,C1,A1,B1\<rbrakk>)
=
        (H \<otimes> idOp)\<guillemotright>\<lbrakk>C1,A1,B1\<rbrakk> \<cdot> ( SPAN (map vec_of_list [ [0,0,0,0, 0,1,1,0, 1,0,0,1, 0,0,0,0] ])\<guillemotright>\<lbrakk>A2,C1,A1,B1\<rbrakk>)
"
    apply (auto simp: C1A2'_def prepare_for_code colocals)
    by eval

(* 0101 + 0110 + 1000 + 1011 *)
(* 0001. - 0101. + 0010? - 0110. + 1000. + 1100. + 1011. + 1111. *)

  have "
        (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op)\<guillemotright>\<lbrakk>C1,A1,B1\<rbrakk> \<cdot> ( SPAN (map vec_of_list [ [0,0,0,0, 1,0,0,1, 1,0,0,1, 0,0,0,0] ])\<guillemotright>\<lbrakk>A2,C1,A1,B1\<rbrakk>)
=
         ( SPAN [vec_of_list [0, 0, 1, - 1,   1, 1, 0, 0,   1, - 1, 0, 0,   0, 0, 1, 1] ]\<guillemotright>\<lbrakk>A1,A2,B1,C1\<rbrakk>)
"
    apply (auto simp: C1A2'_def prepare_for_code colocals)
    by eval

(* 0010. - 0011. + 0100. + 0101. + 1000. - 1001 + 1110. + 1111. *)
  
  have "Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> (Proj (span {basis_vector 0})\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> 
         ( SPAN [vec_of_list [0, 0, 1, - 1,   1, 1, 0, 0,   1, - 1, 0, 0,   0, 0, 1, 1] ]\<guillemotright>\<lbrakk>A1,A2,B1,C1\<rbrakk>) )
=
( 
         ( SPAN [vec_of_list [0, 0, 0, - 1,   1, 1, 0, 0,   0, 0, 0, 0,  0,0,0,0] ]\<guillemotright>\<lbrakk>A1,A2,B1,C1\<rbrakk>) )
"
    apply (auto simp: C1A2'_def prepare_for_code colocals)
    by eval

  have "
SPAN [vec_of_list [0, 0, 0, - 1,   1, 1, 0, 0,   0, 0, 0, 0,  0,0,0,0] ]\<guillemotright>\<lbrakk>A1,A2,B1,C1\<rbrakk>

        (* (H \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op)\<guillemotright>\<lbrakk>C1,A1,B1\<rbrakk> \<cdot> ( SPAN (map vec_of_list [ [0,0,0,0, 1,0,0,1, 1,0,0,1, 0,0,0,0] ])\<guillemotright>\<lbrakk>A2,C1,A1,B1\<rbrakk>))  *)
\<le> ?rhs"
    apply (auto simp: C1A2'_def prepare_for_code colocals)
    apply normalization

(* -0011  0100  0101 *)

(*     apply (subst op_scalar_op)
    apply (subst timesScalarSpace_not0)
using [[show_brackets]]
    apply (rewrite at "_ (_ (1/sqrt2) _) _" DEADID.rel_mono_strong)
     apply (rewrite at "_ _ \<hole> = _" DEADID.rel_mono_strong[where y=a]) defer
  apply (rewrite at "_ (_ _ \<hole>) _ = _" DEADID.rel_mono_strong[where y=b]) defer

    apply (subst scalar_op_op)
    find_theorems "?x = ?y \<Longrightarrow> ?x = ?y"
    find_theorems "(_::complex) \<cdot> (_::_subspace)"
    find_theorems " ((_::complex) \<cdot> (_::(_,_)bounded)) \<cdot> (_::(_,_)bounded)"
 *)
    by eval


(*   show ?thesis
    apply (auto simp: prepare_for_code colocals)
    apply normalization *)

    oops


end


