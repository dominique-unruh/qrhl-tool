theory Teleport
  imports QRHL_Protocol
begin

find_theorems "_ = zero_vec _"

definition "computational_basis_vec n = map (unit_vec n) [0..<n]"
definition "orthogonal_complement_vec n vs = 
  filter (op\<noteq> (zero_vec n)) (drop (length vs) (gram_schmidt n (vs @ computational_basis_vec n)))"


value [nbe] "orthogonal_complement_vec 3 [vec_of_list [1::real,1,0], vec_of_list [1,1,0] ]"    
    
    term finsum

definition [code]: "testA = (mat_of_rows_list 2 [ [1,1],[1,1] ] :: complex mat)"
(* How to find a basis for the kernel of testA: *)
value "find_base_vectors (gauss_jordan_single testA)"


term find_base_vectors

declare[[quick_and_dirty]]

lemma tensor_times[simp]: "(U1 \<otimes> U2) \<cdot> (V1 \<otimes> V2) = (U1 \<cdot> V1) \<otimes> (U2 \<cdot> V2)"
  for U1 U2 V1 V2 :: "(_,_) bounded"
  sorry

axiomatization addState :: "'a vector \<Rightarrow> ('b,'b*'a) bounded"

axiomatization EPR :: "(bit*bit) state" 

lemma applyOpSpace_colocal[simp]:
  fixes U :: "(mem2,mem2) bounded" and S :: predicate
  assumes "colocal_op_pred U S"
  shows "U \<cdot> S = S"
  sorry

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

lemma teleport_goal1:
  assumes "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk> \<and> colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk> \<and> colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk>"
  shows
    "quantum_equality_full (addState EPR*) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>
      \<le> CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> (H\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> quantum_equality_full (addState EPR* \<cdot> (assoc_op* \<cdot> (CNOT \<otimes> idOp \<cdot> (assoc_op \<cdot> H \<otimes> idOp)))) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk>)"
proof -
  have H: "H \<otimes> idOp \<cdot> H \<otimes> idOp = idOp" by simp
  have CNOT: "CNOT \<otimes> idOp \<cdot> CNOT \<otimes> idOp = idOp" by simp
  show ?thesis
    by (simp add: colocal_split1 colocal_split2 assms timesOp_assoc
        lift_extendR[where U=H and R="\<lbrakk>A1,B1\<rbrakk>"] lift_extendR[where U=CNOT and R="\<lbrakk>B1\<rbrakk>"]
        assoc_replace[OF H] assoc_replace[OF UadjU] assoc_replace[OF CNOT] assoc_replace[OF adjUU])
qed

(* axiomatization Proj :: "'a subspace \<Rightarrow> ('a,'a) bounded" where
  isProjector_Proj[simp]: "isProjector (Proj S)"
and imageOp_Proj[simp]: "applyOpSpace (Proj S) top = S"

lemma move_plus:
  assumes "Proj (ortho C) \<cdot> A \<le> B"
  shows "A \<le> B + C"
  sorry

lemma Proj_lift[simp]: "Proj (S\<guillemotright>Q) = (Proj S)\<guillemotright>Q"
  sorry *)


axiomatization eigenspace :: "complex \<Rightarrow> ('a,'a) bounded \<Rightarrow> 'a subspace"
axiomatization kernel :: "('a,'b) bounded \<Rightarrow> 'a subspace"

lemma quantum_equality_full_subspace:
  "colocal Q R \<Longrightarrow> quantum_equality_full U Q V R = (eigenspace 1 (comm_op \<cdot> (V*\<cdot>U)\<otimes>(U*\<cdot>V))) \<guillemotright> qvariable_concat Q R"
  for Q :: "'a qvariables" and R :: "'b qvariables"
  and U V :: "(_,'c) bounded"
  using [[show_types,show_sorts,show_consts,show_brackets]]
  sorry

  

lemma colocal_sym: "colocal Q R \<Longrightarrow> colocal R Q" for Q :: "'a qvariables" and R :: "'b qvariables" sorry

definition "reorder_qvars x (Q::'a qvariables) (R::'b qvariables) = x"

lemma add_reorder_qvars: 
  shows "NO_MATCH (a,a) (Q,R) \<Longrightarrow> S\<guillemotright>Q \<sqinter> T\<guillemotright>R = reorder_qvars (S\<guillemotright>Q) Q R \<sqinter> reorder_qvars (T\<guillemotright>R) Q R"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> S\<guillemotright>Q + T\<guillemotright>R = reorder_qvars (S\<guillemotright>Q) Q R + reorder_qvars (T\<guillemotright>R) Q R"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (S\<guillemotright>Q \<le> T\<guillemotright>R) = (reorder_qvars (S\<guillemotright>Q) Q R \<le> reorder_qvars (T\<guillemotright>R) Q R)"
  unfolding reorder_qvars_def by simp_all

term classical_operator

lemma reorder_qvars_subspace:
  fixes Q :: "'a qvariables" and R :: "'b qvariables"
  fixes A1 :: "'a1 qvariable" and A2 :: "'a2 qvariable" and B1 :: "'b1 qvariable" and C1 :: "'c1 qvariable" 
  fixes S S' T S1 T1 :: "_ subspace"
  shows "colocal Q R \<Longrightarrow> reorder_qvars (S\<guillemotright>Q) Q R = (S\<otimes>top) \<guillemotright> qvariable_concat Q R" 
  and "colocal Q R \<Longrightarrow> reorder_qvars (T\<guillemotright>R) Q R = (top\<otimes>T) \<guillemotright> qvariable_concat Q R"
  and "colocal Q R \<Longrightarrow> reorder_qvars (S'\<guillemotright>qvariable_concat Q R) (qvariable_concat Q R) R = (S'\<guillemotright>qvariable_concat Q R)"
  and "colocal Q R \<Longrightarrow> reorder_qvars (T\<guillemotright>R) (qvariable_concat Q R) R = (top\<otimes>T) \<guillemotright> qvariable_concat Q R"
  and "reorder_qvars (S1\<guillemotright>qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>) (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>) (qvariable_concat \<lbrakk>B1, A2\<rbrakk> \<lbrakk>A1\<rbrakk>)
            = (comm_op \<cdot> S1) \<guillemotright> \<lbrakk>A2,C1,A1,B1\<rbrakk>"
  and "reorder_qvars (T1\<guillemotright>(qvariable_concat \<lbrakk>B1, A2\<rbrakk> \<lbrakk>A1\<rbrakk>)) (qvariable_concat \<lbrakk>C1, A1, B1\<rbrakk> \<lbrakk>A2\<rbrakk>) (qvariable_concat \<lbrakk>B1, A2\<rbrakk> \<lbrakk>A1\<rbrakk>)
            = (classical_operator (\<lambda>(c1,(b1,a2),a1). Some(a2,c1,a1,b1)) \<cdot> (top::'c1 subspace)\<otimes>T1) \<guillemotright> \<lbrakk>A2,C1,A1,B1\<rbrakk>"
  sorry

lemma lift_inf[simp]: "colocal Q \<lbrakk>\<rbrakk> \<Longrightarrow> S\<guillemotright>Q \<sqinter> T\<guillemotright>Q = (S \<sqinter> T)\<guillemotright>Q" sorry 
lemma lift_leq[simp]: "colocal Q \<lbrakk>\<rbrakk> \<Longrightarrow> (S\<guillemotright>Q \<le> T\<guillemotright>Q) = (S \<le> T)" sorry 
lemma lift_plus[simp]: "colocal Q \<lbrakk>\<rbrakk> \<Longrightarrow> S\<guillemotright>Q + T\<guillemotright>Q = (S + T)\<guillemotright>Q" for S T :: "'a subspace" sorry 
lemma lift_ortho[simp]: "colocal Q \<lbrakk>\<rbrakk> \<Longrightarrow> ortho (S\<guillemotright>Q) = (ortho S)\<guillemotright>Q" sorry
  (* by (metis bot_lift reorder_qvars_subspace(3) reorder_qvars_subspace(4) top_lift top_not_bot) sorry *)

definition [code del]: "SPAN x = spanVector (vector_of_vec ` set x)"
code_datatype SPAN

declare ord_subspace_inst.less_eq_subspace[code del]

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

value "1/2 :: complex"

definition "is_subspace_of n vs ws =  
  list_all (op= (zero_vec n)) (drop (length ws) (gram_schmidt n (ws @ vs)))"
term matrix_X
lemma [code]: "SPAN A \<le> (SPAN B :: 'a subspace) \<longleftrightarrow> is_subspace_of (enum_len TYPE('a::enum)) A B" sorry
lemma [code]: "applyOpSpace A (SPAN S) = SPAN (map (mult_mat_vec (mat_of_bounded A)) S)" sorry
lemma [code]: "kernel A = SPAN (find_base_vectors (gauss_jordan_single (mat_of_bounded A)))" sorry
lemma [code]: "(mat_of_bounded (classical_operator f :: ('a,'b)bounded)) = mat (enum_len TYPE('b::enum)) (enum_len TYPE('a::enum))
  (\<lambda>(r,c). if f (Enum.enum!c) = Some (Enum.enum!r) then 1 else 0)" sorry

(* lemma [code]: "SPAN A = (SPAN B :: 'a::enum subspace) \<longleftrightarrow>
  ((SPAN A::'a subspace) \<le> (SPAN B::'a subspace)) \<and> ((SPAN B::'a subspace) \<le> (SPAN A::'a subspace))" by auto *)

lemma [code_abbrev]: "kernel (A-a\<cdot>idOp) = eigenspace a A" sorry
lemma [code_abbrev]: "ortho (ortho A + ortho B) = A \<sqinter> B" unfolding subspace_sup_plus[symmetric] sorry

lemma [simp]: "a\<noteq>0 \<Longrightarrow> eigenspace b (a\<cdot>A) = eigenspace (b/a) A" sorry
lemma [simp]: "eigenspace b 0 = Cla[b=0]" sorry
lemma [simp]: "(a \<cdot> A)* = cnj a \<cdot> (A*)" sorry
lemma [simp]: "addState (a \<cdot> \<psi>) = a \<cdot> addState \<psi>" for a::complex and psi::"'a vector" sorry
lemma [simp]: "cnj sqrt2 = sqrt2" sorry

value "classical_operator (\<lambda>(c1, (b1, a2), a1). Some (a2::bit, c1::bit, a1::bit, b1::bit)) \<cdot>
       top \<otimes> (eigenspace 1 comm_op \<otimes> top \<sqinter> top \<otimes> span {basis_vector 0} + top \<otimes> ortho (span {basis_vector 0}))"

(* lemma [code_post]: "n = length l \<Longrightarrow> vec_impl (Abs_vec_impl (n, IArray l)) = vec_of_list l" sorry *)




value "span { basis_vector (0::bit), (0.123::complex) \<cdot> basis_vector (1::bit)  } \<le> span { (0.123::complex) \<cdot> basis_vector (0::bit), H' \<cdot> basis_vector 1 } "


definition "px = (\<lambda>(x::'a,y::'a). (x,y))"


value "px (comm_op \<cdot>
    eigenspace 4
     (comm_op \<cdot>
      (addState EPR'* \<cdot> (assoc_op* \<cdot> (CNOT \<otimes> idOp \<cdot> (assoc_op \<cdot> H' \<otimes> idOp)))) \<otimes> (H'* \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op \<cdot> addState EPR'))
    , classical_operator (\<lambda>(c1, (b1, a2), a1). Some (a2, c1, a1, b1)) \<cdot>
       top \<otimes> (eigenspace 1 comm_op \<otimes> top \<sqinter> top \<otimes> span {basis_vector 0} + top \<otimes> ortho (span {basis_vector 0})))"


value "comm_op \<cdot>
    eigenspace 4
     (comm_op \<cdot>
      (addState EPR'* \<cdot> (assoc_op* \<cdot> (CNOT \<otimes> idOp \<cdot> (assoc_op \<cdot> H' \<otimes> idOp)))) \<otimes> (H'* \<otimes> idOp \<cdot> assoc_op* \<cdot> CNOT \<otimes> idOp \<cdot> assoc_op \<cdot> addState EPR'))
    \<le> classical_operator (\<lambda>(c1, (b1, a2), a1). Some (a2, c1, a1, b1)) \<cdot>
       top \<otimes> (eigenspace 1 comm_op \<otimes> top \<sqinter> top \<otimes> span {basis_vector 0} + top \<otimes> ortho (span {basis_vector 0}))"

lemmas prepare_for_code = H_H' quantum_equality_full_subspace add_reorder_qvars reorder_qvars_subspace EPR_EPR'
lemma teleport_goal2:
  assumes "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk> \<and> colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk> \<and> colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk> \<and> colocal \<lbrakk>A1\<rbrakk> \<lbrakk>A2\<rbrakk> \<and> colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A2\<rbrakk> \<and> colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A2\<rbrakk>"
  shows "quantum_equality_full (addState EPR* \<cdot> (assoc_op* \<cdot> (CNOT \<otimes> idOp \<cdot> (assoc_op \<cdot> H \<otimes> idOp)))) \<lbrakk>C1, A1, B1\<rbrakk> idOp \<lbrakk>A2\<rbrakk> 
         \<le> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> span {basis_vector 0}\<guillemotright>\<lbrakk>A1\<rbrakk> + ortho (span {basis_vector 0}\<guillemotright>\<lbrakk>A1\<rbrakk>)"
proof -
  have                         "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>B1\<rbrakk>" and "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>C1\<rbrakk>" and "colocal \<lbrakk>A1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A1\<rbrakk>"                        and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>C1\<rbrakk>" and "colocal \<lbrakk>B1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A1\<rbrakk>" and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>B1\<rbrakk>"                        and "colocal \<lbrakk>C1\<rbrakk> \<lbrakk>A2\<rbrakk>" 
    and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>A1\<rbrakk>" and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>B1\<rbrakk>" and "colocal \<lbrakk>A2\<rbrakk> \<lbrakk>C1\<rbrakk>"
    using assms by (auto intro: colocal_sym)
  note colocals = this colocal_split1 colocal_split2
  (* have spanket: "span {basis_vector 0} = span {ket 0}" by auto *)
  show ?thesis
    apply (simp add: prepare_for_code colocals)
    apply normalization







