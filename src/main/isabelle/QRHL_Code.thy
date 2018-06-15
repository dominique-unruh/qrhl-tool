theory QRHL_Code
  imports QRHL_Core "Jordan_Normal_Form.Matrix_Impl" "HOL-Library.Code_Target_Numeral"
begin

(* Hiding constants/syntax that were overwritten by Jordan_Normal_Form *)
hide_const (open) Lattice.sup
hide_const (open) Lattice.inf
hide_const (open) Order.top
hide_const (open) card_UNIV
hide_const (open) Coset.kernel
no_syntax "\<^const>Group.monoid.mult"    :: "['a, 'a, 'a] \<Rightarrow> 'a" (infixl "\<otimes>\<index>" 70)
no_syntax "\<^const>Lattice.meet" :: "[_, 'a, 'a] => 'a" (infixl "\<sqinter>\<index>" 70)


axiomatization bounded_of_mat :: "complex mat \<Rightarrow> ('a::enum,'b::enum) bounded"
  and mat_of_bounded :: "('a::enum,'b::enum) bounded \<Rightarrow> complex mat"
axiomatization vector_of_vec :: "complex vec \<Rightarrow> ('a::enum) vector"
  and vec_of_vector :: "('a::enum) vector \<Rightarrow> complex vec"

axiomatization where mat_of_bounded_inverse [code abstype]:
  "bounded_of_mat (mat_of_bounded B) = B" for B::"('a::enum,'b::enum)bounded"

axiomatization where vec_of_vector_inverse [code abstype]:
  "vector_of_vec (vec_of_vector B) = B" for B::"('a::enum)vector"


fun index_of where
  "index_of x [] = (0::nat)"
| "index_of x (y#ys) = (if x=y then 0 else (index_of x ys + 1))"

definition "enum_idx (x::'a::enum) = index_of x (enum_class.enum :: 'a list)"
(* definition "enum_len (TYPE('a::enum)) = length (enum_class.enum :: 'a list)" *)

axiomatization where bounded_of_mat_id[code]:
  "mat_of_bounded (idOp :: ('a::enum,'a) bounded) = one_mat (CARD('a))"
axiomatization where bounded_of_mat_timesOp[code]:
  "mat_of_bounded (M \<cdot> N) =  (mat_of_bounded M * mat_of_bounded N)" for M::"('b::enum,'c::enum) bounded" and N::"('a::enum,'b) bounded"
axiomatization where bounded_of_mat_plusOp[code]:
  "mat_of_bounded (M + N) =  (mat_of_bounded M + mat_of_bounded N)" for M::"('a::enum,'b::enum) bounded" and N::"('a::enum,'b) bounded"
axiomatization where bounded_of_mat_minusOp[code]:
  "mat_of_bounded (M - N) =  (mat_of_bounded M - mat_of_bounded N)" 
  for M::"('a::enum,'b::enum) bounded" and N::"('a::enum,'b) bounded"
axiomatization where bounded_of_mat_uminusOp[code]:
  "mat_of_bounded (- M) = - mat_of_bounded M" for M::"('a::enum,'b::enum) bounded"
axiomatization where vector_of_vec_applyOp[code]:
  "vec_of_vector (M \<cdot> x) =  (mult_mat_vec (mat_of_bounded M) (vec_of_vector x))" for M :: "('a::enum,'b::enum) bounded"
axiomatization where mat_of_bounded_scalarMult[code]:
  "mat_of_bounded ((a::complex) \<cdot> M) = smult_mat a (mat_of_bounded M)" for M :: "('a::enum,'b::enum) bounded"

axiomatization where mat_of_bounded_inj: "inj mat_of_bounded"
instantiation bounded :: (enum,enum) equal begin
definition [code]: "equal_bounded M N \<longleftrightarrow> mat_of_bounded M = mat_of_bounded N" for M N :: "('a,'b) bounded"
instance 
  apply intro_classes
  unfolding equal_bounded_def 
  using mat_of_bounded_inj injD by fastforce 
end

axiomatization where vec_of_vector_inj: "inj vec_of_vector"
instantiation vector :: (enum) equal begin
definition [code]: "equal_vector M N \<longleftrightarrow> vec_of_vector M = vec_of_vector N" for M N :: "'a vector"
instance 
  apply intro_classes
  unfolding equal_vector_def 
  using vec_of_vector_inj injD by fastforce 
end



definition "matrix_X = mat_of_rows_list 2 [ [0::complex,1], [1,0] ]"
axiomatization where bounded_of_mat_X[code]: "mat_of_bounded pauliX = matrix_X"
definition "matrix_Z = mat_of_rows_list 2 [ [1::complex,0], [0,-1] ]"
axiomatization where bounded_of_mat_Z[code]: "mat_of_bounded pauliZ = matrix_Z"
definition "matrix_Y = mat_of_rows_list 2 [ [0::complex,-\<i>], [\<i>,0] ]"
axiomatization where bounded_of_mat_Y[code]: "mat_of_bounded pauliY = matrix_Y"
definition "matrix_H' = mat_of_rows_list 2 [ [1::complex, 1], [1, -1] ]"
axiomatization where bounded_of_mat_H'[code]: "mat_of_bounded hadamard' = matrix_H'"
definition "matrix_CNOT = mat_of_rows_list 4 [ [1::complex,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0] ]"
axiomatization where bounded_of_mat_CNOT[code]: "mat_of_bounded CNOT = matrix_CNOT"

definition "matrix_tensor (A::'a::times mat) (B::'a mat) =
  mat (dim_row A*dim_row B) (dim_col A*dim_col B) 
  (\<lambda>(r,c). A $$ (r div dim_row B, c div dim_col B) *
           B $$ (r mod dim_row B, c mod dim_col B))"

axiomatization where bounded_of_mat_tensorOp[code]:
  "mat_of_bounded (tensorOp A B) = matrix_tensor (mat_of_bounded A) (mat_of_bounded B)"
for A :: "('a::enum,'b::enum) bounded"
and B :: "('c::enum,'d::enum) bounded"

definition "adjoint_mat M = transpose_mat (map_mat cnj M)"
axiomatization where bounded_of_mat_adjoint[code]:
  "mat_of_bounded (adjoint A) = adjoint_mat (mat_of_bounded A)"
for A :: "('a::enum,'b::enum) bounded"

axiomatization where bounded_of_mat_assoc_op[code]: 
  "mat_of_bounded (assoc_op :: ('a::enum*'b::enum*'c::enum,_) bounded) = one_mat (Enum.card_UNIV TYPE('a)*Enum.card_UNIV TYPE('b)*Enum.card_UNIV TYPE('c))"

definition "comm_op_mat TYPE('a::enum) TYPE('b::enum) =
  (let da = Enum.card_UNIV TYPE('a); db = Enum.card_UNIV TYPE('b) in
  mat (da*db) (da*db)
  (\<lambda>(r,c). (if (r div da = c mod db \<and>
                r mod da = c div db) then 1 else 0)))"

axiomatization where bounded_of_mat_comm_op[code]:
  "mat_of_bounded (comm_op :: ('a::enum*'b::enum,_) bounded) = comm_op_mat TYPE('a) TYPE('b)"

axiomatization where vec_of_vector_zero[code]:
  "vec_of_vector (0::'a::enum vector) = zero_vec (CARD('a))"


axiomatization where vec_of_vector_ket[code]:
  "vec_of_vector (ket i) = unit_vec (CARD('a)) (enum_idx i)" for i::"'a::enum"

instantiation bit :: linorder begin
definition "less_bit (a::bit) (b::bit) = (a=0 \<and> b=1)"
definition "less_eq_bit (a::bit) b = (a=b \<or> a<b)"
instance apply intro_classes unfolding less_bit_def less_eq_bit_def by auto
end



instantiation bit :: card_UNIV begin
definition "finite_UNIV_bit = Phantom(bit) True"
definition "card_UNIV_bit = Phantom(bit) (2::nat)"
instance apply intro_classes unfolding finite_UNIV_bit_def card_UNIV_bit_def 
  apply auto unfolding UNIV_bit by simp 
end

axiomatization where mat_of_bounded_zero[code]:
  "mat_of_bounded (0::('a::enum,'b::enum) bounded) = zero_mat (CARD('b)) (CARD('a))"

definition "computational_basis_vec n = map (unit_vec n) [0..<n]"
definition "orthogonal_complement_vec n vs = 
  filter (op\<noteq> (zero_vec n)) (drop (length vs) (gram_schmidt n (vs @ computational_basis_vec n)))"

definition "vec_tensor (A::'a::times vec) (B::'a vec) =
  vec (dim_vec A*dim_vec B) 
  (\<lambda>r. vec_index A (r div dim_vec B) *
       vec_index B (r mod dim_vec B))"


axiomatization where tensorVec_code[code]: "vec_of_vector (\<psi> \<otimes> \<phi>) = vec_tensor (vec_of_vector \<psi>) (vec_of_vector \<phi>)"
  for \<psi>::"'a::enum vector" and \<phi>::"'b::enum vector"

definition [code del]: "SPAN x = span (vector_of_vec ` set x)"
code_datatype SPAN

definition "mk_projector (S::'a::enum subspace) = mat_of_bounded (Proj S)" 
fun mk_projector_orthog :: "nat \<Rightarrow> complex vec list \<Rightarrow> complex mat" where
  "mk_projector_orthog d [] = zero_mat d d"
| "mk_projector_orthog d [v] = (let norm2 = cscalar_prod v v in
                                if norm2=0 then zero_mat d d else
                                smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [v]))"
| "mk_projector_orthog d (v#vs) = (let norm2 = cscalar_prod v v in
                                   if norm2=0 then mk_projector_orthog d vs else
                                   smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [v]) 
                                        + mk_projector_orthog d vs)"

axiomatization where mk_projector_SPAN[code]: 
  "mk_projector (SPAN S :: 'a::enum subspace) = 
    (let d = CARD('a) in mk_projector_orthog d (gram_schmidt d S))"

(*axiomatization where mk_projector_SPAN[code]: "mk_projector (SPAN S :: 'a::enum subspace) = (case S of 
    [v] \<Rightarrow> (let d = dim_vec v in let norm2 = cscalar_prod v v in
                if norm2=0 then zero_mat d d else
                            smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [v]))
  | _ \<Rightarrow> Code.abort (STR ''Computation of 'Proj S' only implemented for singleton S'') (\<lambda>_. mat_of_bounded (Proj (SPAN S :: 'a subspace))))"*)

lemma [code]: "mat_of_bounded (Proj S) = mk_projector S" for S :: "'a::enum subspace"
  unfolding mk_projector_def by simp


axiomatization where top_as_span[code]: "(top::'a subspace) = SPAN (computational_basis_vec (CARD('a::enum)))"
axiomatization where bot_as_span[code]: "(bot::'a::enum subspace) = SPAN []" 
axiomatization where plus_spans[code]: "SPAN A + SPAN B = SPAN (A @ B)" 

axiomatization where ortho_SPAN[code]: "ortho (SPAN S :: 'a::enum subspace) = SPAN (orthogonal_complement_vec (CARD('a)) S)"
axiomatization where span_Set_Monad[code]: "span (Set_Monad l) = SPAN (map vec_of_vector l)"
  for l :: "'a::enum vector list"
axiomatization where tensorSpace_SPAN[code]: "tensorSpace (SPAN A) (SPAN B) = SPAN [vec_tensor a b. a<-A, b<-B]"

axiomatization where vec_of_vector_timesScalarVec[code]: "vec_of_vector (timesScalarVec a \<psi>) = smult_vec a (vec_of_vector \<psi>)"
  for \<psi> :: "'a::enum vector"

axiomatization where vector_of_vec_plus[code]:
  "vec_of_vector (x + y) =  (vec_of_vector x) + (vec_of_vector y)" for x y :: "'a::enum vector"

axiomatization where vec_of_vector_EPR'[code]: "vec_of_vector EPR' = vec_of_list [1,0,0,1]"

lemma [code_post]: 
  shows "Complex a 0 = complex_of_real a"
  and "complex_of_real 0 = 0"
  and "complex_of_real 1 = 1"
  and "complex_of_real (a/b) = complex_of_real a / complex_of_real b"
  and "complex_of_real (numeral n) = numeral n"
  and "complex_of_real (-r) = - complex_of_real r"
  using complex_eq_cancel_iff2 by auto

instantiation subspace :: (enum) equal begin
definition [code del]: "equal_subspace (A::'a subspace) B = (A=B)"
instance apply intro_classes unfolding equal_subspace_def by simp
end

definition "is_subspace_of n vs ws =  
  list_all (op= (zero_vec n)) (drop (length ws) (gram_schmidt n (ws @ vs)))"

axiomatization where SPAN_leq[code]: "SPAN A \<le> (SPAN B :: 'a subspace) \<longleftrightarrow> is_subspace_of (CARD('a::enum)) A B" 

axiomatization where applyOpSpace_SPAN[code]: "applyOpSpace A (SPAN S) = SPAN (map (mult_mat_vec (mat_of_bounded A)) S)"
  for A::"('a::enum,'b::enum) bounded"

axiomatization where kernel_SPAN[code]: "kernel A = SPAN (find_base_vectors (gauss_jordan_single (mat_of_bounded A)))" 
  for A::"('a::enum,'b::enum) bounded"

lemma [code_abbrev]: "kernel (A-a\<cdot>idOp) = eigenspace a A" 
  unfolding eigenspace_def by simp

axiomatization where mat_of_bounded_classical_operator[code]: 
  "mat_of_bounded (classical_operator f) = mat (CARD('b)) (CARD('a))
  (\<lambda>(r,c). if f (Enum.enum!c) = Some (Enum.enum!r) then 1 else 0)" 
  for f::"'a::enum \<Rightarrow> 'b::enum option"

lemma [code]: "HOL.equal (A::_ subspace) B = (A\<le>B \<and> B\<le>A)"
  unfolding equal_subspace_def by auto


axiomatization where mat_of_bounded_vector_to_bounded[code]: "mat_of_bounded (vector_to_bounded \<psi>) = mat_of_cols (CARD('a)) [vec_of_vector \<psi>]" 
  for \<psi>::"'a::enum vector"

axiomatization where mat_of_bounded_remove_qvar_unit_op[code]:
  "mat_of_bounded (remove_qvar_unit_op::(_,'a::enum) bounded) = mat_of_bounded (idOp::(_,'a) bounded)" 

lemma [code]: "(A::'a subspace) \<sqinter> B = ortho (ortho A + ortho B)"
  unfolding subspace_sup_plus[symmetric]
  by (smt inf.absorb2 inf.orderE inf_assoc_subspace inf_sup_ord(1) inf_sup_ord(2) leq_plus_subspace leq_plus_subspace2 ortho_leq ortho_twice subspace_plus_sup subspace_sup_plus)

lemma [code]: "Inf (Set_Monad l :: 'a subspace set) = fold inf l top"
  unfolding Set_Monad_def
  by (simp add: Inf_set_fold)

declare [[code drop: UNIV]]
declare enum_class.UNIV_enum[code]

declare ord_subspace_inst.less_eq_subspace[code del]
declare ord_subspace_inst.less_subspace[code del]

derive (eq) ceq bit
derive (linorder) compare_order bit
derive (compare) ccompare bit
derive (dlist) set_impl bit
derive (eq) ceq real
derive (linorder) compare real
derive (compare) ccompare real
derive (eq) ceq complex
derive (no) ccompare complex
derive (eq) ceq subspace
derive (no) ccompare subspace
derive (monad) set_impl subspace
derive (eq) ceq vector
derive (no) ccompare vector
derive (monad) set_impl vector


lemmas prepare_for_code = H_H' quantum_equality_full_def add_join_variables_hint space_div_space_div_unlifted
  space_div_add_extend_lift_as_var_concat_hint INF_lift EPR_EPR' Cla_inf_lift Cla_plus_lift

end
