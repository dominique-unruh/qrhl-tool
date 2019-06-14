theory QRHL_Code
  imports QRHL_Core "Jordan_Normal_Form.Matrix_Impl" "HOL-Library.Code_Target_Numeral"
begin

(* Hiding constants/syntax that were overwritten by Jordan_Normal_Form *)
hide_const (open) Lattice.sup
hide_const (open) Lattice.inf
hide_const (open) Order.top
hide_const (open) card_UNIV
hide_const (open) Coset.kernel
hide_const (open) Real_Vector_Spaces.span
no_notation "Order.bottom" ("\<bottom>\<index>")
no_notation "Order.top" ("\<top>\<index>")
no_notation "Lattice.meet" (infixl "\<sqinter>\<index>" 70)
no_notation "Lattice.join" (infixl "\<squnion>\<index>" 65)
hide_const (open) Order.bottom Order.top

named_theorems prepare_for_code \<open>Theorems to rewrite expressions involving bounded operators into expressions involving matrices (in order to make them executable)\<close>

no_syntax "\<^const>Group.monoid.mult"    :: "['a, 'a, 'a] \<Rightarrow> 'a" (infixl "\<otimes>\<index>" 70)
no_syntax "\<^const>Lattice.meet" :: "[_, 'a, 'a] => 'a" (infixl "\<sqinter>\<index>" 70)

consts mat_of_l2bounded :: "('a::basis_enum,'b::basis_enum) Bounded \<Rightarrow> complex mat"
       vec_of_ell2 :: "'a::basis_enum \<Rightarrow> complex vec"

(* consts l2bounded_of_mat :: "complex mat \<Rightarrow> ('a::basis_enum,'b::basis_enum) Bounded"
       mat_of_l2bounded :: "('a::basis_enum,'b::basis_enum) Bounded \<Rightarrow> complex mat"

(* Wrapper class so that we can define a code datatype constructors for that type (does not work with type synonyms) *)
typedef ('a::enum,'b::enum) code_l2bounded = "UNIV::('a,'b) l2bounded set" by simp

consts l2bounded_of_mat' :: "complex mat \<Rightarrow> ('a::enum,'b::enum) code_l2bounded"
       mat_of_l2bounded' :: "('a::enum,'b::enum) code_l2bounded \<Rightarrow> complex mat"

consts ell2_of_vec' :: "complex vec \<Rightarrow> 'a::basis_enum"
       vec_of_ell2' :: "'a::basis_enum \<Rightarrow> complex vec"

definition ell2_of_vec :: "complex vec \<Rightarrow> 'a::enum ell2" where "ell2_of_vec = ell2_of_vec'"
definition vec_of_ell2 :: "'a::enum ell2 \<Rightarrow> complex vec" where "vec_of_ell2 = vec_of_ell2'" *)



(* lemma mat_of_l2bounded_inverse [code abstype]:
  "l2bounded_of_mat (mat_of_l2bounded B) = B" 
  for B::"('a::basis_enum,'b::basis_enum)Bounded"
  by (cheat 15)

lemma mat_of_l2bounded_inverse' [code abstype]:
  "l2bounded_of_mat' (mat_of_l2bounded' B) = B" 
  by (cheat 15)

lemma [code]: "mat_of_l2bounded' (Abs_code_l2bounded X) = mat_of_l2bounded X"
  by (cheat 15)
lemma [code]: "mat_of_l2bounded (Rep_code_l2bounded X) = mat_of_l2bounded' X"
  by (cheat 15)

lemma vec_of_ell2_inverse [code abstype]:
  "ell2_of_vec (vec_of_ell2 B) = B" 
  by (cheat 15) *)

fun index_of where
  "index_of x [] = (0::nat)"
| "index_of x (y#ys) = (if x=y then 0 else (index_of x ys + 1))"

definition "enum_idx (x::'a::enum) = index_of x (enum_class.enum :: 'a list)"

lemma l2bounded_of_mat_id[prepare_for_code]:
  "mat_of_l2bounded (idOp :: ('a::basis_enum,'a) Bounded) = one_mat (canonical_basis_length TYPE('a))"
  by (cheat 15)

lemma l2bounded_of_mat_timesOp[prepare_for_code]:
  "mat_of_l2bounded (M \<cdot> N) =  (mat_of_l2bounded M * mat_of_l2bounded N)" 
  for M::"('b::basis_enum,'c::basis_enum) Bounded" and N::"('a::basis_enum,'b) Bounded"
  by (cheat 15)
lemma l2bounded_of_mat_plusOp[prepare_for_code]:
  "mat_of_l2bounded (M + N) =  (mat_of_l2bounded M + mat_of_l2bounded N)" 
  for M::"('a::basis_enum,'b::basis_enum) Bounded" and N::"('a::basis_enum,'b) Bounded"
  by (cheat 15)
lemma l2bounded_of_mat_minusOp[prepare_for_code]:
  "mat_of_l2bounded (M - N) =  (mat_of_l2bounded M - mat_of_l2bounded N)" 
  for M::"('a::basis_enum,'b::basis_enum) Bounded" and N::"('a::basis_enum,'b) Bounded"
  by (cheat 15)
lemma l2bounded_of_mat_uminusOp[prepare_for_code]:
  "mat_of_l2bounded (- M) = - mat_of_l2bounded M" for M::"('a::basis_enum,'b::basis_enum) Bounded"
  by (cheat 15)

(* definition [code del]: "applyOp_code M x = applyOp (Rep_code_l2bounded M) x"
lemma [symmetric,code_abbrev]: "applyOp M = applyOp_code (Abs_code_l2bounded M)"
  by (cheat 15) *)
lemma ell2_of_vec_applyOp[prepare_for_code]:
  "vec_of_ell2 (applyOp M x) = (mult_mat_vec (mat_of_l2bounded M) (vec_of_ell2 x))" 
  by (cheat 15)


lemma mat_of_l2bounded_scalarMult[prepare_for_code]:
  "mat_of_l2bounded ((a::complex) \<cdot> M) = smult_mat a (mat_of_l2bounded M)" for M :: "('a::basis_enum,'b::basis_enum) Bounded"
  by (cheat 16)

lemma mat_of_l2bounded_inj: "inj mat_of_l2bounded"
  by (cheat 16)

lemma bounded_eq[prepare_for_code]: "x = y \<longleftrightarrow> mat_of_l2bounded x = mat_of_l2bounded y"
  by (cheat 16)

(* instantiation Bounded :: (basis_enum,basis_enum) equal begin
definition [code]: "equal_Bounded M N \<longleftrightarrow> mat_of_l2bounded M = mat_of_l2bounded N" 
  for M N :: "('a,'b) Bounded"
instance 
  apply intro_classes
  unfolding equal_Bounded_def 
  using mat_of_l2bounded_inj injD by fastforce
end *)

lemma vec_of_ell2_inj: "inj vec_of_ell2"
  by (cheat 16)

lemma ell2_eq[prepare_for_code]: "x = y \<longleftrightarrow> vec_of_ell2 x = vec_of_ell2 y"
  by (cheat 16)

instantiation ell2 :: (enum) equal begin
definition [code]: "equal_ell2 M N \<longleftrightarrow> vec_of_ell2 M = vec_of_ell2 N" 
  for M N :: "'a::enum ell2"
instance 
  apply intro_classes
  unfolding equal_ell2_def 
  using vec_of_ell2_inj injD
  by fastforce
end



definition "matrix_X = mat_of_rows_list 2 [ [0::complex,1], [1,0] ]"
lemma l2bounded_of_mat_X[prepare_for_code]: "mat_of_l2bounded pauliX = matrix_X"
  by (cheat 16)
definition "matrix_Z = mat_of_rows_list 2 [ [1::complex,0], [0,-1] ]"
lemma l2bounded_of_mat_Z[prepare_for_code]: "mat_of_l2bounded pauliZ = matrix_Z"
  by (cheat 16)
definition "matrix_Y = mat_of_rows_list 2 [ [0::complex,-\<i>], [\<i>,0] ]"
lemma l2bounded_of_mat_Y[prepare_for_code]: "mat_of_l2bounded pauliY = matrix_Y"
  by (cheat 16)
definition "matrix_hadamard = mat_of_rows_list 2 [ [1/sqrt 2::complex, 1/sqrt 2], [1/sqrt 2, -1/sqrt 2] ]"
lemma l2bounded_of_mat_hadamard[prepare_for_code]: "mat_of_l2bounded hadamard = matrix_hadamard"
  by (cheat 16)
definition "matrix_CNOT = mat_of_rows_list 4 [ [1::complex,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0] ]"
lemma l2bounded_of_mat_CNOT[prepare_for_code]: "mat_of_l2bounded CNOT = matrix_CNOT"
  by (cheat 17)

definition "matrix_tensor (A::'a::times mat) (B::'a mat) =
  mat (dim_row A*dim_row B) (dim_col A*dim_col B) 
  (\<lambda>(r,c). A $$ (r div dim_row B, c div dim_col B) *
           B $$ (r mod dim_row B, c mod dim_col B))"

lemma l2bounded_of_mat_tensorOp[prepare_for_code]:
  "mat_of_l2bounded (tensorOp A B) = matrix_tensor (mat_of_l2bounded A) (mat_of_l2bounded B)"
for A :: "('a::enum,'b::enum) l2bounded"
and B :: "('c::enum,'d::enum) l2bounded"
  by (cheat 17)

definition "adjoint_mat M = transpose_mat (map_mat cnj M)"
lemma l2bounded_of_mat_adjoint[prepare_for_code]:
  "mat_of_l2bounded (adjoint A) = adjoint_mat (mat_of_l2bounded A)"
for A :: "('a::basis_enum,'b::basis_enum) Bounded"
  by (cheat 17)

(* TODO generalize to Bounded *)
lemma l2bounded_of_mat_assoc_op[prepare_for_code]: 
  "mat_of_l2bounded (assoc_op :: ('a::enum*'b::enum*'c::enum,_) l2bounded) = one_mat (Enum.card_UNIV TYPE('a)*Enum.card_UNIV TYPE('b)*Enum.card_UNIV TYPE('c))"
  by (cheat 17)

definition "comm_op_mat TYPE('a::enum) TYPE('b::enum) =
  (let da = Enum.card_UNIV TYPE('a); db = Enum.card_UNIV TYPE('b) in
  mat (da*db) (da*db)
  (\<lambda>(r,c). (if (r div da = c mod db \<and>
                r mod da = c div db) then 1 else 0)))"

(* TODO generalize to Bounded *)
lemma l2bounded_of_mat_comm_op[prepare_for_code]:
  "mat_of_l2bounded (comm_op :: ('a::enum*'b::enum,_) l2bounded) = comm_op_mat TYPE('a) TYPE('b)"
  by (cheat 17)

lemma vec_of_ell2_zero[prepare_for_code]:
  "vec_of_ell2 (0::'a::enum ell2) = zero_vec (CARD('a))"
  by (cheat 17)


lemma vec_of_ell2_ket[prepare_for_code]:
  "vec_of_ell2 (ket i) = unit_vec (CARD('a)) (enum_idx i)" for i::"'a::enum"
  by (cheat 17)

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

lemma mat_of_l2bounded_zero[prepare_for_code]:
  "mat_of_l2bounded (0::('a::basis_enum,'b::basis_enum) Bounded)
       = zero_mat (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a))"
  by (cheat 17)

definition "computational_basis_vec n = map (unit_vec n) [0..<n]"
(* TODO: the filter part creates zero_vec's for each test *)
definition "orthogonal_complement_vec n vs = 
  filter ((\<noteq>) (zero_vec n)) (drop (length vs) (gram_schmidt n (vs @ computational_basis_vec n)))"

definition "vec_tensor (A::'a::times vec) (B::'a vec) =
  vec (dim_vec A*dim_vec B) 
  (\<lambda>r. vec_index A (r div dim_vec B) *
       vec_index B (r mod dim_vec B))"


lemma tensorVec_code[prepare_for_code]: "vec_of_ell2 (\<psi> \<otimes> \<phi>) = vec_tensor (vec_of_ell2 \<psi>) (vec_of_ell2 \<phi>)"
  for \<psi>::"'a::enum ell2" and \<phi>::"'b::enum ell2"
  by (cheat 17)

(* definition [code del]: "SPAN x = span (ell2_of_vec' ` set x)"
code_datatype SPAN *)

axiomatization same_vec_subspace :: "nat * complex vec set \<Rightarrow> nat * complex vec set \<Rightarrow> bool"
quotient_type vec_subspace = "nat * complex vec set" / partial: same_vec_subspace
  by (cheat 17)

axiomatization mk_vec_subspace :: "nat * complex vec set \<Rightarrow> vec_subspace"
(* axiomatization unmake_vec_subspace :: "vec_subspace \<Rightarrow> nat * complex vec list" *)

(* lemma [code abstype]:
  "mk_vec_subspace (unmake_vec_subspace S) = S"
  by (cheat 17) *)

code_datatype mk_vec_subspace

axiomatization vec_subspace_of :: "'a::basis_enum linear_space \<Rightarrow> vec_subspace"

(* definition "mk_projector (S::vec_subspace) = mat_of_l2bounded (Proj S)"  *)
axiomatization mk_projector :: "vec_subspace \<Rightarrow> complex mat"
fun mk_projector_orthog :: "nat \<Rightarrow> complex vec list \<Rightarrow> complex mat" where
  "mk_projector_orthog d [] = zero_mat d d"
| "mk_projector_orthog d [v] = (let norm2 = cscalar_prod v v in
                                if norm2=0 then zero_mat d d else
                                smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [v]))"
| "mk_projector_orthog d (v#vs) = (let norm2 = cscalar_prod v v in
                                   if norm2=0 then mk_projector_orthog d vs else
                                   smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [v]) 
                                        + mk_projector_orthog d vs)"


lemma mk_projector_code[code]: 
  "mk_projector (mk_vec_subspace (d,Set_Monad S)) = 
    (mk_projector_orthog d (gram_schmidt d S))"
  by (cheat 17)

(*lemma mk_projector_SPAN[code]: "mk_projector (SPAN S :: 'a::enum subspace) = (case S of 
    [v] \<Rightarrow> (let d = dim_vec v in let norm2 = cscalar_prod v v in
                if norm2=0 then zero_mat d d else
                            smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [v]))
  | _ \<Rightarrow> Code.abort (STR ''Computation of 'Proj S' only implemented for singleton S'') (\<lambda>_. mat_of_l2bounded (Proj (SPAN S :: 'a subspace))))"*)

lemma [prepare_for_code]: "mat_of_l2bounded (Proj S) = mk_projector (vec_subspace_of S)" 
  for S :: "'a::basis_enum linear_space"
  (* unfolding mk_projector_def by simp *)
  sorry

definition "vec_subspace_zero n = mk_vec_subspace (n, {})"
definition "vec_subspace_top d = mk_vec_subspace (d, Set_Monad (computational_basis_vec d))"


lemma top_as_span[prepare_for_code]: "vec_subspace_of (top::'a linear_space) = 
  vec_subspace_top (canonical_basis_length TYPE('a::basis_enum))"
  by (cheat 17)
lemma bot_as_span[prepare_for_code]: "vec_subspace_of (bot::'a::basis_enum linear_space) = 
  vec_subspace_zero (canonical_basis_length TYPE('a))"
  by (cheat 17)

(* Convention: operations on vec_subspace with a dimension mismatch return this *)
definition "null_subspace = mk_vec_subspace (0,{})"

instance vec_subspace :: plus sorry
instance vec_subspace :: inf sorry

lemma plus_spans[code]: "mk_vec_subspace (d,A) + mk_vec_subspace (d',B) = 
  (if d=d' then mk_vec_subspace (d, A \<union> B) else Code.abort STR ''dimension mismatch'' (\<lambda>_. mk_vec_subspace (d,A) + mk_vec_subspace (d',B)))"
  by (cheat 17)

lemma linear_space_plus[prepare_for_code]: "vec_subspace_of (A+B) = vec_subspace_of A + vec_subspace_of B"
  sorry

axiomatization ortho_vec :: "vec_subspace \<Rightarrow> vec_subspace"
lemma ortho_vec_SPAN[code]: "ortho_vec (mk_vec_subspace (d,Set_Monad A))
        = mk_vec_subspace (d, Set_Monad (orthogonal_complement_vec d A))"
  by (cheat 17)
lemma ortho_vec[prepare_for_code]: "vec_subspace_of (ortho S) = ortho_vec (vec_subspace_of S)"
  by (cheat 17)


(* definition [code del,code_abbrev]: "span_code (S::'a::enum ell2 set) = (span S)" *)

(* lemma span_Set_Monad[code]: "span_code (Set_Monad l) = (SPAN (map vec_of_ell2 l))"
  (* for l :: "'a::enum ell2 list" *)
  by (cheat 17) *)
axiomatization tensorSpace_vec :: "vec_subspace \<Rightarrow> vec_subspace \<Rightarrow> vec_subspace"
lemma tensorSpace_SPAN[code]: "tensorSpace_vec (mk_vec_subspace (dA,Set_Monad A)) (mk_vec_subspace (dB,Set_Monad B))
   = mk_vec_subspace (dA*dB, Set_Monad [vec_tensor a b. a<-A, b<-B])"
  by (cheat 17)
lemma tensorSpace_vec[prepare_for_code]: "vec_subspace_of (tensorSpace A B)
  = tensorSpace_vec (vec_subspace_of A) (vec_subspace_of B)"
  by (cheat 17)

lemma vec_of_ell2_timesScalarVec[prepare_for_code]: "vec_of_ell2 (scaleC a \<psi>) = smult_vec a (vec_of_ell2 \<psi>)"
  for \<psi> :: "'a::enum ell2"
  by (cheat 17)

lemma vec_of_ell2_scaleR[prepare_for_code]: "vec_of_ell2 (scaleR a \<psi>) = smult_vec (complex_of_real a) (vec_of_ell2 \<psi>)"
  for \<psi> :: "'a::enum ell2"
  by (cheat 17)

lemma ell2_of_vec_plus[prepare_for_code]:
  "vec_of_ell2 (x + y) =  (vec_of_ell2 x) + (vec_of_ell2 y)" for x y :: "'a::enum ell2"
  by (cheat 17)

lemma ell2_of_vec_minus[prepare_for_code]:
  "vec_of_ell2 (x - y) =  (vec_of_ell2 x) - (vec_of_ell2 y)" for x y :: "'a::enum ell2"
  by (cheat 17)

lemma ell2_of_vec_uminus[prepare_for_code]:
  "vec_of_ell2 (- y) =  - (vec_of_ell2 y)" for y :: "'a::enum ell2"
  by (cheat 17)

lemma vec_of_ell2_EPR[prepare_for_code]: "vec_of_ell2 EPR = vec_of_list [1/sqrt 2,0,0,1/sqrt 2]"
  by (cheat 17)

lemma [code_post]: 
  shows "Complex a 0 = complex_of_real a"
  and "complex_of_real 0 = 0"
  and "complex_of_real 1 = 1"
  and "complex_of_real (a/b) = complex_of_real a / complex_of_real b"
  and "complex_of_real (numeral n) = numeral n"
  and "complex_of_real (-r) = - complex_of_real r"
  using complex_eq_cancel_iff2 by auto

(* instantiation linear_space :: (basis_enum) equal begin
definition [code del]: "equal_linear_space (A::'a linear_space) B = (A=B)"
instance apply intro_classes unfolding equal_linear_space_def by simp
end *)

lemma eq_linear_space[prepare_for_code]: "A = B \<longleftrightarrow> vec_subspace_of A = vec_subspace_of B" 
  sorry

instantiation vec_subspace :: equal begin
definition [code del]: "equal_vec_subspace (x::vec_subspace) y = (x=y)"
instance
  apply intro_classes unfolding equal_vec_subspace_def by simp
end

instantiation vec_subspace :: ord begin
(* axiomatization [code del]: "less_eq_vec_subspace (x::vec_subspace) y = (x=y)" *)
instance sorry
  (* apply intro_classes unfolding equal_vec_subspace_def by simp *)
end

(* definition "is_subspace_of = (\<lambda> (n,vs) (m,ws).
  ((n=m) \<and> list_all ((=) (zero_vec n)) (drop (length ws) (gram_schmidt n (ws @ vs)))))" *)

lemma vec_subspace_leq[code]: "mk_vec_subspace (n,Set_Monad vs) \<le> mk_vec_subspace (m,Set_Monad ws) \<longleftrightarrow>
  ((n=m) \<and> list_all ((=) (zero_vec n)) (drop (length ws) (gram_schmidt n (ws @ vs))))"
  sorry

lemma leq_subspace[prepare_for_code]: "A \<le> B \<longleftrightarrow> vec_subspace_of A \<le> vec_subspace_of B"
  sorry

(* lemma SPAN_leq[code]: "mk_vec_subspace A \<le> (mk_vec_subspace B) \<longleftrightarrow> is_subspace_of A B" 
  by (cheat 17) *)

lemma subspace_leq[prepare_for_code]: "vec_subspace_of A \<le> vec_subspace_of B \<longleftrightarrow> A \<le> B"
  sorry

axiomatization apply_vec_subspace :: "complex mat \<Rightarrow> vec_subspace \<Rightarrow> vec_subspace"
lemma [code]: "apply_vec_subspace A (mk_vec_subspace (n,S)) 
  = (if dim_col A=n then mk_vec_subspace (dim_row A, mult_mat_vec A ` S)
    else Code.abort STR ''dimension mismatch'' (\<lambda>_. apply_vec_subspace A (mk_vec_subspace (n,S))))"
  sorry

lemma applyOpSpace_code[prepare_for_code]:
  "vec_subspace_of (applyOpSpace A S) = apply_vec_subspace (mat_of_l2bounded A) (vec_subspace_of S)"
  sorry

(* lemma applyOpSpace_SPAN[code]: "applyOpSpace A (SPAN S) = SPAN (map (mult_mat_vec (mat_of_l2bounded A)) S)"
  for A::"('a::basis_enum,'b::basis_enum) Bounded"
  by (cheat 17) *)

axiomatization kernel_vec :: "complex mat \<Rightarrow> vec_subspace"
lemma kernel_SPAN[code]: "kernel_vec A = 
  mk_vec_subspace (dim_col A, Set_Monad (find_base_vectors (gauss_jordan_single A)))"
  by (cheat 17)
lemma kernel_code[prepare_for_code]: "vec_subspace_of (kernel A) = kernel_vec (mat_of_l2bounded A)"
  by (cheat 17)

declare eigenspace_def[prepare_for_code]
(* 
lemma [prepare_for_code]: "kernel (A-a\<cdot>idOp) = eigenspace a A" 
  unfolding eigenspace_def by simp
 *)

definition [code]: "classical_operator_vec dA dB lA lB f =
mat dB dA (\<lambda>(r,c). if f (lA!c) = Some (lB!r) then 1 else 0)"

lemma mat_of_l2bounded_classical_operator[prepare_for_code]: 
  "mat_of_l2bounded (classical_operator f) = classical_operator_vec (CARD('b)) (CARD('a))
  Enum.enum Enum.enum f" 
  for f::"'a::enum \<Rightarrow> 'b::enum option"
  by (cheat 17)

lemma [code]: "HOL.equal (A::vec_subspace) B = (A\<le>B \<and> B\<le>A)"
  (* unfolding equal_linear_space_def by auto *)
  sorry

(* definition [code del,code_abbrev]: "ell2_to_Bounded_code (\<psi>::'a ell2) = (ell2_to_Bounded \<psi>)" *)

definition "mat_of_col \<psi> = mat_of_cols (dim_vec \<psi>) [\<psi>]"

lemma mat_of_l2bounded_ell2_to_l2bounded[prepare_for_code]:  
  "mat_of_l2bounded (ell2_to_Bounded \<psi>) = mat_of_col (vec_of_ell2 \<psi>)" 
  (* for \<psi>::"'a::basis_enum" *)
  by (cheat 17)

lemma mat_of_l2bounded_remove_qvar_unit_op[prepare_for_code]:
  "mat_of_l2bounded (remove_qvar_unit_op::(_,'a::enum) l2bounded) = mat_of_l2bounded (idOp::(_,'a) l2bounded)" 
  by (cheat 17)

(* TODO: prove this in Complex_L2 *)
lemma inf_ortho: "(A::'a::basis_enum linear_space) \<sqinter> B = ortho (ortho A + ortho B)"
  unfolding linear_space_sup_plus[symmetric]
  by (cheat demorgan) 

lemma inf_ortho_vec[code]:
  "A \<sqinter> B = ortho_vec (ortho_vec A + ortho_vec B)"
  sorry

lemma inf_code[prepare_for_code]: "vec_subspace_of (A \<sqinter> B) = vec_subspace_of A \<sqinter> vec_subspace_of B"
  sorry


axiomatization Inf_vec_subspace :: "nat \<Rightarrow> vec_subspace set \<Rightarrow> vec_subspace"

lemma [code]: "Inf_vec_subspace d (Set_Monad l :: vec_subspace set) = fold inf l (vec_subspace_zero d)"
  unfolding Set_Monad_def
  sorry

lemma quantum_equality_full_def_let:
  "quantum_equality_full U Q V R = (let U=U; V=V in
                 (eigenspace 1 (comm_op \<cdot> (V*\<cdot>U)\<otimes>(U*\<cdot>V))) \<guillemotright> variable_concat Q R)"
  unfolding quantum_equality_full_def by auto

(* TODO intro constant for the vec side? *)
lemma space_div_unlifted_code [prepare_for_code]: "space_div_unlifted S \<psi> = 
  (let A = addState \<psi> in kernel (Proj S \<cdot> A - A))" 
  by (cheat space_div_unlifted_code)
declare addState_def[prepare_for_code]

definition "cinner_vec \<psi> \<phi> = scalar_prod (map_vec cnj \<psi>) \<phi>"

lemma cinner_ell2_code [prepare_for_code]:
  "cinner \<psi> \<phi> = cinner_vec (vec_of_ell2 \<psi>) (vec_of_ell2 \<phi>)"
  by (cheat cinner_ell2_code)

definition "norm_vec \<psi>' = sqrt (\<Sum> i \<in> {0 ..< dim_vec \<psi>'}. let z = vec_index \<psi>' i in (Re z)\<^sup>2 + (Im z)\<^sup>2)"

lemma norm_ell2_code [prepare_for_code]: "norm \<psi> = norm_vec (vec_of_ell2 \<psi>)"
  by (cheat norm_ell2_code)

(* (* Hack: Without this definition, code generation produces invalid code. *)
lemma [code]: "(uniformity :: ('a ell2 * _) filter) = Filter.abstract_filter (%_. 
    Code.abort STR ''no uniformity'' (%_. 
    let x = ((=)::'a\<Rightarrow>_\<Rightarrow>_) in uniformity))"
  by auto *)


(* declare [[code drop: UNIV]] *)
declare enum_class.UNIV_enum[code]

declare ord_linear_space_inst.less_eq_linear_space[code del]
declare ord_linear_space_inst.less_linear_space[code del]

derive (eq) ceq bit
derive (linorder) compare_order bit
derive (compare) ccompare bit
derive (dlist) set_impl bit
derive (eq) ceq real
derive (linorder) compare real
derive (compare) ccompare real
derive (eq) ceq complex
derive (no) ccompare complex
(* derive (eq) ceq linear_space
derive (no) ccompare linear_space
derive (monad) set_impl linear_space
derive (eq) ceq ell2
derive (no) ccompare ell2
derive (monad) set_impl ell2
 *)
derive (eq) ceq vec_subspace
derive (no) ccompare vec_subspace
derive (monad) set_impl vec_subspace
derive (monad) set_impl ell2


lemmas [prepare_for_code] = quantum_equality_full_def_let add_join_variables_hint space_div_space_div_unlifted
  space_div_add_extend_lift_as_var_concat_hint INF_lift Cla_inf_lift Cla_plus_lift
  top_leq_lift top_geq_lift bot_leq_lift bot_geq_lift top_eq_lift bot_eq_lift top_eq_lift2 bot_eq_lift2

end
