theory QRHL_Code
  imports QRHL_Core "Jordan_Normal_Form.Matrix_Impl" "HOL-Library.Code_Target_Numeral"
    Tensor_Product.Tensor_Product_Code
begin

unbundle jnf_notation

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

no_syntax "\<^const>Group.monoid.mult"    :: "['a, 'a, 'a] \<Rightarrow> 'a" (infixl "\<otimes>\<index>" 70)
no_syntax "\<^const>Lattice.meet" :: "[_, 'a, 'a] => 'a" (infixl "\<sqinter>\<index>" 70)

(* Wrapper class so that we can define a code datatype constructors for that type (does not work with type synonyms) *)
typedef ('a::enum,'b::enum) code_l2bounded = "UNIV::('a,'b) l2bounded set" by simp
setup_lifting type_definition_code_l2bounded

lift_definition l2bounded_of_mat' :: "complex mat \<Rightarrow> ('a::enum,'b::enum) code_l2bounded"
  is cblinfun_of_mat.
lift_definition mat_of_l2bounded' :: "('a::enum,'b::enum) code_l2bounded \<Rightarrow> complex mat"
  is mat_of_cblinfun.

(* abbreviation "onb_enum_of_vec == onb_enum_of_vec" *)
(* abbreviation "vec_of_onb_enum == vec_of_onb_enum" *)

definition ell2_of_vec :: "complex vec \<Rightarrow> 'a::enum ell2" where "ell2_of_vec = onb_enum_of_vec"
definition vec_of_ell2 :: "'a::enum ell2 \<Rightarrow> complex vec" where "vec_of_ell2 = vec_of_onb_enum"

lemma mat_of_cblinfun_inverse' [code abstype]:
  "l2bounded_of_mat' (mat_of_l2bounded' B) = B" 
  apply transfer
  using mat_of_cblinfun_inverse by blast

lemma [code]: "mat_of_l2bounded' (Abs_code_l2bounded X) = mat_of_cblinfun X"
  apply transfer by simp
lemma [code]: "mat_of_cblinfun (Rep_code_l2bounded X) = mat_of_l2bounded' X"
  apply transfer by simp

lemma vec_of_ell2_inverse [code abstype]:
  "ell2_of_vec (vec_of_ell2 B) = B" 
  unfolding ell2_of_vec_def vec_of_ell2_def
  by (simp add: onb_enum_of_vec_inverse)

fun index_of where
  "index_of x [] = (0::nat)"
| "index_of x (y#ys) = (if x=y then 0 else (index_of x ys + 1))"

definition "enum_idx (x::'a::enum) = index_of x (enum_class.enum :: 'a list)"

lift_definition applyOp_code :: "('a::enum, 'b::enum) code_l2bounded \<Rightarrow> 'a ell2 \<Rightarrow> 'b ell2" 
  is "applyOp :: ('a ell2,'b ell2) bounded \<Rightarrow> _ \<Rightarrow> _".
(* definition [code del]: "applyOp_code M x = applyOp (Rep_code_l2bounded M) x" *)

lemma [symmetric,code_abbrev]: "applyOp M = applyOp_code (Abs_code_l2bounded M)"
  apply transfer by simp
lemma ell2_of_vec_applyOp[code]:
  "vec_of_ell2 (applyOp_code M x) = (mult_mat_vec (mat_of_l2bounded' M) (vec_of_ell2 x))" 
  by (cheat 15)


lemma vec_of_ell2_inj: "inj vec_of_ell2"
  unfolding vec_of_ell2_def
  by (metis injI vec_of_ell2_def vec_of_ell2_inverse)

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
lemma bounded_of_mat_X[code]: "mat_of_cblinfun pauliX = matrix_X"
  by (cheat 16)
definition "matrix_Z = mat_of_rows_list 2 [ [1::complex,0], [0,-1] ]"
lemma bounded_of_mat_Z[code]: "mat_of_cblinfun pauliZ = matrix_Z"
  by (cheat 16)
definition "matrix_Y = mat_of_rows_list 2 [ [0::complex,-\<i>], [\<i>,0] ]"
lemma bounded_of_mat_Y[code]: "mat_of_cblinfun pauliY = matrix_Y"
  by (cheat 16)
definition "matrix_hadamard = mat_of_rows_list 2 [ [1/sqrt 2::complex, 1/sqrt 2], [1/sqrt 2, -1/sqrt 2] ]"
lemma bounded_of_mat_hadamard[code]: "mat_of_cblinfun hadamard = matrix_hadamard"
  by (cheat 16)
definition "matrix_CNOT = mat_of_rows_list 4 [ [1::complex,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0] ]"
lemma bounded_of_mat_CNOT[code]: "mat_of_cblinfun CNOT = matrix_CNOT"
  by (cheat 17)

definition "matrix_tensor (A::'a::times mat) (B::'a mat) =
  mat (dim_row A*dim_row B) (dim_col A*dim_col B) 
  (\<lambda>(r,c). A $$ (r div dim_row B, c div dim_col B) *
           B $$ (r mod dim_row B, c mod dim_col B))"

lemma bounded_of_mat_tensorOp[code]:
  "mat_of_cblinfun (tensorOp A B) = matrix_tensor (mat_of_cblinfun A) (mat_of_cblinfun B)"
  for A :: "('a::enum,'b::enum) l2bounded"
    and B :: "('c::enum,'d::enum) l2bounded"
  by (cheat 17)


lemma bounded_of_mat_assoc_op[code]: 
  "mat_of_cblinfun (assoc_op :: ('a::enum*'b::enum*'c::enum,_) l2bounded) = one_mat (Enum.card_UNIV TYPE('a)*Enum.card_UNIV TYPE('b)*Enum.card_UNIV TYPE('c))"
  by (cheat 17)

definition "comm_op_mat TYPE('a::enum) TYPE('b::enum) =
  (let da = Enum.card_UNIV TYPE('a); db = Enum.card_UNIV TYPE('b) in
  mat (da*db) (da*db)
  (\<lambda>(r,c). (if (r div da = c mod db \<and>
                r mod da = c div db) then 1 else 0)))"

lemma bounded_of_mat_comm_op[code]:
  "mat_of_cblinfun (comm_op :: ('a::enum*'b::enum,_) l2bounded) = comm_op_mat TYPE('a) TYPE('b)"
  by (cheat 17)

lemma vec_of_ell2_zero[code]:
  "vec_of_ell2 (0::'a::enum ell2) = zero_vec (CARD('a))"
  by (cheat 17)


lemma vec_of_ell2_ket[code]:
  "vec_of_ell2 (ket i) = unit_vec (CARD('a)) (enum_idx i)" for i::"'a::enum"
  by (cheat 17)

(* TODO move *)
instantiation bit :: linorder begin
definition "less_bit (a::bit) (b::bit) = (a=0 \<and> b=1)"
definition "less_eq_bit (a::bit) b = (a=b \<or> a<b)"
instance apply intro_classes unfolding less_bit_def less_eq_bit_def by auto
end

(* TODO move *)
instantiation bit :: card_UNIV begin
definition "finite_UNIV_bit = Phantom(bit) True"
definition "card_UNIV_bit = Phantom(bit) (2::nat)"
instance apply intro_classes unfolding finite_UNIV_bit_def card_UNIV_bit_def 
  apply auto unfolding UNIV_bit by simp 
end

definition "computational_basis_vec n = map (unit_vec n) [0..<n]"
definition "orthogonal_complement_vec n vs = 
  filter ((\<noteq>) (zero_vec n)) (drop (length vs) (gram_schmidt n (vs @ computational_basis_vec n)))"

definition "vec_tensor (A::'a::times vec) (B::'a vec) =
  vec (dim_vec A*dim_vec B) 
  (\<lambda>r. vec_index A (r div dim_vec B) *
       vec_index B (r mod dim_vec B))"

lemma tensorVec_code[code]: "vec_of_ell2 (\<psi> \<otimes> \<phi>) = vec_tensor (vec_of_ell2 \<psi>) (vec_of_ell2 \<phi>)"
  for \<psi>::"'a::enum ell2" and \<phi>::"'b::enum ell2"
  by (cheat 17)

definition [code del]: "SPAN x = Span (onb_enum_of_vec ` set x)"
code_datatype SPAN

definition "mk_projector (S::'a::onb_enum clinear_space) = mat_of_cblinfun (Proj S)" 
fun mk_projector_orthog :: "nat \<Rightarrow> complex vec list \<Rightarrow> complex mat" where
  "mk_projector_orthog d [] = zero_mat d d"
| "mk_projector_orthog d [v] = (let norm2 = cscalar_prod v v in
                                if norm2=0 then zero_mat d d else
                                smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [v]))"
| "mk_projector_orthog d (v#vs) = (let norm2 = cscalar_prod v v in
                                   if norm2=0 then mk_projector_orthog d vs else
                                   smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [v]) 
                                        + mk_projector_orthog d vs)"

lemma mk_projector_SPAN[code]: 
  "mk_projector (SPAN S :: 'a::onb_enum clinear_space) = 
    (let d = canonical_basis_length TYPE('a) in mk_projector_orthog d (gram_schmidt d S))"
  by (cheat 17)

(*lemma mk_projector_SPAN[code]: "mk_projector (SPAN S :: 'a::enum subspace) = (case S of 
    [v] \<Rightarrow> (let d = dim_vec v in let norm2 = cscalar_prod v v in
                if norm2=0 then zero_mat d d else
                            smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [v]))
  | _ \<Rightarrow> Code.abort (STR ''Computation of 'Proj S' only implemented for singleton S'') (\<lambda>_. mat_of_cblinfun (Proj (SPAN S :: 'a subspace))))"*)

lemma [code]: "mat_of_cblinfun (Proj S) = mk_projector S" for S :: "'a::onb_enum clinear_space"
  unfolding mk_projector_def by simp


lemma top_as_span[code]: "(top::'a clinear_space) = SPAN (computational_basis_vec (canonical_basis_length TYPE('a::onb_enum)))"
  by (cheat 17)
lemma bot_as_span[code]: "(bot::'a::onb_enum clinear_space) = SPAN []"
  by (cheat 17)
lemma sup_spans[code]: "SPAN A \<squnion> SPAN B = SPAN (A @ B)" 
  by (cheat 17)

lemma ortho_SPAN[code]: "- (SPAN S :: 'a::onb_enum clinear_space)
        = SPAN (orthogonal_complement_vec (canonical_basis_length TYPE('a)) S)"
  by (cheat 17)

definition [code del,code_abbrev]: "span_code (S::'a::enum ell2 set) = (Span S)"

lemma span_Set_Monad[code]: "span_code (Set_Monad l) = (SPAN (map vec_of_ell2 l))"
  (* for l :: "'a::enum ell2 list" *)
  by (cheat 17)
lemma tensorSpace_SPAN[code]: "tensorSpace (SPAN A) (SPAN B) = SPAN [vec_tensor a b. a<-A, b<-B]"
  by (cheat 17)

lemma vec_of_ell2_timesScalarVec[code]: "vec_of_ell2 (scaleC a \<psi>) = smult_vec a (vec_of_ell2 \<psi>)"
  for \<psi> :: "'a::enum ell2"
  by (cheat 17)

lemma vec_of_ell2_scaleR[code]: "vec_of_ell2 (scaleR a \<psi>) = smult_vec (complex_of_real a) (vec_of_ell2 \<psi>)"
  for \<psi> :: "'a::enum ell2"
  by (cheat 17)

lemma ell2_of_vec_plus[code]:
  "vec_of_ell2 (x + y) =  (vec_of_ell2 x) + (vec_of_ell2 y)" for x y :: "'a::enum ell2"
  unfolding vec_of_ell2_def
  by (simp add: vec_of_onb_enum_add) 

lemma ell2_of_vec_minus[code]:
  "vec_of_ell2 (x - y) =  (vec_of_ell2 x) - (vec_of_ell2 y)" for x y :: "'a::enum ell2"
  unfolding vec_of_ell2_def 
  by (cheat 17)

lemma ell2_of_vec_uminus[code]:
  "vec_of_ell2 (- y) =  - (vec_of_ell2 y)" for y :: "'a::enum ell2"
  unfolding vec_of_ell2_def
  by (metis (mono_tags, hide_lams) carrier_vec_dim_vec diff_0 diff_self ell2_of_vec_minus minus_cancel_vec vec_of_ell2_def zero_minus_vec)

lemma vec_of_ell2_EPR[code]: "vec_of_ell2 EPR = vec_of_list [1/sqrt 2,0,0,1/sqrt 2]"
  by (cheat 17)

lemma [code_post]: 
  shows "Complex a 0 = complex_of_real a"
  and "complex_of_real 0 = 0"
  and "complex_of_real 1 = 1"
  and "complex_of_real (a/b) = complex_of_real a / complex_of_real b"
  and "complex_of_real (numeral n) = numeral n"
  and "complex_of_real (-r) = - complex_of_real r"
  using complex_eq_cancel_iff2 by auto

instantiation clinear_space :: (onb_enum) equal begin
definition [code del]: "equal_clinear_space (A::'a clinear_space) B = (A=B)"
instance apply intro_classes unfolding equal_clinear_space_def by simp
end

definition "is_subspace_of n vs ws =  
  list_all ((=) (zero_vec n)) (drop (length ws) (gram_schmidt n (ws @ vs)))"

lemma SPAN_leq[code]: "SPAN A \<le> (SPAN B :: 'a::onb_enum clinear_space) \<longleftrightarrow> is_subspace_of (canonical_basis_length TYPE('a)) A B" 
  by (cheat 17)

lemma applyOpSpace_SPAN[code]: "applyOpSpace A (SPAN S) = SPAN (map (mult_mat_vec (mat_of_cblinfun A)) S)"
  for A::"('a::onb_enum,'b::onb_enum) bounded"
  by (cheat 17)

lemma kernel_SPAN[code]: "kernel A = SPAN (find_base_vectors (gauss_jordan_single (mat_of_cblinfun A)))" 
  for A::"('a::onb_enum,'b::onb_enum) bounded"
  by (cheat 17)

lemma [code_abbrev]: "kernel (A - a *\<^sub>C idOp) = eigenspace a A" 
  unfolding eigenspace_def by simp

lemma [code]: "HOL.equal (A::_ clinear_space) B = (A\<le>B \<and> B\<le>A)"
  unfolding equal_clinear_space_def by auto

definition [code del,code_abbrev]: "vector_to_cblinfun_code (\<psi>::'a ell2) = (vector_to_cblinfun \<psi>)"

lemma mat_of_cblinfun_ell2_to_l2bounded[code]: 
  "mat_of_cblinfun (vector_to_cblinfun_code \<psi>) = mat_of_cols (CARD('a)) [vec_of_ell2 \<psi>]" 
  for \<psi>::"'a::enum ell2"
  unfolding vector_to_cblinfun_code_def
  by (cheat 17)

(* See comment at definition of remove_qvar_unit_op before proving *)
lemma mat_of_cblinfun_remove_qvar_unit_op[code]:
  "mat_of_cblinfun (remove_qvar_unit_op::(_,'a::enum) l2bounded) = mat_of_cblinfun (idOp::(_,'a) l2bounded)" 
  by (cheat 17)

(* TODO: more direct code equation (w/o remove_qvar_unit_op) *)
lemma addState_remove_qvar_unit_op[code]: "addState \<psi> = idOp \<otimes> (vector_to_cblinfun \<psi>) \<cdot> remove_qvar_unit_op*"
  by (cheat addState_remove_qvar_unit_op)

lemma [code]: "(A::'a::onb_enum clinear_space) \<sqinter> B = - (- A \<squnion> - B)"
  by (subst ortho_involution[symmetric], subst compl_inf, simp)

lemma [code]: "Inf (Set_Monad l :: 'a::onb_enum clinear_space set) = fold inf l top"
  unfolding Set_Monad_def
  by (simp add: Inf_set_fold)

lemma quantum_equality_full_def_let:
  "quantum_equality_full U Q V R = (let U=U; V=V in
                 (eigenspace 1 (comm_op \<cdot> (V*\<cdot>U)\<otimes>(U*\<cdot>V))) \<guillemotright> variable_concat Q R)"
  unfolding quantum_equality_full_def by auto

lemma space_div_unlifted_code [code]: "space_div_unlifted S \<psi> = (let A = addState \<psi> in kernel (Proj S \<cdot> A - A))"
  by (cheat space_div_unlifted_code)

(* Although this code would work for any type 'a::onb_enum, we only define it 
   for 'a ell2 because otherwise the code generation mechanism does not accept it
   (Message "Overloaded constant as head in equation") *)
lemma cinner_ell2_code [code]: "cinner \<psi> \<phi> = scalar_prod (map_vec cnj (vec_of_ell2 \<psi>)) (vec_of_ell2 \<phi>)"
  unfolding vec_of_ell2_def
  by (cheat cinner_ell2_code)

(* Although this code would work for any type 'a::onb_enum, we only define it 
   for 'a ell2 because otherwise the code generation mechanism does not accept it
   (Message "Overloaded constant as head in equation") *)
lemma norm_ell2_code [code]: "norm \<psi> = 
  (let \<psi>' = vec_of_ell2 \<psi> in
    sqrt (\<Sum> i \<in> {0 ..< dim_vec \<psi>'}. let z = vec_index \<psi>' i in (Re z)\<^sup>2 + (Im z)\<^sup>2))"
  by (cheat norm_ell2_code)

lemma times_ell2_code[code]: "vec_of_ell2 (\<psi> * \<phi>) == vec_of_list [vec_index (vec_of_ell2 \<psi>) 0 * vec_index (vec_of_ell2 \<phi>) 0]"
  for \<psi> \<phi>
  by (cheat times_ell2_code)

lemma one_ell2_code[code]: "vec_of_ell2 (1 :: 'a::{CARD_1,enum} ell2) == vec_of_list [1]" 
  by (cheat one_ell2_code)

declare [[code drop: UNIV]]
declare enum_class.UNIV_enum[code]

(* TODO: remove once "code del" is added at the definitions themselves \<longrightarrow> is already done! *)
declare ord_clinear_space_inst.less_eq_clinear_space[code del]
declare ord_clinear_space_inst.less_clinear_space[code del]

derive (eq) ceq bit
derive (linorder) compare_order bit
derive (compare) ccompare bit
derive (dlist) set_impl bit
derive (eq) ceq real
derive (linorder) compare real
derive (compare) ccompare real
derive (eq) ceq complex
derive (no) ccompare complex
derive (eq) ceq clinear_space
derive (no) ccompare clinear_space
derive (monad) set_impl clinear_space
derive (eq) ceq ell2
derive (no) ccompare ell2
derive (monad) set_impl ell2

lemmas prepare_for_code = quantum_equality_full_def_let add_join_variables_hint space_div_space_div_unlifted
  space_div_add_extend_lift_as_var_concat_hint INF_lift Cla_inf_lift Cla_plus_lift Cla_sup_lift
  top_leq_lift top_geq_lift bot_leq_lift bot_geq_lift top_eq_lift bot_eq_lift top_eq_lift2 bot_eq_lift2

unbundle no_jnf_notation

end
