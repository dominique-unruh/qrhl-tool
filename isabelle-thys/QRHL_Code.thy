theory QRHL_Code
  imports 
    QRHL_Core
    "Jordan_Normal_Form.Matrix_Impl"
    "HOL-Library.Code_Target_Numeral"
    (* Tensor_Product.Tensor_Product_Code *)
    "HOL-Eisbach.Eisbach"
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


(* TODO remove? *)
lemma vec_of_ell2_inj: "inj vec_of_ell2"
  unfolding vec_of_ell2_def
  by (metis injI vec_of_ell2_def vec_of_ell2_inverse)

definition "matrix_X = mat_of_rows_list 2 [ [0::complex,1], [1,0] ]"
lemma bounded_of_mat_X[code]: "mat_of_cblinfun pauliX = matrix_X"
  by (cheat 16)
definition "matrix_Z = mat_of_rows_list 2 [ [1::complex,0], [0,-1] ]"
lemma bounded_of_mat_Z[code]: "mat_of_cblinfun pauliZ = matrix_Z"
  by (cheat 16)
definition "matrix_Y = mat_of_rows_list 2 [ [0::complex,-\<i>], [\<i>,0] ]"
lemma bounded_of_mat_Y[code]: "mat_of_cblinfun pauliY = matrix_Y"
  by (cheat 16)
(* definition "matrix_hadamard = mat_of_rows_list 2 [ [1/sqrt 2::complex, 1/sqrt 2], [1/sqrt 2, -1/sqrt 2] ]" *)
lemma bounded_of_mat_hadamard[code]: "mat_of_cblinfun hadamard = matrix_hadamard"
  sorry
(*   unfolding hadamard_def
  apply (rule cblinfun_of_mat_inverse)
  by (auto simp add: matrix_hadamard_def) *)
(* definition "matrix_CNOT = mat_of_rows_list 4 [ [1::complex,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0] ]" *)
lemma bounded_of_mat_CNOT[code]: "mat_of_cblinfun CNOT = matrix_CNOT"
  sorry
  (* unfolding CNOT_def
  apply (rule cblinfun_of_mat_inverse)
  by (auto simp add: matrix_CNOT_def) *)


(* TODO move *)
instantiation bit :: linorder begin
definition "less_bit (a::bit) (b::bit) = (a=0 \<and> b=1)"
definition "less_eq_bit (a::bit) b = (a=b \<or> a<b)"
instance apply intro_classes unfolding less_bit_def less_eq_bit_def by auto
end

(* TODO move *)
(* instantiation bit :: card_UNIV begin
definition "finite_UNIV_bit = Phantom(bit) True"
definition "card_UNIV_bit = Phantom(bit) (2::nat)"
instance apply intro_classes unfolding finite_UNIV_bit_def card_UNIV_bit_def 
  apply auto unfolding UNIV_bit by simp 
end *)





(*lemma mk_projector_SPAN[code]: "mk_projector (SPAN S :: 'a::enum subspace) = (case S of 
    [v] \<Rightarrow> (let d = dim_vec v in let norm2 = cscalar_prod v v in
                if norm2=0 then zero_mat d d else
                            smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [v]))
  | _ \<Rightarrow> Code.abort (STR ''Computation of 'Proj S' only implemented for singleton S'') (\<lambda>_. mat_of_cblinfun (Proj (SPAN S :: 'a subspace))))"*)


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



lemma quantum_equality_full_def_let:
  "quantum_equality_full U Q V R = (let U=U; V=V in
                 (eigenspace 1 (comm_op \<cdot> (V*\<cdot>U)\<otimes>(U*\<cdot>V))) \<guillemotright> \<lbrakk>Q,R\<rbrakk>)"
  unfolding quantum_equality_full_def by auto

lemma space_div_unlifted_code [code]: "space_div_unlifted S \<psi> = (let A = addState \<psi> in kernel (Proj S \<cdot> A - A))"
  by (cheat space_div_unlifted_code)

(* TODO: remove once "code del" is added at the definitions themselves \<longrightarrow> is already done! *)
(* declare ord_clinear_space_inst.less_eq_clinear_space[code del]
declare ord_clinear_space_inst.less_clinear_space[code del] *)

(* derive (eq) ceq bit *)
derive (linorder) compare_order bit
(* derive (compare) ccompare bit *)
(* derive (dlist) set_impl bit *)
derive (eq) ceq real
derive (linorder) compare real
derive (compare) ccompare real
derive (eq) ceq complex
derive (no) ccompare complex

(* (* TODO: remove *)
lemmas prepare_for_code = quantum_equality_full_def_let (* add_join_variables_hint *) space_div_space_div_unlifted
  (* space_div_add_extend_lift_as_var_concat_hint *) INF_lift Cla_inf_lift Cla_plus_lift Cla_sup_lift
  top_leq_lift top_geq_lift bot_leq_lift bot_geq_lift top_eq_lift bot_eq_lift top_eq_lift2 bot_eq_lift2 *)


subsection \<open>\<open>prepare_for_code\<close> method\<close>

lemmas prepare_for_code_add =
  (* qregister_of_cregister_Fst[symmetric] qregister_of_cregister_Snd[symmetric] *)
  (* qregister_of_cregister_pair[symmetric] qregister_of_cregister_chain[symmetric] *)
  apply_qregister_of_cregister permute_and_tensor1_cblinfun_code_prep
  same_outside_cregister_def
  
  case_prod_beta if_distrib[of fst] if_distrib[of snd] prod_eq_iff

  div_leq_simp mod_mod_cancel

  getter_pair getter_chain setter_chain setter_pair setter_Fst setter_Snd

  enum_index_prod_def fst_enum_nth snd_enum_nth enum_index_nth if_distrib[of enum_index]
  enum_nth_injective

  quantum_equality_full_def_let space_div_space_div_unlifted INF_lift Cla_inf_lift Cla_plus_lift Cla_sup_lift
  top_leq_lift top_geq_lift bot_leq_lift bot_geq_lift top_eq_lift bot_eq_lift top_eq_lift2 bot_eq_lift2

lemmas prepare_for_code_flip =
  qregister_of_cregister_Fst qregister_of_cregister_Snd
  qregister_of_cregister_pair qregister_of_cregister_chain


method prepare_for_code = simp add: join_registers cong del: if_weak_cong
  add: prepare_for_code_add flip: prepare_for_code_flip


unbundle no_jnf_notation

end
