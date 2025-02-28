theory QRHL_Code
  imports 
    QRHL_Core
    "Jordan_Normal_Form.Matrix_Impl"
    "HOL-Library.Code_Target_Numeral"
    "HOL-Eisbach.Eisbach"
begin

unbundle jnf_syntax

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

(* hide_const (open) Quantum.hadamard
hide_const (open) Quantum.matrix_hadamard
hide_const (open) Quantum.CNOT
hide_const (open) Quantum.matrix_CNOT
hide_const (open) Quantum.pauliX
hide_const (open) Quantum.matrix_pauliX
(* hide_const (open) Quantum.pauliY *)
(* hide_const (open) Quantum.matrix_pauliY *)
hide_const (open) Quantum.pauliZ
hide_const (open) Quantum.matrix_pauliZ *)


no_syntax "\<^const>Group.monoid.mult"    :: "['a, 'a, 'a] \<Rightarrow> 'a" (infixl "\<otimes>\<index>" 70)
no_syntax "\<^const>Lattice.meet" :: "[_, 'a, 'a] => 'a" (infixl "\<sqinter>\<index>" 70)


(* TODO remove? *)
lemma vec_of_ell2_inj: "inj vec_of_ell2"
  unfolding vec_of_ell2_def
  by (metis injI vec_of_ell2_def vec_of_ell2_inverse)

(* (* Already in Quantum.thy *)
definition "matrix_X = mat_of_rows_list 2 [ [0::complex,1], [1,0] ]"
lemma bounded_of_mat_X[code]: "mat_of_cblinfun pauliX = matrix_X"
definition "matrix_Z = mat_of_rows_list 2 [ [1::complex,0], [0,-1] ]"
lemma bounded_of_mat_Z[code]: "mat_of_cblinfun pauliZ = matrix_Z" *)
(* (* Already in QRHL_Core.thy *)
definition "matrix_Y = mat_of_rows_list 2 [ [0::complex,-\<i>], [\<i>,0] ]"
lemma bounded_of_mat_Y[code]: "mat_of_cblinfun pauliY = matrix_Y" *)

(* (* Already in QRHL_Core.thy *)
definition "matrix_hadamard = mat_of_rows_list 2 [ [1/sqrt 2::complex, 1/sqrt 2], [1/sqrt 2, -1/sqrt 2] ]"
lemma bounded_of_mat_hadamard[code]: "mat_of_cblinfun hadamard = matrix_hadamard" *)
(*   unfolding hadamard_def
  apply (rule cblinfun_of_mat_inverse)
  by (auto simp add: matrix_hadamard_def) *)
(* definition "matrix_CNOT = mat_of_rows_list 4 [ [1::complex,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0] ]" *)
(* lemma bounded_of_mat_CNOT[code]: "mat_of_cblinfun CNOT = matrix_CNOT" *)

(* TODO move *)
instantiation bit :: linorder begin
definition "less_bit (a::bit) (b::bit) = (a=0 \<and> b=1)"
definition "less_eq_bit (a::bit) b = (a=b \<or> a<b)"
instance apply intro_classes unfolding less_bit_def less_eq_bit_def by auto
end

(* Defined in Registers.Misc *)
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


(* Already in Quantum.thy (via alias \<beta>00) *)
(* lemma vec_of_ell2_EPR[code]: "vec_of_ell2 EPR = vec_of_list [1/sqrt 2,0,0,1/sqrt 2]" *)

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
                 (eigenspace 1 (comm_op o\<^sub>C\<^sub>L (V* o\<^sub>C\<^sub>L U) \<otimes>\<^sub>o (U* o\<^sub>C\<^sub>L V))) \<guillemotright> \<lbrakk>Q,R\<rbrakk>)"
  unfolding quantum_equality_full_def 
  by auto

lemma space_div_unlifted_code [code]: 
  "space_div_unlifted S \<psi> = kernel ((Proj S - id_cblinfun) o\<^sub>C\<^sub>L tensor_ell2_right \<psi>)"
proof (rule ccsubspace_eqI)
  fix x :: \<open>'a ell2\<close>
  define A :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close> where \<open>A = tensor_ell2_right \<psi>\<close>
  have \<open>x \<in> space_as_set (space_div_unlifted S \<psi>) \<longleftrightarrow> x \<otimes>\<^sub>s \<psi> \<in> space_as_set S\<close>
    by (simp add: space_div_unlifted.rep_eq)
  also have \<open>\<dots> \<longleftrightarrow> tensor_ell2_right \<psi> x \<in> space_as_set S\<close>
    by simp
  also have \<open>\<dots> \<longleftrightarrow> (Proj S - id_cblinfun) *\<^sub>V tensor_ell2_right \<psi> x = 0\<close>
    by (metis (no_types, lifting) Proj_fixes_image cblinfun.diff_left eq_iff_diff_eq_0 id_cblinfun.rep_eq norm_Proj_apply)
  also have \<open>\<dots> \<longleftrightarrow> x \<in> space_as_set (kernel ((Proj S - id_cblinfun) o\<^sub>C\<^sub>L tensor_ell2_right \<psi>))\<close>
    by (simp add: kernel_member_iff)
  finally show \<open>x \<in> space_as_set (space_div_unlifted S \<psi>) \<longleftrightarrow> \<dots>\<close>
    by -
qed

(* TODO needed? We can't give a code equation for cregister_pair anyway *)
definition cregister_to_coderep :: \<open>('a,'b) cregister \<Rightarrow> (('b \<Rightarrow> 'a) \<times> ('a => 'b => 'b)) option\<close> where
  \<open>cregister_to_coderep R = (if cregister R then Some (getter R, setter R) else None)\<close>

fun cregister_from_coderep :: \<open>(('b \<Rightarrow> 'a) \<times> ('a => 'b => 'b)) option \<Rightarrow> ('a,'b) cregister\<close> where
  \<open>cregister_from_coderep None = non_cregister\<close>
| \<open>cregister_from_coderep (Some (g, s)) = cregister_from_getter_setter g s\<close>

lemma cregister_to_coderep_inverse[code abstype]: \<open>cregister_from_coderep (cregister_to_coderep R) = R\<close>
  apply (cases \<open>cregister R\<close>)
  by (auto simp: cregister_to_coderep_def cregister_eqI_setter
      setter_of_cregister_from_getter_is_cregister setter_of_cregister_from_getter_setter
      valid_getter_setter_def non_cregister)
lemma [code]: \<open>cregister_to_coderep cFst = Some (fst, \<lambda>a. apfst (\<lambda>_. a))\<close>
  by (simp add: cregister_to_coderep_def setter_cFst[abs_def] case_prod_unfold)
lemma [code]: \<open>cregister_to_coderep cSnd = Some (snd, \<lambda>b. apsnd (\<lambda>_. b))\<close>
  by (simp add: cregister_to_coderep_def setter_cSnd[abs_def] case_prod_unfold)
lemma [code]: \<open>getter R = (case cregister_to_coderep R of 
  None \<Rightarrow> Code.abort STR ''getter of non_cregister executed'' (\<lambda>_. getter R)
  | Some (g, s) \<Rightarrow> g)\<close>
  by (simp add: cregister_to_coderep_def)
lemma [code]: \<open>setter R = (case cregister_to_coderep R of 
  None \<Rightarrow> Code.abort STR ''setter of non_cregister executed'' (\<lambda>_. setter R)
  | Some (g, s) \<Rightarrow> s)\<close>
  by (simp add: cregister_to_coderep_def)
lemma [code]: \<open>cregister_to_coderep cregister_id = Some (id, \<lambda>x _. x)\<close>
  by (simp add: cregister_to_coderep_def getter_id[abs_def] setter_id[abs_def] id_def)

(* TODO think of something more efficient... *)
lemma apply_qregister_space_code_hack: \<open>apply_qregister_space (qregister_of_cregister F) S = apply_qregister (qregister_of_cregister F) (Proj S) *\<^sub>S \<top>\<close>
  by (rule apply_qregister_space_def)

(* TODO: remove once "code del" is added at the definitions themselves \<longrightarrow> is already done! *)
(* declare ord_clinear_space_inst.less_eq_clinear_space[code del]
declare ord_clinear_space_inst.less_clinear_space[code del] *)

(* derive (eq) ceq bit *) (* In Registers.Quantum *)
derive (linorder) compare_order bit
(* derive (compare) ccompare bit *) (* In Registers.Quantum *)
(* derive (dlist) set_impl bit *) (* In Registers.Quantum *)
derive (eq) ceq real
derive (linorder) compare real
derive (compare) ccompare real
derive (eq) ceq complex
derive (no) ccompare complex

(* (* TODO: remove *)
lemmas prepare_for_code = quantum_equality_full_def_let (* add_join_variables_hint *) space_div_space_div_unlifted
  (* space_div_add_extend_lift_as_var_concat_hint *) INF_lift Cla_inf_lift Cla_plus_lift Cla_sup_lift
  top_leq_lift top_geq_lift bot_leq_lift bot_geq_lift top_eq_lift bot_eq_lift top_eq_lift2 bot_eq_lift2 *)

declare mat_of_cblinfun_tensor_op[code]

subsection \<open>\<open>prepare_for_code\<close> method\<close>

lemmas prepare_for_code_add =
  (* qregister_of_cregister_Fst[symmetric] qregister_of_cregister_Snd[symmetric] *)
  (* qregister_of_cregister_pair[symmetric] qregister_of_cregister_chain[symmetric] *)
  apply_qregister_of_cregister permute_and_tensor1_cblinfun_code_prep
  same_outside_cregister_def

  apply_qregister_space_code_hack (* TODO think of something more efficient *)

  case_prod_beta if_distrib[of fst] if_distrib[of snd] prod_eq_iff

  div_leq_simp mod_mod_cancel

  getter_pair getter_chain setter_chain setter_pair setter_cFst setter_cSnd

  enum_index_prod_def fst_enum_nth snd_enum_nth enum_index_nth if_distrib[of enum_index]
  enum_nth_injective

  quantum_equality_full_def_let space_div_space_div_unlifted INF_lift Cla_inf_lift Cla_plus_lift Cla_sup_lift
  top_leq_lift top_geq_lift bot_leq_lift bot_geq_lift top_eq_lift bot_eq_lift top_eq_lift2 bot_eq_lift2

lemmas prepare_for_code_flip =
  qregister_of_cregister_Fst qregister_of_cregister_Snd
  qregister_of_cregister_pair qregister_of_cregister_chain


method prepare_for_code = (
    translate_to_index_registers,
    simp add: join_registers cong del: if_weak_cong add: prepare_for_code_add flip: prepare_for_code_flip
    )


unbundle no jnf_syntax

end
