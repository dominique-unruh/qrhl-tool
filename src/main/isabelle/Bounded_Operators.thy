theory Bounded_Operators
  imports Complex_L2 "HOL-Library.Adhoc_Overloading"
begin


subsection \<open>Bounded operators\<close>

typedef ('a,'b) bounded = "{A::'a vector\<Rightarrow>'b vector. bounded_linear A}"
  morphisms applyOp Abs_bounded
  using bounded_linear_zero by blast
setup_lifting type_definition_bounded

lift_definition idOp :: "('a,'a)bounded" is id
  by (metis bounded_linear_ident comp_id fun.map_ident)

instantiation bounded :: (type,type) zero begin
lift_definition zero_bounded :: "('a,'b) bounded" is "\<lambda>_. 0" by simp
instance ..
end

(* lift_definition timesOp :: "('b,'c) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'c) bounded" is "(o)"
  unfolding bounded_linear_def unfolding linear_def linear_axioms_def *)

axiomatization
  adjoint :: "('a,'b) bounded \<Rightarrow> ('b,'a) bounded" ("_*" [99] 100)
and timesOp :: "('b,'c) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'c) bounded" 
(* and applyOp :: "('a,'b) bounded \<Rightarrow> 'a vector \<Rightarrow> 'b vector" *)
and applyOpSpace :: "('a,'b) bounded \<Rightarrow> 'a subspace \<Rightarrow> 'b subspace"
and timesScalarOp :: "complex \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded"
and timesScalarSpace :: "complex \<Rightarrow> 'a subspace \<Rightarrow> 'a subspace"
where
 applyOp_0[simp]: "applyOpSpace U 0 = 0"
and times_applyOp: "applyOp (timesOp A B) \<psi> = applyOp A (applyOp B \<psi>)"
and timesScalarSpace_0[simp]: "timesScalarSpace 0 S = 0"
and timesScalarSpace_not0[simp]: "a \<noteq> 0 \<Longrightarrow> timesScalarSpace a S = S"
and one_times_op[simp]: "timesScalarOp (1::complex) B = B"

axiomatization where scalar_times_adj[simp]: "(timesScalarOp a A)* = timesScalarOp (cnj a) (A*)" for A::"('a,'b)bounded"

axiomatization where
  timesOp_assoc: "timesOp (timesOp A B) C = timesOp A (timesOp B C)" 
and times_adjoint[simp]: "adjoint (timesOp A B) = timesOp (adjoint B) (adjoint A)"
for A :: "('b,'a) bounded" and B :: "('c,'b) bounded" and C :: "('d,'c) bounded"

axiomatization where
  timesOp_assoc_subspace: "applyOpSpace (timesOp A B) S = applyOpSpace A (applyOpSpace B S)"
for S :: "'a subspace" and B :: "('a,'b) bounded" and A :: "('b,'c) bounded"



axiomatization plusOp :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" 
  (* and uminusOp :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded" *)
  where
  plusOp_assoc: "plusOp (plusOp a b) c = plusOp a (plusOp b c)"
  and plusOp_comm: "plusOp a b = plusOp b a"
  and plusOp_0: "plusOp 0 a = a"
  and plusOp_cancel: "plusOp (uminusOp a) a = 0"
for a b c :: "('a,'b) bounded"

lemmas assoc_left = timesOp_assoc[symmetric] timesOp_assoc_subspace[symmetric] plusOp_assoc[symmetric]
lemmas assoc_right = timesOp_assoc timesOp_assoc_subspace plusOp_assoc

instantiation bounded :: (type,type) ab_group_add begin
definition "(+) = plusOp" 
definition "uminus = timesScalarOp (-1)"
definition "A - B = A + (uminus B)" for A::"('a,'b) bounded"
instance apply intro_classes
  unfolding plus_bounded_def minus_bounded_def uminus_bounded_def
      apply (fact plusOp_assoc)
     apply (fact plusOp_comm)
    apply (fact plusOp_0)
   apply (fact plusOp_cancel)
  by auto
end

axiomatization where scalar_times_op_add[simp]: "timesScalarOp a (A+B) = timesScalarOp a A + timesScalarOp a B" for a::complex and A B :: "('a,'b) bounded"
lemma scalar_times_op_minus[simp]: "timesScalarOp a (A-B) = timesScalarOp a A - timesScalarOp a B" for a::complex and A B :: "('a,'b) bounded"
  by (metis add_diff_cancel_right' diff_add_cancel scalar_times_op_add)

lemma applyOp_bot[simp]: "applyOpSpace U bot = bot"
  by (simp add: subspace_zero_bot[symmetric])

axiomatization where equal_basis: "(\<And>x. applyOp A (ket x) = applyOp B (ket x)) \<Longrightarrow> A = B" for A::"('a,'b) bounded"

axiomatization where adjoint_twice[simp]: "(U*)* = U" for U :: "('a,'b) bounded"

(* TODO: move specialized syntax into QRHL-specific file *)
consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)
adhoc_overloading
  cdot timesOp applyOp applyOpSpace timesScalarOp timesScalarSpace timesScalarVec

axiomatization where
  cdot_plus_distrib[simp]: "U \<cdot> (A + B) = U \<cdot> A + U \<cdot> B"
for A B :: "'a subspace" and U :: "('a,'b) bounded"

axiomatization where scalar_op_subspace_assoc [simp]: 
  "(\<alpha>\<cdot>A)\<cdot>S = \<alpha>\<cdot>(A\<cdot>S)" for \<alpha>::complex and A::"('a,'b)bounded" and S::"'a subspace"

lemma apply_idOp[simp]: "applyOp idOp \<psi> = \<psi>"
  by (simp add: idOp.rep_eq)

axiomatization where scalar_mult_1_op[simp]: "1 \<cdot> A = A" for A::"('a,'b)bounded"
axiomatization where scalar_mult_0_op[simp]: "(0::complex) \<cdot> A = 0" for A::"('a,'b)bounded" 
axiomatization where scalar_op_op[simp]: "(a \<cdot> A) \<cdot> B = a \<cdot> (A \<cdot> B)" 
  for a :: complex and A :: "('a,'b) bounded" and B :: "('c,'a) bounded"
axiomatization where op_scalar_op[simp]: "A \<cdot> (a \<cdot> B) = a \<cdot> (A \<cdot> B)" 
  for a :: complex and A :: "('a,'b) bounded" and B :: "('c,'a) bounded" 
axiomatization where scalar_scalar_op[simp]: "a \<cdot> (b \<cdot> A) = (a*b) \<cdot> A"
  for a b :: complex and A  :: "('a,'b) bounded" 
axiomatization where scalar_op_vec[simp]: "(a \<cdot> A) \<cdot> \<psi> = a \<cdot> (A \<cdot> \<psi>)" 
  for a :: complex and A :: "('a,'b) bounded" and \<psi> :: "'a vector" 
axiomatization where add_scalar_mult: "a\<noteq>0 \<Longrightarrow> a \<cdot> A = a \<cdot> B \<Longrightarrow> A=B" for A B :: "('a,'b)bounded" and a::complex 

axiomatization where
    apply_idOp_space[simp]: "applyOpSpace idOp S = S"
and apply_0[simp]: "applyOp U 0 = 0"
and times_idOp1[simp]: "U \<cdot> idOp = U"
and times_idOp2[simp]: "idOp \<cdot> V = V"
and idOp_adjoint[simp]: "idOp* = idOp"
for \<psi> :: "'a vector" and S :: "'a subspace" and U :: "('a,'b) bounded" and V :: "('b,'a) bounded"

axiomatization where mult_INF[simp]: "U \<cdot> (INF x. V x) = (INF x. U \<cdot> V x)" 
  for V :: "'a \<Rightarrow> 'b subspace" and U :: "('b,'c) bounded"

lemma mult_inf_distrib[simp]: "U \<cdot> (B \<sqinter> C) = (U \<cdot> B) \<sqinter> (U \<cdot> C)" 
  for U :: "('a,'b) bounded" and B C :: "'a subspace"
  using mult_INF[where V="\<lambda>x. if x then B else C" and U=U] 
  unfolding INF_UNIV_bool_expand
  by simp

definition "inj_option \<pi> = (\<forall>x y. \<pi> x = \<pi> y \<and> \<pi> x \<noteq> None \<longrightarrow> x = y)"
definition "inv_option \<pi> = (\<lambda>y. if Some y \<in> range \<pi> then Some (Hilbert_Choice.inv \<pi> (Some y)) else None)"
lemma inj_option_Some_pi[simp]: "inj_option (Some o \<pi>) = inj \<pi>"
  unfolding inj_option_def inj_def by simp

lemma inj_option_Some[simp]: "inj_option Some"
  using[[show_consts,show_types,show_sorts]]
  apply (rewrite asm_rl[of "(Some::'a\<Rightarrow>_) = Some o id"]) apply simp
  unfolding inj_option_Some_pi by simp

lemma inv_option_Some: "surj \<pi> \<Longrightarrow> inv_option (Some o \<pi>) = Some o (Hilbert_Choice.inv \<pi>)"
  unfolding inv_option_def o_def inv_def apply (rule ext) by auto
lemma inj_option_map_comp[simp]: "inj_option f \<Longrightarrow> inj_option g \<Longrightarrow> inj_option (f \<circ>\<^sub>m g)"
  unfolding inj_option_def apply auto
  by (smt map_comp_Some_iff)

lemma inj_option_inv_option[simp]: "inj_option (inv_option \<pi>)"
proof (unfold inj_option_def, rule allI, rule allI, rule impI, erule conjE)
  fix x y
  assume same: "inv_option \<pi> x = inv_option \<pi> y"
    and pix_not_None: "inv_option \<pi> x \<noteq> None"
  have x_pi: "Some x \<in> range \<pi>" 
    using pix_not_None unfolding inv_option_def apply auto
    by (meson option.distinct(1))
  have y_pi: "Some y \<in> range \<pi>" 
    using pix_not_None unfolding same unfolding inv_option_def apply auto
    by (meson option.distinct(1))
  have "inv_option \<pi> x = Some (Hilbert_Choice.inv \<pi> (Some x))"
    unfolding inv_option_def using x_pi by simp
  moreover have "inv_option \<pi> y = Some (Hilbert_Choice.inv \<pi> (Some y))"
    unfolding inv_option_def using y_pi by simp
  ultimately have "Hilbert_Choice.inv \<pi> (Some x) = Hilbert_Choice.inv \<pi> (Some y)"
    using same by simp
  then show "x = y"
    by (meson inv_into_injective option.inject x_pi y_pi)
qed


axiomatization classical_operator :: "('a\<Rightarrow>'b option) \<Rightarrow> ('a,'b) bounded" where
 classical_operator_basis: "inj_option \<pi> \<Longrightarrow>
    applyOp (classical_operator \<pi>) (ket x) = (case \<pi> x of Some y \<Rightarrow> ket y | None \<Rightarrow> 0)"
axiomatization where classical_operator_adjoint[simp]: 
  "inj_option \<pi> \<Longrightarrow> adjoint (classical_operator \<pi>) = classical_operator (inv_option \<pi>)"
for \<pi> :: "'a \<Rightarrow> 'b option"


lemma classical_operator_mult[simp]:
  "inj_option \<pi> \<Longrightarrow> inj_option \<rho> \<Longrightarrow> classical_operator \<pi> \<cdot> classical_operator \<rho> = classical_operator (map_comp \<pi> \<rho>)"
  apply (rule equal_basis)
  unfolding times_applyOp
  apply (subst classical_operator_basis, simp)+
  apply (case_tac "\<rho> x")
   apply auto
  apply (subst classical_operator_basis, simp)
  by auto


lemma classical_operator_Some[simp]: "classical_operator Some = idOp"
  apply (rule equal_basis) apply (subst classical_operator_basis) apply simp by auto

definition "unitary U = (U \<cdot> (U*) = idOp \<and> U* \<cdot> U = idOp)"  
definition "isometry U = (U* \<cdot> U = idOp)"  

lemma adjUU[simp]: "isometry U \<Longrightarrow> U* \<cdot> U = idOp" unfolding isometry_def by simp
lemma UadjU[simp]: "unitary U \<Longrightarrow> U \<cdot> U* = idOp" unfolding unitary_def by simp

lemma unitary_isometry[simp]: "unitary U \<Longrightarrow> isometry U"
  unfolding unitary_def isometry_def by simp

lemma unitary_adjoint[simp]: "unitary (U*) = unitary U" for U::"('a,'b)bounded"
  unfolding unitary_def by auto

lemma unitary_times[simp]: "unitary A \<Longrightarrow> unitary B \<Longrightarrow> unitary (A\<cdot>B)"
  unfolding unitary_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma isometry_times[simp]: "isometry A \<Longrightarrow> isometry B \<Longrightarrow> isometry (A\<cdot>B)"
  unfolding isometry_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma isometry_classical_operator[simp]:
  assumes "inj \<pi>"
  shows "isometry (classical_operator (Some o \<pi>))"
proof -
  have comp: "inv_option (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>) = Some" 
    apply (rule ext) unfolding inv_option_def o_def 
    using assms unfolding inj_def inv_def by auto

  show ?thesis
    unfolding isometry_def
    apply (subst classical_operator_adjoint) using assms apply simp
    apply (subst classical_operator_mult) using assms apply auto[2]
    apply (subst comp)
    by simp
qed

lemma unitary_classical_operator[simp]:
  assumes "bij \<pi>"
  shows "unitary (classical_operator (Some o \<pi>))"
proof (unfold unitary_def, rule conjI)
  have "isometry (classical_operator (Some o \<pi>))"
    by (simp add: assms bij_is_inj)
  then show "classical_operator (Some \<circ> \<pi>)* \<cdot> classical_operator (Some \<circ> \<pi>) = idOp"
    unfolding isometry_def by simp
next
  have "inj \<pi>"
    by (simp add: assms bij_is_inj)
  have comp: "Some \<circ> \<pi> \<circ>\<^sub>m inv_option (Some \<circ> \<pi>) = Some"
    apply (rule ext)
    unfolding inv_option_def o_def map_comp_def
    unfolding inv_def apply auto
    apply (metis \<open>inj \<pi>\<close> inv_def inv_f_f)
    by (metis assms bij_def image_iff range_eqI)

  show "classical_operator (Some \<circ> \<pi>) \<cdot> classical_operator (Some \<circ> \<pi>)* = idOp"
    by (simp add: comp \<open>inj \<pi>\<close>)
qed



axiomatization where unitary_image[simp]: "unitary U \<Longrightarrow> applyOpSpace U top = top"
  for U :: "('a,'a) bounded"

lemma unitary_id[simp]: "unitary idOp"
  unfolding unitary_def by simp

axiomatization vector_to_bounded :: "'a vector \<Rightarrow> (unit,'a) bounded"
  where vector_to_bounded_applyOp: "vector_to_bounded (A\<cdot>\<psi>) = A \<cdot> vector_to_bounded \<psi>" for A :: "(_,_)bounded"

lemma vector_to_bounded_scalar_times: "vector_to_bounded (a\<cdot>\<psi>) = a \<cdot> vector_to_bounded \<psi>" for a::complex
  apply (rewrite at "a\<cdot>\<psi>" DEADID.rel_mono_strong[of _ "(a\<cdot>idOp)\<cdot>\<psi>"])
   apply simp
  apply (subst vector_to_bounded_applyOp)
  by simp


axiomatization kernel :: "('a,'b) bounded \<Rightarrow> 'a subspace"
definition eigenspace :: "complex \<Rightarrow> ('a,'a) bounded \<Rightarrow> 'a subspace" where
  "eigenspace a A = kernel (A-a\<cdot>idOp)" 

axiomatization where kernel_scalar_times[simp]: "a\<noteq>0 \<Longrightarrow> kernel (a\<cdot>A) = kernel A" 
  for a :: complex and A :: "('a,'b) bounded"

axiomatization where kernel_0[simp]: "kernel 0 = top"
axiomatization where kernel_id[simp]: "kernel idOp = 0"

lemma [simp]: "a\<noteq>0 \<Longrightarrow> eigenspace b (a\<cdot>A) = eigenspace (b/a) A"
  unfolding eigenspace_def
  apply (rewrite at "kernel \<hole>" DEADID.rel_mono_strong[where y="a \<cdot> (A - b / a \<cdot> idOp)"])
   apply auto[1]
  by (subst kernel_scalar_times, auto)



section \<open>Projectors\<close>

definition "isProjector P = (P=P* \<and> P=P\<cdot>P)"

axiomatization Proj :: "'a subspace \<Rightarrow> ('a,'a) bounded" where
  isProjector_Proj[simp]: "isProjector (Proj S)"
and imageOp_Proj[simp]: "applyOpSpace (Proj S) top = S"

lemma Proj_leq: "Proj S \<cdot> A \<le> S"
  by (metis imageOp_Proj inf.orderE inf.orderI mult_inf_distrib top_greatest)


axiomatization where Proj_times: "A \<cdot> Proj S \<cdot> A* = Proj (A\<cdot>S)" for A::"('a,'b)bounded"

abbreviation proj :: "'a vector \<Rightarrow> ('a,'a) bounded" where "proj \<psi> \<equiv> Proj (span {\<psi>})"

axiomatization where proj_scalar_mult[simp]: 
  "a \<noteq> 0 \<Longrightarrow> proj (a \<cdot> \<psi>) = proj \<psi>" for a::complex and \<psi>::"'a vector"


axiomatization where move_plus:
  "Proj (ortho C) \<cdot> A \<le> B \<Longrightarrow> A \<le> B + C"
for A B C::"'a subspace"


section \<open>Tensor products\<close>

axiomatization "tensorOp" :: "('a,'b) bounded \<Rightarrow> ('c,'d) bounded \<Rightarrow> ('a*'c,'b*'d) bounded"
axiomatization "tensorSpace" :: "'a subspace \<Rightarrow> 'c subspace \<Rightarrow> ('a*'c) subspace"
axiomatization "tensorVec" :: "'a vector \<Rightarrow> 'c vector \<Rightarrow> ('a*'c) vector"
consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infix "\<otimes>" 71)
adhoc_overloading tensor tensorOp tensorSpace tensorVec

axiomatization where idOp_tensor_idOp[simp]: "idOp\<otimes>idOp = idOp"

axiomatization "comm_op" :: "('a*'b, 'b*'a) bounded"

axiomatization where adj_comm_op[simp]: "adjoint comm_op = comm_op"

axiomatization where
  comm_op_swap[simp]: "comm_op \<cdot> (A\<otimes>B) \<cdot> comm_op = B\<otimes>A"
  for A::"('a,'b) bounded" and B::"('c,'d) bounded"

lemma comm_op_times_comm_op[simp]: "comm_op \<cdot> comm_op = idOp"
proof -
  find_theorems "idOp \<otimes> idOp"
  have "comm_op \<cdot> (idOp \<otimes> idOp) \<cdot> comm_op = idOp \<otimes> idOp" by (simp del: idOp_tensor_idOp)
  then show ?thesis by simp
qed

lemma unitary_comm_op[simp]: "unitary comm_op"
  unfolding unitary_def by simp

axiomatization "assoc_op" :: "('a*'b*'c, ('a*'b)*'c) bounded"
  where unitary_assoc_op[simp]: "unitary assoc_op"

axiomatization where tensor_scalar_mult1[simp]: "(a \<cdot> A) \<otimes> B = a \<cdot> (A \<otimes> B)" for a::complex and A::"('a,'b)bounded" and B::"('c,'d)bounded"
axiomatization where tensor_scalar_mult2[simp]: "A \<otimes> (a \<cdot> B) = a \<cdot> (A \<otimes> B)" for a::complex and A::"('a,'b)bounded" and B::"('c,'d)bounded"

axiomatization where tensor_times[simp]: "(U1 \<otimes> U2) \<cdot> (V1 \<otimes> V2) = (U1 \<cdot> V1) \<otimes> (U2 \<cdot> V2)"
  for V1 :: "('a1,'b1) bounded" and U1 :: "('b1,'c1) bounded"
   and V2 :: "('a2,'b2) bounded" and U2 :: "('b2,'c2) bounded"

axiomatization remove_qvar_unit_op :: "('a*unit,'a) bounded"


definition addState :: "'a vector \<Rightarrow> ('b,'b*'a) bounded" where
  "addState \<psi> = idOp \<otimes> (vector_to_bounded \<psi>) \<cdot> remove_qvar_unit_op*"

lemma addState_times_scalar[simp]: "addState (a \<cdot> \<psi>) = a \<cdot> addState \<psi>" for a::complex and psi::"'a vector"
  unfolding addState_def by (simp add: vector_to_bounded_scalar_times)

axiomatization where tensor_adjoint[simp]: "adjoint (U\<otimes>V) = (adjoint U) \<otimes> (adjoint V)"
  for U :: "('a,'b) bounded" and V :: "('c,'d) bounded"


lemma tensor_unitary[simp]: 
  assumes "unitary U" and "unitary V"
  shows "unitary (U\<otimes>V)"
  using assms unfolding unitary_def by simp

end
