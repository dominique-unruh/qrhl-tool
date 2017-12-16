theory QRHL_Code
  imports QRHL "Jordan_Normal_Form.Matrix_Impl"
begin

hide_const (open) Lattice.sup
hide_const (open) Lattice.inf
hide_const (open) Order.top
hide_const (open) card_UNIV

no_syntax "\<^const>Group.monoid.mult"    :: "['a, 'a, 'a] \<Rightarrow> 'a" (infixl "\<otimes>\<index>" 70)
no_syntax "\<^const>Lattice.meet" :: "[_, 'a, 'a] => 'a" (infixl "\<sqinter>\<index>" 70)


axiomatization bounded_of_mat :: "complex mat \<Rightarrow> ('a::enum,'b::enum) bounded"
  and mat_of_bounded :: "('a::enum,'b::enum) bounded \<Rightarrow> complex mat"
axiomatization vector_of_vec :: "complex vec \<Rightarrow> ('a::enum) vector"
  and vec_of_vector :: "('a::enum) vector \<Rightarrow> complex vec"

axiomatization where mat_of_bounded_inverse [code abstype]:
  "bounded_of_mat (mat_of_bounded B) = B"

axiomatization where vec_of_vector_inverse [code abstype]:
  "vector_of_vec (vec_of_vector B) = B"


fun index_of where
  "index_of x [] = (0::nat)"
| "index_of x (y#ys) = (if x=y then 0 else (index_of x ys + 1))"

definition "enum_idx (x::'a::enum) = index_of x (enum_class.enum :: 'a list)"
definition "enum_len (TYPE('a::enum)) = length (enum_class.enum :: 'a list)"

axiomatization where bounded_of_mat_id[code]:
  "mat_of_bounded (idOp :: ('a::enum,'a) bounded) = one_mat (enum_len TYPE('a))"
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
axiomatization where bounded_of_mat_X[code]: "mat_of_bounded X = matrix_X"
definition "matrix_Z = mat_of_rows_list 2 [ [1::complex,0], [0,-1] ]"
axiomatization where bounded_of_mat_Z[code]: "mat_of_bounded Z = matrix_Z"
definition "matrix_Y = mat_of_rows_list 2 [ [0::complex,-\<i>], [\<i>,0] ]"
axiomatization where bounded_of_mat_Y[code]: "mat_of_bounded Y = matrix_Y"
definition "matrix_H' = mat_of_rows_list 2 [ [1::complex, 1], [1, -1] ]"
axiomatization where bounded_of_mat_H'[code]: "mat_of_bounded H' = matrix_H'"
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
  "vec_of_vector (0::'a::enum vector) = zero_vec (enum_len TYPE('a))"

axiomatization where mat_of_bounded_proj[code]:
  "mat_of_bounded (proj \<psi>) = 
    (let v = vec_of_vector \<psi>; d = dim_vec v in
    if \<psi>=0 then zero_mat d d else
          smult_mat (1/(cscalar_prod v v)) (mat_of_cols d [v] * mat_of_rows d [v]))"
for \<psi> :: "'a::enum vector"

axiomatization where vec_of_vector_basis_vector[code]:
  "vec_of_vector (basis_vector i) = unit_vec (enum_len TYPE('a)) (enum_idx i)" for i::"'a::enum"

instantiation bit :: linorder begin
definition "less_bit (a::bit) (b::bit) = (a=0 \<and> b=1)"
definition "less_eq_bit (a::bit) b = (a=b \<or> a<b)"
instance apply intro_classes unfolding less_bit_def less_eq_bit_def by auto
end


derive (eq) ceq bit
derive (linorder) compare_order bit
derive (compare) ccompare bit
derive (dlist) set_impl bit
print_derives

instantiation bit :: card_UNIV begin
definition "finite_UNIV_bit = Phantom(bit) True"
definition "card_UNIV_bit = Phantom(bit) (2::nat)"
instance apply intro_classes unfolding finite_UNIV_bit_def card_UNIV_bit_def 
  apply auto unfolding UNIV_bit by simp 
end

axiomatization where mat_of_bounded_zero[code]:
  "mat_of_bounded (0::('a::enum,'b::enum) bounded) = zero_mat (enum_len TYPE('b)) (enum_len TYPE('a))"


derive (eq) ceq real
derive (linorder) compare real
derive (compare) ccompare real
derive (eq) ceq complex
derive (no) ccompare complex


(*
section {* Experiments *}

value "mat_of_bounded CNOT"

value "matrix_tensor (mat_of_bounded CNOT) (mat_of_bounded X)"

value "tensorOp (CNOT::(_,_)bounded) (idOp::(bit,_)bounded)"


lemma "H \<cdot> X = Z \<cdot> H"
  unfolding H_H' 
  apply (rule  add_scalar_mult[of sqrt2]) 
  using [[show_brackets]]
  apply auto
  by code_simp



lemma "proj (H \<cdot> basis_vector (0::bit)) + proj (H \<cdot> basis_vector (1::bit)) = idOp"
  unfolding H_H'
  using [[show_brackets]]
  apply simp                                               
  by normalization
  
lemma "sum (\<lambda>i::bit*bit. proj (CNOT \<cdot> (H\<otimes>H) \<cdot> basis_vector i)) (set enum_class.enum) = idOp"
  unfolding H_H' 
  apply simp
  by eval

value [code] "sum (\<lambda>i::bit. proj (basis_vector i)) (set enum_class.enum) = idOp"




value "tensorOp CNOT X"
value X
value "(tensorOp CNOT X) \<cdot> basis_vector ((0,0),0)"
value "basis_vector ((0::bit,0::bit),1::bit)"

























lemma "(tensorOp CNOT X) \<cdot> basis_vector ((a,b),c) = basis_vector ((a,a+b),1+c)"
  apply (rule spec[of _ a])
  apply (rule spec[of _ b])
  apply (rule spec[of _ c])
  by eval

lemma tensor_lift:
  assumes "colocal R Q"
  shows "A\<guillemotright>Q = (idOp\<otimes>A)\<guillemotright>qvariable_concat R Q" sorry

lemma lift_swap:
  fixes A :: "(_,_) bounded"
  assumes "colocal Q R"
  shows "A \<guillemotright> qvariable_concat Q R = (comm_op \<cdot> A \<cdot> comm_op) \<guillemotright> qvariable_concat R Q"
  sorry

lemma lift_assoc:
  fixes A :: "(('a*'b)*'c,_) bounded"
  assumes "colocal Q R" and "colocal Q S" and "colocal S R"
  shows "A \<guillemotright> qvariable_concat (qvariable_concat Q R) S = (assoc_op* \<cdot> A \<cdot> assoc_op) \<guillemotright> qvariable_concat Q (qvariable_concat R S)"
  sorry

lemma times_lift:
  fixes A B :: "(_,_) bounded"
  shows "(A \<guillemotright> Q) \<cdot> (B \<guillemotright> Q) = (A \<cdot> B) \<guillemotright> Q"
  sorry
  
lemma lift_eq[simp]: 
  fixes B :: "('a,'a) bounded"
  shows "(A \<guillemotright> Q = B \<guillemotright> Q) = (A=B)"
  sorry

(* lemma assms: "colocal (A::'b qvariables) (B::'a qvariables)" sorry (*TODO remove! WRONG!*) *)

lemma VUadjU[simp]: 
  fixes V :: "('a,'b) bounded"
  assumes "unitary U"
  shows "V \<cdot> U \<cdot> U* = V"
  sorry

lemma Vcommcomm[simp]:
  fixes V :: "(_,_) bounded"
  shows "V \<cdot> comm_op \<cdot> comm_op = V"
  sorry

lemma tensor_times: 
  fixes A :: "('a,'b)bounded"
    and B :: "('c,'d)bounded"
  shows "(A\<otimes>B) \<cdot> (C\<otimes>D) = (A\<cdot>C) \<otimes> (B\<cdot>D)"
  sorry

lemma tensor_times': 
  fixes V A B :: "(_,_)bounded"
  shows "V \<cdot> (A\<otimes>B) \<cdot> (C\<otimes>D) = V \<cdot> (A\<cdot>C) \<otimes> (B\<cdot>D)"
  sorry

lemma comm_op_tensor: "comm_op \<cdot> (A \<otimes> B) = (B \<otimes> A) \<cdot> comm_op" 
  sorry


(* value "matrix (assoc_op* \<cdot> CNOT \<otimes> X \<cdot> assoc_op \<cdot> proj (basis_vector (a, b, c)))" *)

(* lemmas prepare_code = matrix_adjoint *)

(* lemma matrix_classical_operator: "matrix (classical_operator f) = undefined" sorry *)

value CNOT
value "basis_vector (0::bit,1::bit)"
value "basis_vector (1::bit,1::bit)"

value "Enum.enum :: (bit*bit) list"

value "CNOT \<cdot> basis_vector (0,1) = basis_vector (0,1)"

value "(CNOT \<otimes> X) \<cdot>  (basis_vector ((0,1),0)) = basis_vector (((0, 1), 1))"

value "assoc_op* \<cdot> CNOT \<otimes> X \<cdot> assoc_op \<cdot> proj (basis_vector (0,1,0)) \<cdot> assoc_op* \<cdot> (CNOT \<otimes> X)* \<cdot> assoc_op =
 proj (basis_vector ((0, 1, 1)))
"

value "comm_op :: ((bit*bit)*bit,_) bounded"
value "comm_op :: (bit*(bit*bit),_) bounded"

(* TODO: True *)
value " (basis_vector (((0, 1), 1)))
=
    comm_op \<cdot> (basis_vector ((1, (0, 1))::bit*bit*bit))"


value " proj (basis_vector (((0, 1), 1)))
=
    comm_op \<cdot> proj (basis_vector ((1, (0, 1))::bit*bit*bit)) \<cdot> comm_op"

value "assoc_op* \<cdot> CNOT \<otimes> X \<cdot> assoc_op \<cdot> proj (basis_vector (0,1,0)) \<cdot> assoc_op* \<cdot> (CNOT \<otimes> X)* \<cdot> assoc_op =
    assoc_op* \<cdot> comm_op \<cdot> proj (basis_vector ((1, 0, 1)::bit*bit*bit)) \<cdot> comm_op \<cdot> assoc_op"

find_theorems "Group.monoid.mult"
term "a\<otimes>b"

lemma
  assumes "colocal \<lbrakk>Q3\<rbrakk> \<lbrakk>Q1, Q2\<rbrakk>" "colocal \<lbrakk>Q1, Q2\<rbrakk> \<lbrakk>Q3\<rbrakk>" "colocal \<lbrakk>Q1\<rbrakk> \<lbrakk>Q2\<rbrakk>" "colocal \<lbrakk>Q1\<rbrakk> \<lbrakk>Q3\<rbrakk>" "colocal \<lbrakk>Q3\<rbrakk> \<lbrakk>Q2\<rbrakk>"
  shows "CNOT\<guillemotright>\<lbrakk>Q1,Q2\<rbrakk> \<cdot> X\<guillemotright>\<lbrakk>Q3\<rbrakk> \<cdot> (proj (basis_vector (a,b,c)) \<guillemotright> \<lbrakk>Q1,Q2,Q3\<rbrakk>)  \<cdot> (CNOT\<guillemotright>\<lbrakk>Q1,Q2\<rbrakk> \<cdot> X\<guillemotright>\<lbrakk>Q3\<rbrakk>)* = proj (basis_vector (1+c,a,a+b)) \<guillemotright> \<lbrakk>Q3,Q1,Q2\<rbrakk>"
  apply (subst tensor_lift[where Q="\<lbrakk>Q1,Q2\<rbrakk>" and R="\<lbrakk>Q3\<rbrakk>"])
   apply (simp add: assms)
  apply (subst tensor_lift[where Q="\<lbrakk>Q1,Q2\<rbrakk>" and R="\<lbrakk>Q3\<rbrakk>"])
   apply (simp add: assms)
  apply (subst tensor_lift[where Q="\<lbrakk>Q3\<rbrakk>" and R="\<lbrakk>Q1,Q2\<rbrakk>"])
   apply (simp add: assms)
  apply (subst tensor_lift[where Q="\<lbrakk>Q3\<rbrakk>" and R="\<lbrakk>Q1,Q2\<rbrakk>"])
   apply (simp add: assms)
  apply (subst lift_swap[where Q="\<lbrakk>Q3\<rbrakk>" and R="\<lbrakk>Q1,Q2\<rbrakk>"])
   apply (simp add: assms)
  apply (subst lift_swap[where Q="\<lbrakk>Q3\<rbrakk>" and R="\<lbrakk>Q1,Q2\<rbrakk>"])
   apply (simp add: assms)
  apply (subst lift_swap[where Q="\<lbrakk>Q3\<rbrakk>" and R="\<lbrakk>Q1,Q2\<rbrakk>"])
   apply (simp add: assms)
  apply (subst lift_assoc)
     apply (simp_all add: assms)[3]
  apply (subst lift_assoc)
     apply (simp_all add: assms)[3]
  apply (subst lift_assoc)
     apply (simp_all add: assms)[3]
  apply (subst lift_assoc)
     apply (simp_all add: assms)[3]
  apply (subst lift_assoc)
     apply (simp_all add: assms)[3]
  apply (simp add: times_lift timesOp_assoc comm_op_tensor tensor_times')
  
  apply (rule spec[of _ a], rule spec[of _ b], rule spec[of _ c])
  by eval

*)

end