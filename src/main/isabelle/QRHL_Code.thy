theory QRHL_Code
  imports QRHL "Jordan_Normal_Form.Matrix_Impl"
begin

hide_const (open) Lattice.sup
hide_const (open) Lattice.inf
hide_const (open) Order.top

axiomatization bounded_of_mat :: "complex mat \<Rightarrow> ('a::enum,'b::enum) bounded"
  and mat_of_bounded :: "('a::enum,'b::enum) bounded \<Rightarrow> complex mat"
axiomatization vector_of_vec :: "complex vec \<Rightarrow> ('a::enum) vector"
  and vec_of_vector :: "('a::enum) vector \<Rightarrow> complex vec"

lemma [code abstype]:
  "bounded_of_mat (mat_of_bounded B) = B"





section \<open>Matrix computations, try 2\<close>

fun index_of where
  "index_of x [] = (0::nat)"
| "index_of x (y#ys) = (if x=y then 0 else (index_of x ys + 1))"

(* Forces evaluation of matrix, to avoid that the functions inside are reevaluated all the time *)
definition "fix_mat M = mat_of_rows_list (dim_col M) (mat_to_list M)"
definition "fix_vec v = vec_of_list (list_of_vec v)"

axiomatization bounded_of_mat :: "complex mat \<Rightarrow> ('a::enum,'b::enum) bounded"
axiomatization vector_of_vec :: "complex vec \<Rightarrow> ('a::enum) vector"
definition "enum_idx (x::'a::enum) = index_of x (enum_class.enum :: 'a list)"
axiomatization where bounded_of_mat_id:
  "(idOp :: ('a::enum,'a) bounded) = bounded_of_mat (one_mat (card_UNIV TYPE('a)))"
axiomatization where bounded_of_mat_timesOp:
  "bounded_of_mat M \<cdot> bounded_of_mat N = bounded_of_mat (fix_mat (M*N))"
axiomatization where vector_of_vec_applyOp:
  "bounded_of_mat M \<cdot> vector_of_vec x = vector_of_vec (fix_vec (mult_mat_vec M x))"

axiomatization where bounded_of_mat_eq:
  "(bounded_of_mat M = bounded_of_mat N) = (mat_to_list M = mat_to_list N)"
axiomatization where vector_of_vec_eq:
  "(vector_of_vec x = vector_of_vec y) = (list_of_vec x = list_of_vec y)"


axiomatization where vector_of_vec_basis_vector: 
  "basis_vector i = vector_of_vec (unit_vec (card_UNIV TYPE('a)) (enum_idx i))" for i::"'a::enum"

definition "matrix_X = mat_of_rows_list 2 [ [0::complex,1], [1,0] ]"
axiomatization where bounded_of_mat_X: "X = bounded_of_mat matrix_X"
definition "matrix_H = mat_of_rows_list 2 [ [1/sqrt 2::complex, 1/sqrt 2], [1/sqrt 2, -1/sqrt 2] ]"
axiomatization where bounded_of_mat_H: "H = bounded_of_mat matrix_H"
definition "matrix_CNOT = mat_of_rows_list 4 [ [1::complex,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0] ]"
axiomatization where bounded_of_mat_CNOT: "CNOT = bounded_of_mat matrix_CNOT"

definition "matrix_tensor (A::'a::times mat) (B::'a mat) =
  mat (dim_row A*dim_row B) (dim_col A*dim_col B) 
  (\<lambda>(r,c). A $$ (r div dim_row A, c div dim_col A) *
           B $$ (r mod dim_row B, c mod dim_col B))"

axiomatization where bounded_of_mat_tensorOp:
  "((bounded_of_mat A) \<otimes> (bounded_of_mat B)) = bounded_of_mat (matrix_tensor A B)"

definition "adjoint_mat M = transpose_mat (map_mat cnj M)"
axiomatization where bounded_of_mat_adjoint:
  "adjoint (bounded_of_mat A) = bounded_of_mat (adjoint_mat A)"

axiomatization where bounded_of_mat_assoc_op: 
  "(assoc_op :: ('a::enum*'b::enum*'c::enum,_) bounded) = bounded_of_mat (one_mat (card_UNIV TYPE('a)*card_UNIV TYPE('b)*card_UNIV TYPE('c)))"

definition "comm_op_mat TYPE('a::enum) TYPE('b::enum) =
  (let da = card_UNIV TYPE('a); db = card_UNIV TYPE('b) in
  mat (da*db) (da*db)
  (\<lambda>(r,c). (if (r div da = c mod da \<and>
                r mod db = c div db) then 1 else 0)))"

axiomatization where bounded_of_mat_comm_op:
  "(comm_op :: ('a::enum*'b::enum,_) bounded) = bounded_of_mat (comm_op_mat TYPE('a) TYPE('b))"

definition "mat_proj_basis_vector (x::'a::enum) = 
  (let n = card_UNIV TYPE('a); i = enum_idx x in 
     mat n n (\<lambda>(r,c). (if r=i \<and> c=i then 1 else 0)))"
axiomatization where bounded_of_mat_proj_basis_vector: 
  "proj (basis_vector x) = bounded_of_mat (mat_proj_basis_vector x)" for x::"'a::enum"

lemmas prepare_matrix_code = 
bounded_of_mat_id bounded_of_mat_timesOp vector_of_vec_applyOp vector_of_vec_basis_vector
bounded_of_mat_X bounded_of_mat_H bounded_of_mat_CNOT bounded_of_mat_assoc_op
bounded_of_mat_tensorOp bounded_of_mat_adjoint bounded_of_mat_assoc_op
bounded_of_mat_proj_basis_vector bounded_of_mat_eq vector_of_vec_eq

section \<open>Matrix computations\<close>

(*

(* Inner product of two vectors (without complex conjugate). Vector is given as a list. *)
fun vector_vector_mult where
  "vector_vector_mult [] [] = 0"
| "vector_vector_mult (x#xs) (y#ys) = (x*y) + vector_vector_mult xs ys"
| "vector_vector_mult _ _ = 0"

(* Multiplication matrix*vector. Matrix is given as a list of rows, rows are lists of scalars. *)
definition [code]: "matrix_vector_mult M x = map (\<lambda>y. vector_vector_mult y x) M"

(* Multiplication matrix*matrix *)
definition [code]: "matrix_matrix_mult A B = transpose (map (matrix_vector_mult A) (transpose B))"

(* i-th basis vector. *)
definition [code]: "vector_basis_vector i = [if x=i then 1 else (0::complex). x<-enum_class.enum]"

definition [code]: "matrix_id TYPE('a::enum) = [vector_basis_vector (x::'a). x <- enum_class.enum]"

definition [code]: "matrix_tensor' (A::complex list list) (B::complex list list) = map (\<lambda>(a, b). map (\<lambda>(x,y). x*y) (List.product a b)) (List.product A B)"
definition [code]: "matrix_adjoint A = transpose (map (map cnj) A)"
definition [code]: "matrix_proj_basis_vector i = [ [if x=i \<and> y=i then (1::complex) else 0. x<-enum_class.enum]. y<-enum_class.enum ]"

(* TODO: is this the identity? *)
definition [code]: "matrix_assoc_op TYPE('a::enum) TYPE('b::enum) TYPE('c::enum) = [ [(if a=a' \<and> b=b' \<and> c=c' then 1 else 0).
        (a::'a,b::'b,c::'c) <- enum_class.enum].
        ((a'::'a,b'::'b),c'::'c) <- enum_class.enum ]"

definition [code]: "matrix_comm_op TYPE('a::enum) TYPE('b::enum) = [ [(if a=a' \<and> b=b' then 1 else 0).
        (a::'a,b::'b) <- enum_class.enum].
        (b'::'b,a'::'a) <- enum_class.enum ]"
*)

subsection \<open>Linking matrices and bounded operators\<close>

(*
axiomatization matrix :: "('a::enum,'b::enum) bounded \<Rightarrow> complex list list" and
               vector :: "('a::enum) vector \<Rightarrow> complex list" 
axiomatization where
    vector_applyOp: "vector (A \<cdot> \<psi>) = matrix_vector_mult (matrix A) (vector \<psi>)"
and matrix_timesOp: "matrix (A \<cdot> B) = matrix_matrix_mult (matrix A) (matrix B)"
for A :: "('a::enum,'b::enum) bounded"
and B :: "('c::enum, 'a::enum) bounded"
and \<psi> :: "'a vector"

axiomatization where vector_eq: "vector \<psi> = vector \<phi> \<Longrightarrow> \<psi> = \<phi>" for \<psi> :: "'a::enum vector"
axiomatization where matrix_eq: "matrix A = matrix B \<Longrightarrow> A = B" for A :: "('a::enum,'b::enum) bounded"

axiomatization where vector_basis_vector: "vector (basis_vector i) = vector_basis_vector i" for i::"'a::enum"

definition [code]: "matrix_X = [ [0::complex,1], [1,0] ]"
axiomatization where X_matrix: "matrix X = matrix_X"
definition [code]: "matrix_H = [ [1/sqrt 2::complex, 1/sqrt 2], [1/sqrt 2, -1/sqrt 2] ]"
axiomatization where H_matrix: "matrix H = matrix_H"
definition [code]: "matrix_CNOT = [ [1::complex,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0] ]"
axiomatization where CNOT_matrix: "matrix CNOT = matrix_CNOT"
axiomatization where matrix_idOp: "matrix (idOp::('a::enum,_)bounded) = matrix_id TYPE('a)"


axiomatization where matrix_tensorOp: "matrix (tensorOp A B) = matrix_tensor' (matrix A) (matrix B)"
  for A :: "('a::enum,'b::enum) bounded" and  B :: "('c::enum,'d::enum) bounded"

axiomatization where matrix_adjoint: "matrix (A* ) = matrix_adjoint (matrix A)"
  for A :: "('a::enum,'b::enum) bounded" 
 


axiomatization where matrix_assoc_op: 
  "matrix (assoc_op :: ('a::enum*'b::enum*'c::enum,_) bounded) = matrix_assoc_op TYPE('a) TYPE('b) TYPE('c)"
  


axiomatization where matrix_comm_op: 
  "matrix (comm_op :: ('a::enum*'b::enum,_) bounded) = matrix_comm_op TYPE('a) TYPE('b)"
 

axiomatization where matrix_proj_basis_vector: "matrix (proj (basis_vector i)) = matrix_proj_basis_vector i" for i::"'a::enum"

(* TODO: some simplification rules that simplify simple cases (e.g., matrix_matrix_mult matrix_id x) *)

lemmas prepare_matrix_code = X_matrix H_matrix CNOT_matrix matrix_timesOp vector_basis_vector 
vector_applyOp matrix_idOp matrix_tensorOp matrix_adjoint matrix_assoc_op matrix_comm_op matrix_proj_basis_vector
*)


section "Experiments"



lemma fix_mat_rm: "fix_mat M = M" sorry

lemma "X \<cdot> X = idOp"
  unfolding prepare_matrix_code
  (* apply (simp add: matrix_matrix_mult_def matrix_vector_mult_def vector_basis_vector X_matrix matrix_idOp enum_bit_def) *)
  by eval

lemma "X \<cdot> basis_vector 0 = basis_vector 1"
  unfolding prepare_matrix_code
  unfolding fix_mat_rm
  by eval

lemma "CNOT \<cdot> basis_vector (a,b) = basis_vector (a,a+b)"
  unfolding prepare_matrix_code
  apply (rule spec[of _ a])
  apply (rule spec[of _ b])
  by eval


lemma "(tensorOp CNOT X) \<cdot> basis_vector ((a,b),c) = basis_vector ((a,a+b),1+c)"
  unfolding prepare_matrix_code 
  (* apply (simp add: vector_basis_vector matrix_vector_mult_def CNOT_matrix enum_bit_def enum_prod_def matrix_tensor'_def matrix_tensorOp X_matrix) *)
  apply (cases a; hypsubst_thin) apply (cases b; hypsubst_thin) apply (cases c; hypsubst_thin)
  apply simp     apply code_simp

  (* apply (rule spec[where x=a]) *)
  apply (rule spec[where x=b])
  apply (rule spec[where x=c])
  apply xcode_simp
  done (* TODO fix *)

lemma tensor_lift:
  assumes "colocal R Q"
  shows "A\<guillemotright>Q = (idOp\<otimes>A)\<guillemotright>qvariable_concat R Q" sorry

lemma lift_swap:
  assumes "colocal Q R"
  shows "A \<guillemotright> qvariable_concat Q R = (comm_op \<cdot> A \<cdot> comm_op) \<guillemotright> qvariable_concat R Q"
  sorry

lemma lift_assoc:
  fixes A :: "(('a*'b)*'c,_) bounded"
  assumes "colocal Q R" and "colocal Q S" and "colocal S R"
  shows "A \<guillemotright> qvariable_concat (qvariable_concat Q R) S = (assoc_op* \<cdot> A \<cdot> assoc_op) \<guillemotright> qvariable_concat Q (qvariable_concat R S)"
  sorry

lemma times_lift:
  fixes B :: "('a,'a) bounded"
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
  fixes A :: "('a,'b)bounded"
    and B :: "('c,'d)bounded"
  shows "V \<cdot> (A\<otimes>B) \<cdot> (C\<otimes>D) = V \<cdot> (A\<cdot>C) \<otimes> (B\<cdot>D)"
  sorry

lemma comm_op_tensor: "comm_op \<cdot> (A \<otimes> B) = (B \<otimes> A) \<cdot> comm_op" 
  sorry


(* value "matrix (assoc_op* \<cdot> CNOT \<otimes> X \<cdot> assoc_op \<cdot> proj (basis_vector (a, b, c)))" *)

(* lemmas prepare_code = matrix_adjoint *)

(* lemma matrix_classical_operator: "matrix (classical_operator f) = undefined" sorry *)

value "matrix_vector_mult matrix_CNOT (vector_basis_vector (0::bit,0::bit))"

value "(matrix_matrix_mult
              (matrix_matrix_mult 
(matrix_adjoint (matrix_assoc_op TYPE(bit) TYPE(bit) TYPE(bit)))
(matrix_tensor' matrix_CNOT matrix_X))
              (matrix_assoc_op TYPE(bit) TYPE(bit) TYPE(bit)))"

value "
            (matrix_proj_basis_vector (0::bit, 0::bit, 0::bit))"

value "
 (matrix_matrix_mult
[ [Complex 0 0, Complex 1 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 1 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 1 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 1 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 1 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 1 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 1 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 1 0, Complex 0 0, Complex 0 0, Complex 0 0] ]

[ [Complex 1 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0] ]
)
"


value "(vector_basis_vector (0::bit, 0::bit, 0::bit))"

(* definition [code]: "matrix_vector_mult M x = map (\<lambda>y. vector_vector_mult y x) M" *)

value  "matrix_vector_mult
         [ [Complex 0 0, Complex 1 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0],
  [Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0] ]

          [Complex 1 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0, Complex 0 0]
          "

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
  apply (rule matrix_eq)

     apply (simp only: prepare_matrix_code)
  apply (rule spec[of _ a])
  apply (rule spec[of _ b])
  apply (rule spec[of _ c])
  by eval
*)



end