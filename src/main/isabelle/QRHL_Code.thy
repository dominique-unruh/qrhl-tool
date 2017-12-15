theory QRHL_Code
  imports QRHL "Jordan_Normal_Form.Matrix_Impl"
begin

hide_const (open) Lattice.sup
hide_const (open) Lattice.inf
hide_const (open) Order.top
hide_const (open) card_UNIV

(* TODO move *)
axiomatization plusOp :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded"
axiomatization uminusOp :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded"
instantiation bounded :: (type,type) ab_group_add begin
definition "op+ = plusOp" 
definition "A - B = plusOp A (uminusOp B)"
definition "uminus = uminusOp"
instance apply intro_classes sorry
end

axiomatization bounded_of_mat :: "complex mat \<Rightarrow> ('a::enum,'b::enum) bounded"
  and mat_of_bounded :: "('a::enum,'b::enum) bounded \<Rightarrow> complex mat"
axiomatization vector_of_vec :: "complex vec \<Rightarrow> ('a::enum) vector"
  and vec_of_vector :: "('a::enum) vector \<Rightarrow> complex vec"

lemma [code abstype]:
  "bounded_of_mat (mat_of_bounded B) = B"
  sorry
lemma [code abstype]:
  "vector_of_vec (vec_of_vector B) = B"
  sorry

fun index_of where
  "index_of x [] = (0::nat)"
| "index_of x (y#ys) = (if x=y then 0 else (index_of x ys + 1))"

definition "enum_idx (x::'a::enum) = index_of x (enum_class.enum :: 'a list)"
definition "enum_len (TYPE('a::enum)) = length (enum_class.enum :: 'a list)"

definition [code del]: "simplify_matrix x = (x::complex mat)"
definition [code del]: "simplify_vector x = (x::complex vec)"

axiomatization where bounded_of_mat_id[code]:
  "mat_of_bounded (idOp :: ('a::enum,'a) bounded) = one_mat (enum_len TYPE('a))"
axiomatization where bounded_of_mat_timesOp[code]:
  "mat_of_bounded (M \<cdot> N) = simplify_matrix (mat_of_bounded M * mat_of_bounded N)" for M::"('b::enum,'c::enum) bounded" and N::"('a::enum,'b) bounded"
axiomatization where bounded_of_mat_plusOp[code]:
  "mat_of_bounded (M + N) = simplify_matrix (mat_of_bounded M + mat_of_bounded N)" for M::"('a::enum,'b::enum) bounded" and N::"('a::enum,'b) bounded"
axiomatization where bounded_of_mat_uminusOp[code]:
  "mat_of_bounded (- M) = - mat_of_bounded M" for M::"('a::enum,'b::enum) bounded"
axiomatization where vector_of_vec_applyOp[code]:
  "vec_of_vector (M \<cdot> x) = simplify_vector (mult_mat_vec (mat_of_bounded M) (vec_of_vector x))"


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
definition "matrix_H = mat_of_rows_list 2 [ [1/sqrt 2::complex, 1/sqrt 2], [1/sqrt 2, -1/sqrt 2] ]"
axiomatization where bounded_of_mat_H[code]: "mat_of_bounded H = matrix_H"
definition "matrix_CNOT = mat_of_rows_list 4 [ [1::complex,0,0,0], [0,1,0,0], [0,0,0,1], [0,0,1,0] ]"
axiomatization where bounded_of_mat_CNOT[code]: "mat_of_bounded CNOT = matrix_CNOT"

definition "matrix_tensor (A::'a::times mat) (B::'a mat) =
  mat (dim_row A*dim_row B) (dim_col A*dim_col B) 
  (\<lambda>(r,c). A $$ (r div dim_row A, c div dim_col A) *
           B $$ (r mod dim_row B, c mod dim_col B))"

axiomatization where bounded_of_mat_tensorOp[code]:
  "mat_of_bounded (tensorOp A B) = matrix_tensor (mat_of_bounded A) (mat_of_bounded B)"

definition "adjoint_mat M = transpose_mat (map_mat cnj M)"
axiomatization where bounded_of_mat_adjoint[code]:
  "mat_of_bounded (adjoint A) = adjoint_mat (mat_of_bounded A)"

axiomatization where bounded_of_mat_assoc_op[code]: 
  "mat_of_bounded (assoc_op :: ('a::enum*'b::enum*'c::enum,_) bounded) = one_mat (Enum.card_UNIV TYPE('a)*Enum.card_UNIV TYPE('b)*Enum.card_UNIV TYPE('c))"

definition "comm_op_mat TYPE('a::enum) TYPE('b::enum) =
  (let da = Enum.card_UNIV TYPE('a); db = Enum.card_UNIV TYPE('b) in
  mat (da*db) (da*db)
  (\<lambda>(r,c). (if (r div da = c mod da \<and>
                r mod db = c div db) then 1 else 0)))"

axiomatization where bounded_of_mat_comm_op[code]:
  "mat_of_bounded (comm_op :: ('a::enum*'b::enum,_) bounded) = comm_op_mat TYPE('a) TYPE('b)"

axiomatization where vec_of_vector_zero[code]:
  "vec_of_vector (0::'a::enum vector) = zero_vec (enum_len TYPE('a))"

(* definition "mat_proj_basis_vector (x::'a::enum) = 
  (let n = Enum.card_UNIV TYPE('a); i = enum_idx x in 
     mat n n (\<lambda>(r,c). (if r=i \<and> c=i then 1 else 0)))"
axiomatization where bounded_of_mat_proj_basis_vector[code]: 
  "mat_of_bounded (proj (basis_vector x)) = mat_proj_basis_vector x" for x::"'a::enum" *)

(* (* TODO move *)
axiomatization norm2 :: "'a vector \<Rightarrow> real"

axiomatization where norm2[code]: "norm2 \<psi> = cscalar_prod (vec_of_vector \<psi>) (vec_of_vector \<psi>)" 
 *)

axiomatization where mat_of_bounded_proj[code]:
  "mat_of_bounded (proj \<psi>) = 
    (let v = vec_of_vector \<psi>; d = dim_vec v in
    if \<psi>=0 then zero_mat d d else
          smult_mat (1/(cscalar_prod v v)) (mat_of_cols d [v] * mat_of_rows d [v]))"

axiomatization where vec_of_vector_basis_vector[code]:
  "vec_of_vector (basis_vector i) = unit_vec (enum_len TYPE('a)) (enum_idx i)" for i::"'a::enum"

(* lemmas prepare_matrix_code = 
bounded_of_mat_id bounded_of_mat_timesOp vector_of_vec_applyOp vector_of_vec_basis_vector
bounded_of_mat_X bounded_of_mat_H bounded_of_mat_CNOT bounded_of_mat_assoc_op
bounded_of_mat_tensorOp bounded_of_mat_adjoint bounded_of_mat_assoc_op
bounded_of_mat_proj_basis_vector bounded_of_mat_eq vector_of_vec_eq
 *)

term "f sums s \<longleftrightarrow> (\<lambda>n. \<Sum>i<n. f i) \<longlonglongrightarrow> s"

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

instantiation bit :: finite_UNIV begin
definition "finite_UNIV_bit = Phantom(bit) True"
instance apply intro_classes unfolding finite_UNIV_bit_def by simp
end

axiomatization where mat_of_bounded_zero[code]:
  "mat_of_bounded (0::('a::enum,'b::enum) bounded) = zero_mat (enum_len TYPE('b)) (enum_len TYPE('a))"

find_theorems set_fold_cfc

axiomatization sqrt2 :: complex

derive (eq) ceq real
derive (no) ccompare real
derive (eq) ceq complex
derive (no) ccompare complex

definition "two = (2::complex)"

datatype real' = Plus rat "real' list" | ErrorReal real


(* definition[code del]: "Sqrt = sqrt" *)
fun Real' where
  Real': "Real' (Plus (r::rat) (x::real' list)) = foldl (\<lambda> x y. x+sqrt(Real' y)) (Ratreal r) x"
(* definition[code del]: "Uminus = (uminus :: real \<Rightarrow> _)" *)
(* definition [code del]: "ErrorReal x = (x::real)" *)
(* declare to_real_Plus[code del] *)
code_datatype Real' Ratreal 

definition "real'_of_rat r = Plus r []"

instantiation real' :: plus begin
fun plus_real' where "(Plus r xs) + (Plus r' xs') = Plus (r+r') (xs @ xs')"
instance ..
end


fun real'_sort_key  where
  "real'_sort_key (Plus a []) = (if a=0 then 0 else 1)"
| "real'_sort_key (Plus a (_#_)) = (2::nat)"
| "real'_sort_key (ErrorReal x) = 3"

fun simplify_real' and simplify_real'0 and simplify_real'1 where
  "simplify_real' (Plus a xs) = simplify_real'0 (Plus a (sort_key real'_sort_key (map simplify_real' xs)))"
| "simplify_real' (ErrorReal a) = ErrorReal a"

| "simplify_real'0 (Plus a (Plus b [] # xs)) = 
     (if b=0 then simplify_real'0 (Plus a xs)
      else simplify_real'1 (Plus a (Plus b [] # xs)))"
| "simplify_real'0 x = simplify_real'1 x"

| "simplify_real'1 x = x"

lemma size_list_sort_key: "size_list f (sort_key k l) = size_list f l" for f k l sorry

(*
lemma "size (simplify_real' x) \<le> size x \<and> size (simplify_real'0 x) \<le> size x \<and> size (simplify_real'1 x) \<le> size x"
proof (induction "size x"  arbitrary:x rule:nat_less_induct)
  case 1
  then have size: "size (simplify_real' y) \<le> size y"
    and size0: "size (simplify_real'0 y) \<le> size y"
    and size1: "size (simplify_real'1 y) \<le> size y"
    if "size y < size x" for y 
    using that by auto

  have "size (simplify_real'1 x) \<le> size x" by simp
  moreover
  consider (a0) a xs where "x=Plus a (Plus 0 [] # xs)"
    | (ab) a b xs where "x=Plus a (Plus b [] # xs)" and "b\<noteq>0"
    | (else) "simplify_real'0 x = x"
    sorry
  then have "size (simplify_real'0 x) \<le> size x"
  proof (cases)
    case a0
    then show ?thesis apply simp
      using size0
      by (metis (no_types, lifting) add.commute add.right_neutral add_Suc le_SucI lessI less_SucI list.size(2) list.size_gen(1) real'.size(3))
  next
    case ab
    then show ?thesis by auto
  next
    case else
    then show ?thesis by auto
  qed
  moreover 
  {fix a xs
    have "size (Plus a (sort_key real'_sort_key (map simplify_real' xs))) \<le> 
        size (Plus a (map simplify_real' xs))"
      by (simp add: size_list_sort_key)
    also
    have "\<dots> \<le> Suc (size_list size xs)" apply simp
    

      by
    size (simplify_real'0 (Plus a ((map simplify_real' xs))))" 
    apply simp

    find_theorems size_list insort_key
    by
"\<le> Suc (size_list size xs)"
  have "size (simplify_real'0 (Plus a (sort_key real'_sort_key (map simplify_real' xs)))) \<le> Suc (size_list size xs)"
  have "size (simplify_real' x) \<le> size x"
    apply (cases x, hypsubst_thin, auto)
    sorry
  ultimately show ?case by simp
qed
  apply (induction x and y)
  apply auto
*)

definition "exception f = f ()"
declare[[code abort: exception]]

fun rat_times_real' where
  "rat_times_real' r (Plus r' xs) = Plus (r*r') (map (rat_times_real' (r*r)) xs)"

instantiation real' :: times begin
fun times_real' where 
"(Plus r xs) * (Plus r' xs') = 
  Plus (r*r') []
  +
  (rat_times_real' r (Plus 0 xs'))
  +
  (rat_times_real' r' (Plus 0 xs))
  +
  (Plus 0 (map (\<lambda>(x,y). x*y) (List.product xs xs')))"
| "a*b = ErrorReal (Real' a * Real' b)"
instance..
end

definition "simplify_real'_sized x = (let y = simplify_real' x in if size y \<le> size x then y else x)"
lemma simplify_real'_sized_size: "size (simplify_real'_sized x) \<le> size x"
  unfolding simplify_real'_sized_def
  by (metis order_refl) 

instantiation real' :: inverse begin
function (sequential) inverse_real'0 and inverse_real' where
  "inverse_real'0 (Plus a []) = Plus (inverse a) []"
| "inverse_real'0 (Plus a [r]) = (if a=0 then Plus 0 [inverse r] else
        exception (%_. ErrorReal (inverse (Real' (Plus a [r])))))"
| "inverse_real' x = inverse_real'0 ( simplify_real'_sized x)"
  by pat_completeness auto
termination apply (relation "case_sum size size <*mlex*> case_sum (\<lambda>x. 0) (\<lambda>x. Suc 0) <*mlex*> {}")
    apply auto
  apply (simp add: wf_mlex)
   apply (simp add: mlex_less)
  by (simp add: simplify_real'_sized_size mlex_leq mlex_less)

definition "divide_real' (a::real') b = a * inverse b"
instance..
end

instantiation real' :: uminus begin
fun uminus_real' where
  "uminus_real' (Plus a xs) = Plus (-a) (map uminus_real' xs)"
| "uminus_real' (ErrorReal a) = ErrorReal (-a)"
instance..
end

typ rat

instantiation real' :: minus begin
definition "minus_real' a b = a + (uminus_real'_inst.uminus_real' b)"
instance..
end

lemma [code]: "sqrt (Real' x) = Real' (Plus 0 [x])" by simp
lemma [code]: 
  "Real' a * Real' b = Real' (a*b)"
  "Ratreal a' * Real' b = Real' (real'_of_rat a' * b)"
  "Real' a * Ratreal b' = Real' (a * real'_of_rat b')"
  sorry

lemma [code]: 
  "Real' a + Real' b = Real' (a+b)"
  "Ratreal a' + Real' b = Real' (real'_of_rat a' + b)"
  "Real' a + Ratreal b' = Real' (a + real'_of_rat b')"
  sorry

lemma [code]: 
  "Real' a / Real' b = Real' (a/b)"
  "Ratreal a' / Real' b = Real' (real'_of_rat a' / b)"
  "Real' a / Ratreal b' = Real' (a / real'_of_rat b')"
  sorry

lemma [code]: 
  "Real' a - Real' b = Real' (a-b)"
  "Ratreal a' - Real' b = Real' (real'_of_rat a' - b)"
  "Real' a - Ratreal b' = Real' (a - real'_of_rat b')"
  sorry

lemma [code]:
  "sqrt (Ratreal a) = sqrt (Real' (Plus a []))"
  "sqrt (Real' x) = Real' (Plus 0 [x])"
  sorry

definition "tmp = 1/sqrt 2"
value [code] "1/tmp"


export_code "op/ :: real\<Rightarrow>_\<Rightarrow>_" in Haskell 

(* print_codesetup *)

lemma Real'_simplify_real': "Real' (simplify_real' x) = Real' x"
  sorry

definition [code del]: "simplify_real x = (x::real)"
lemma[code]: 
"simplify_real (Ratreal x) = Ratreal x"
"simplify_real (Real' y) = (case simplify_real' y of Plus a [] \<Rightarrow> Ratreal a | z \<Rightarrow> Real' z)"
  sorry

(* declare Real'[code_post] *)

lemma [code_post]:
  "Real' (Plus a (x#xs)) = Real' (Plus a xs) + sqrt(Real' x)"
  "Real' (Plus a []) = Ratreal a"
  "0 + y = y"
  sorry

definition "simplify_complex (x::complex) = x"
lemma [code]: "simplify_vector v = map_vec simplify_complex v" 
  unfolding simplify_complex_def simplify_vector_def by auto 
lemma [code]: "simplify_matrix v = map_mat simplify_complex v"  
  unfolding simplify_complex_def simplify_matrix_def by auto 
lemma [code]: "simplify_complex (Complex a b) = Complex (simplify_real a) (simplify_real b)"
  unfolding simplify_complex_def simplify_real_def by simp

  (* value "simplify_real (Real' (Plus 2 []))" *)
  (* value "Real' (Plus 1 [Plus 2 []])" *)
(* lemma "x=(Plus 0 [Plus 1 []]) * (Plus 0 [Plus (1 / 2) []])" *)
(* value [nbe] "simplify_real (Real' ((Plus 0 [Plus 1 []]) * (Plus 0 [Plus (1 / 2) []])))" *)
(* value [nbe] "simplify_real ( sqrt(1)/sqrt 2 )" *)
(* value [nbe] "simplify_real ( sqrt(1)/sqrt 2 )" *)
(* value "sqrt (1 / 2) - 0 + 0" *)

value [nbe] "basis_vector (0::bit)"
  value [code] "(H \<cdot> basis_vector (0::bit))"

  value "simplify_real (sqrt 0 + sqrt 0 + sqrt 0 + sqrt (1 / 2))"
  value "simplify_real (sqrt (1 / 2) + sqrt 0 + sqrt 0 + sqrt 0)"

  value [nbe] "proj (H \<cdot> basis_vector (0::bit))"

value [nbe] "mat_of_rows_list 2 [ [1/sqrt 2::complex, 1/sqrt 2], [1/sqrt 2, -1/sqrt 2] ]"

value [nbe] "matrix_H"


vaxlue [nbe] "proj (H \<cdot> basis_vector (0::bit)) + proj (H \<cdot> basis_vector 1) = idOp"

value [nbe] "sum (\<lambda>i::bit. proj (basis_vector i)) (set enum_class.enum) = idOp"


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