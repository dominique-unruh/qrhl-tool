theory Real_Sqrt2
  imports Complex_Main
begin

definition [code del]: "(REAL_SQRT2 a b :: real) = of_rat a + of_rat b * sqrt 2" for a b :: rat
code_datatype REAL_SQRT2

lemmas [code del] = real_times_code real_plus_code one_real_code root_def real_equal_code
real_less_eq_code real_less_code real_minus_code real_inverse_code
real_divide_code real_uminus_code
(* not reimplemented: *) 
real_floor_code 

lemma [code_abbrev del]:
  "real_of_rat (numeral k) = numeral k"
  "real_of_rat (- numeral k) = - numeral k"
  "real_of_rat (rat_of_int a) = real_of_int a"
  by simp_all

lemma sqrt_2_sq: "sqrt 2 * sqrt 2 = 2" by simp

lemma REAL_SQRT2_times [code]: "REAL_SQRT2 a b * REAL_SQRT2 c d == REAL_SQRT2 (a*c+2*b*d) (a*d+b*c)"
  unfolding REAL_SQRT2_def of_rat_mult of_rat_add 
  using sqrt_2_sq apply auto sorry

lemma REAL_SQRT2_equal [code]: "HOL.equal (REAL_SQRT2 a b) (REAL_SQRT2 c d) \<longleftrightarrow> HOL.equal a c \<and> HOL.equal b d"
  sorry

definition [code del]: "is_nonnegative_real (x::real) = (x\<ge>0)"

lemma REAL_SQRT2_uminus [code]: "- (REAL_SQRT2 a b) = REAL_SQRT2 (-a) (-b)"
  unfolding REAL_SQRT2_def of_rat_minus by simp

lemma REAL_SQRT2_is_nonnegative [code]: "is_nonnegative_real (REAL_SQRT2 a b) =
  (if a\<ge>0 then (if b\<ge>0 then True else a*a \<ge> 2*b*b)
           else (if b\<ge>0 then a*a \<le> 2*b*b else False))"
  sorry

lemma REAL_SQRT2_inverse [code]: "inverse (REAL_SQRT2 a b) = (let x = inverse (a*a-2*b*b) in REAL_SQRT2 (a*x) (-b*x))"
  sorry

lemma REAL_SQRT2_plus [code]: "REAL_SQRT2 a b + REAL_SQRT2 c d == REAL_SQRT2 (a+c) (b+d)"
  unfolding REAL_SQRT2_def of_rat_add by algebra
lemma REAL_SQRT2_minus [code]: "REAL_SQRT2 a b - REAL_SQRT2 c d == REAL_SQRT2 (a-c) (b-d)"
  unfolding REAL_SQRT2_def of_rat_minus sorry
lemma REAL_SQRT2_numeral [symmetric, code_abbrev]: "(numeral k :: real) = REAL_SQRT2 (numeral k) 0"
  unfolding REAL_SQRT2_def sorry
lemma REAL_SQRT2_uminus_numeral [symmetric, code_abbrev]: "- (numeral k :: real) = REAL_SQRT2 (- numeral k) 0"
  unfolding REAL_SQRT2_def sorry
lemma REAL_SQRT2_rat_of_int [code_abbrev]: "REAL_SQRT2 (rat_of_int a) 0 = rat_of_int a"
  unfolding REAL_SQRT2_def sorry
lemma REAL_SQRT2_one [code]: "(1 :: real) = REAL_SQRT2 1 0"
  unfolding REAL_SQRT2_def sorry
lemma REAL_SQRT2_zero [code]: "0 = REAL_SQRT2 0 0"
  unfolding REAL_SQRT2_def sorry
lemma REAL_SQRT2_sqrt2 [code]: "sqrt a = 
  (if a=2 then REAL_SQRT2 0 1 
   else if a=1 then 1
   else if a=0 then 0
   else if a=4 then 2
   else Code.abort (STR ''sqrt only implemented on 0,1,2,4'') (\<lambda>_. sqrt a))"
  unfolding REAL_SQRT2_def by auto
lemma REAL_SQRT2_less_eq [code]: "a \<le> b \<longleftrightarrow> is_nonnegative_real (b-a)" for a b :: real
  unfolding is_nonnegative_real_def by simp
lemma REAL_SQRT2_less [code]: "a < b \<longleftrightarrow> a\<noteq>b \<and> a \<le> b" for a b :: real
  by auto
lemma REAL_SQRT2_divide [code]: "a / b = a * inverse b" for a b :: real
  by (rule divide_inverse)



end
