theory Real_Sqrt2
  imports Complex_Main "HOL-ex.Sqrt" "HOL-Library.Rewrite"
begin

definition [code del]: "(REAL_SQRT2 a b :: real) = of_rat a + of_rat b * sqrt 2" for a b :: rat
code_datatype REAL_SQRT2

lemmas [code del] = real_times_code real_plus_code one_real_code root_def real_equal_code
real_less_eq_code real_less_code real_minus_code real_inverse_code
real_divide_code real_uminus_code zero_real_code
(* not reimplemented: *) 
real_floor_code 

lemma [code_abbrev del]:
  "real_of_rat (numeral k) = numeral k"
  "real_of_rat (- numeral k) = - numeral k"
  "real_of_rat (rat_of_int a) = real_of_int a"
  by simp_all

lemma sqrt_2_sq: "sqrt 2 * sqrt 2 = 2" by simp

lemma REAL_SQRT2_times [code]: "REAL_SQRT2 a b * REAL_SQRT2 c d = REAL_SQRT2 (a*c+2*b*d) (a*d+b*c)"
  (* apply (rule eq_reflection) *)
  unfolding REAL_SQRT2_def of_rat_mult of_rat_add ring_distribs
  using sqrt_2_sq by auto


lemma REAL_SQRT2_equal [code]: "HOL.equal (REAL_SQRT2 a b) (REAL_SQRT2 c d) \<longleftrightarrow> HOL.equal a c \<and> HOL.equal b d"
proof (unfold equal, rule iffI[rotated], simp, rule ccontr)
  define aa bb cc dd where "aa = real_of_rat a" and "bb = real_of_rat b" and "cc = real_of_rat c" and "dd = real_of_rat d"
  note defs = this
  assume "REAL_SQRT2 a b = REAL_SQRT2 c d"
  then have aa_cc: "aa-cc = (dd-bb) * sqrt 2"
    unfolding REAL_SQRT2_def defs[symmetric] by algebra
  assume "\<not> (a=c \<and> b=d)"
  with aa_cc have "(aa-cc)/(dd-bb) = sqrt 2"
    unfolding defs by auto
  also have "(aa-cc)/(dd-bb) = real_of_rat ((a-c)/(d-b))"
    unfolding defs of_rat_divide of_rat_diff by simp 
  finally have "sqrt 2 \<in> \<rat>"
    using Rats_of_rat by metis
  with sqrt_2_not_rat show False by simp
qed

definition [code del]: "is_nonnegative_real (x::real) = (x\<ge>0)"

lemma REAL_SQRT2_uminus [code]: "- (REAL_SQRT2 a b) = REAL_SQRT2 (-a) (-b)"
  unfolding REAL_SQRT2_def of_rat_minus by simp

lemma REAL_SQRT2_is_nonnegative [code]: "is_nonnegative_real (REAL_SQRT2 a b) =
  (if a\<ge>0 then (if b\<ge>0 then True else a*a \<ge> 2*b*b)
           else (if b\<ge>0 then a*a \<le> 2*b*b else False))"
proof -
  define aa bb where "aa = real_of_rat a" and "bb = real_of_rat b"
  note defs = this
  have 1: "(0 \<le> aa + bb * sqrt 2) \<longleftrightarrow> (2 * bb * bb \<le> aa * aa)" if "0 \<le> aa" and "\<not> 0 \<le> bb"
  proof -
    have "0 \<le> aa + bb * sqrt 2 \<longleftrightarrow> (-bb) * sqrt 2 \<le> aa"
      by auto
    also have "\<dots> \<longleftrightarrow> ((-bb) * sqrt 2)\<^sup>2 \<le> aa^2"
      apply (subst abs_le_square_iff[symmetric])
      using that by (auto simp: mult_nonneg_nonpos2)
    also have "\<dots> \<longleftrightarrow> 2 * bb * bb \<le> aa * aa"
      by (simp add: power2_eq_square mult.commute mult.left_commute sqrt_2_sq) 
    finally show ?thesis by assumption
  qed
  have 2: "(0 \<le> aa + bb * sqrt 2) = (aa * aa \<le> 2 * bb * bb)" if "\<not> 0 \<le> aa" and "0 \<le> bb"
  proof -
    have "0 \<le> aa + bb * sqrt 2 \<longleftrightarrow> -aa \<le> bb * sqrt 2"
      by auto
    also have "\<dots> \<longleftrightarrow> aa\<^sup>2 \<le> (bb * sqrt 2)\<^sup>2"
      apply (subst abs_le_square_iff[symmetric])
      using that by (auto simp: mult_nonneg_nonpos2)
    also have "\<dots> \<longleftrightarrow> aa * aa \<le> 2 * bb * bb"
      by (simp add: power2_eq_square mult.commute mult.left_commute sqrt_2_sq) 
    finally show ?thesis by assumption
  qed
  have 3: "\<not> 0 \<le> aa + bb * sqrt 2" if "\<not> 0 \<le> aa" and "\<not> 0 \<le> bb"
    using that
    by (metis add.left_neutral add_mono_thms_linordered_field(5) not_less not_numeral_le_zero real_sqrt_le_0_iff zero_le_mult_iff) 

  show ?thesis
    unfolding is_nonnegative_real_def REAL_SQRT2_def defs[symmetric]
      of_rat_less_eq[where ?'a=real, symmetric] of_rat_mult of_rat_0
      of_rat_numeral_eq
    apply (cases "aa\<ge>0"; cases "bb\<ge>0")
    using 1 2 3 by simp_all
qed

lemma Rats_abs_real [simp]: "a \<in> \<rat> \<Longrightarrow> abs a \<in> \<rat>" for a :: real
  by (cases "a\<ge>0", auto)

lemma REAL_SQRT2_inverse [code]: "inverse (REAL_SQRT2 a b) = (let x = inverse (a*a-2*b*b) in REAL_SQRT2 (a*x) (-b*x))" (is "?lhs = ?rhs")
proof (cases "a=0 \<and> b=0")
  case True
  then show ?thesis by (simp add: REAL_SQRT2_def)
next
  case False
  define aa bb lhs rhs where "aa = real_of_rat a" and "bb = real_of_rat b"
    and "lhs = ?lhs" and "rhs = ?rhs"
  note defs = this
  from False have nonzero: "aa \<noteq> 0 \<or> bb \<noteq> 0" unfolding defs by simp
  have neq0: "aa * aa - 2 * bb * bb \<noteq> 0"
  proof (cases "bb=0")
    case True
    with nonzero show ?thesis by simp
  next
    case False 
    { assume "aa * aa - 2 * bb * bb = 0"
      with False have "(aa/bb)^2 = 2" unfolding power2_eq_square by simp
      then have "abs (aa/bb) = sqrt 2"
        by (metis real_sqrt_abs)
      moreover have "abs (aa/bb) \<in> \<rat>" unfolding aa_def bb_def 
        by auto
      ultimately have False
        using sqrt_2_not_rat by auto }
    then show ?thesis by auto
  qed
  have rhs2: "rhs = inverse (aa*aa-2*bb*bb) * REAL_SQRT2 a (-b)"
    unfolding rhs_def Let_def REAL_SQRT2_def of_rat_mult of_rat_inverse of_rat_diff of_rat_minus of_rat_numeral_eq defs[symmetric]
    by algebra
  have "rhs * (REAL_SQRT2 a b) = inverse (aa*aa-2*bb*bb) * (aa*aa-2*bb*bb)"
    unfolding rhs2
    apply (simp add: mult.assoc REAL_SQRT2_times)
    unfolding REAL_SQRT2_def of_rat_mult of_rat_inverse of_rat_diff of_rat_minus of_rat_numeral_eq defs[symmetric]
    by simp
  also have "inverse (aa*aa-2*bb*bb) * (aa*aa-2*bb*bb) = 1"
    using neq0 by (rule field_class.field_inverse)
  finally have "rhs * (REAL_SQRT2 a b) = 1" by assumption
  then have "rhs = inverse (REAL_SQRT2 a b)"
    using inverse_eq_iff_eq inverse_unique by fastforce
  then show ?thesis 
    unfolding rhs_def by simp
qed

lemma REAL_SQRT2_plus [code]: "REAL_SQRT2 a b + REAL_SQRT2 c d == REAL_SQRT2 (a+c) (b+d)"
  unfolding REAL_SQRT2_def of_rat_add by algebra
lemma REAL_SQRT2_minus [code]: "REAL_SQRT2 a b - REAL_SQRT2 c d == REAL_SQRT2 (a-c) (b-d)"
  unfolding REAL_SQRT2_def of_rat_diff by algebra
lemma REAL_SQRT2_numeral [symmetric, code_abbrev]: "(numeral k :: real) = REAL_SQRT2 (numeral k) 0"
  unfolding REAL_SQRT2_def by auto
lemma REAL_SQRT2_uminus_numeral [symmetric, code_abbrev]: "- (numeral k :: real) = REAL_SQRT2 (- numeral k) 0"
  by (metis REAL_SQRT2_numeral REAL_SQRT2_uminus add.inverse_neutral)
lemma REAL_SQRT2_rat_of_int [code_abbrev]: "REAL_SQRT2 (rat_of_int a) 0 = rat_of_int a"
  unfolding REAL_SQRT2_def by simp
lemma REAL_SQRT2_one [code]: "(1 :: real) = REAL_SQRT2 1 0"
  unfolding REAL_SQRT2_def by simp
lemma REAL_SQRT2_zero [code]: "0 = REAL_SQRT2 0 0"
  unfolding REAL_SQRT2_def by simp
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
