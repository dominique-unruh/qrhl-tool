section \<open>Inner Product Spaces and the Gradient Derivative\<close>

theory Complex_Inner_Product
imports Complex_Main Complex_Vector_Spaces "HOL-Analysis.Inner_Product"
begin

subsection \<open>Complex inner product spaces\<close>

text \<open>
  Temporarily relax type constraints for \<^term>\<open>open\<close>, \<^term>\<open>uniformity\<close>,
  \<^term>\<open>dist\<close>, and \<^term>\<open>norm\<close>.
\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::open set \<Rightarrow> bool\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::dist \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniformity \<times> 'a) filter\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::norm \<Rightarrow> real\<close>)\<close>

class complex_inner = complex_vector + sgn_div_norm + dist_norm + uniformity_dist + open_uniformity +
  fixes cinner :: "'a \<Rightarrow> 'a \<Rightarrow> complex"
  assumes cinner_commute: "cinner x y = cnj (cinner y x)"
  and cinner_add_left: "cinner (x + y) z = cinner x z + cinner y z"
  and cinner_scaleC_left [simp]: "cinner (scaleC r x) y = cnj r * (cinner x y)"
  and cinner_ge_zero [simp]: "0 \<le> cinner x x"
  and cinner_eq_zero_iff [simp]: "cinner x x = 0 \<longleftrightarrow> x = 0"
  and norm_eq_sqrt_cinner: "norm x = sqrt (cmod (cinner x x))"
begin

lemma cinner_real: "cinner x x \<in> \<real>"
  by (simp add: reals_zero_comparable_iff)

lemmas cinner_commute' [simp] = cinner_commute[symmetric]

lemma cinner_zero_left [simp]: "cinner 0 x = 0"
  using cinner_add_left [of 0 0 x] by simp

lemma cinner_minus_left [simp]: "cinner (- x) y = - cinner x y"
  using cinner_add_left [of x "- x" y]
  by (metis (mono_tags, lifting) cancel_ab_semigroup_add_class.add_diff_cancel_left' cinner_zero_left group_add_class.diff_0 local.right_minus)

lemma cinner_diff_left: "cinner (x - y) z = cinner x z - cinner y z"
  using cinner_add_left [of x "- y" z] by simp

lemma cinner_sum_left: "cinner (\<Sum>x\<in>A. f x) y = (\<Sum>x\<in>A. cinner (f x) y)"
  by (cases "finite A", induct set: finite, simp_all add: cinner_add_left)

text \<open>Transfer distributivity rules to right argument.\<close>

lemma cinner_add_right: "cinner x (y + z) = cinner x y + cinner x z"
  using cinner_add_left [of y z x]
  by (metis complex_cnj_add local.cinner_commute)

lemma cinner_scaleC_right [simp]: "cinner x (scaleC r y) = r * (cinner x y)"
  using cinner_scaleC_left [of r y x]
  by (metis complex_cnj_cnj complex_cnj_mult local.cinner_commute)

lemma cinner_zero_right [simp]: "cinner x 0 = 0"
  using cinner_zero_left [of x] 
  by (metis (mono_tags, lifting) complex_cnj_zero local.cinner_commute) 

lemma cinner_minus_right [simp]: "cinner x (- y) = - cinner x y"
  using cinner_minus_left [of y x]
  by (metis complex_cnj_minus local.cinner_commute)

lemma cinner_diff_right: "cinner x (y - z) = cinner x y - cinner x z"
  using cinner_diff_left [of y z x]
  by (metis complex_cnj_diff local.cinner_commute)

lemma cinner_sum_right: "cinner x (\<Sum>y\<in>A. f y) = (\<Sum>y\<in>A. cinner x (f y))"
  apply (subst cinner_commute)
  apply (subst (2) cinner_commute)
  unfolding cnj_sum[symmetric]
  apply (subst cinner_sum_left) by simp

lemmas cinner_add [algebra_simps] = cinner_add_left cinner_add_right
lemmas cinner_diff [algebra_simps]  = cinner_diff_left cinner_diff_right
lemmas cinner_scaleC = cinner_scaleC_left cinner_scaleC_right

text \<open>Legacy theorem names\<close>
lemmas cinner_left_distrib = cinner_add_left
lemmas cinner_right_distrib = cinner_add_right
lemmas cinner_distrib = cinner_left_distrib cinner_right_distrib

lemma cinner_gt_zero_iff [simp]: "0 < cinner x x \<longleftrightarrow> x \<noteq> 0"
  by (simp add: order_less_le)

lemma power2_norm_eq_cinner: "(norm x)\<^sup>2 = cmod (cinner x x)"
  by (simp add: norm_eq_sqrt_cinner)


lemma power2_norm_eq_cinner': "complex_of_real ((norm x)\<^sup>2) = cinner x x"
  apply (subst power2_norm_eq_cinner)
  using cinner_ge_zero by (rule complex_of_real_cmod)

lemma power2_norm_eq_cinner'': "(complex_of_real (norm x))\<^sup>2 = cinner x x"
  using power2_norm_eq_cinner' by simp


text \<open>Identities involving complex multiplication and division.\<close>

lemma cinner_mult_left: "cinner (of_complex m * a) b = cnj m * (cinner a b)"
  unfolding of_complex_def by simp

lemma cinner_mult_right: "cinner a (of_complex m * b) = m * (cinner a b)"
  by (metis complex_inner_class.cinner_scaleC_right scaleC_conv_of_complex)

lemma cinner_mult_left': "cinner (a * of_complex m) b = cnj m * (cinner a b)"
  using cinner_mult_left by (simp add: of_complex_def)

lemma cinner_mult_right': "cinner a (b * of_complex m) = (cinner a b) * m"
  by (simp add: of_complex_def complex_inner_class.cinner_scaleC_right)

lemma Cauchy_Schwarz_ineq:
  "cinner x y * cnj (cinner x y) \<le> cinner x x * cinner y y"
proof (cases)
  assume "y = 0"
  thus ?thesis by simp
next
  assume y: "y \<noteq> 0"
  have [simp]: "cnj (cinner y y) = cinner y y" for y
    by (metis local.cinner_commute)
  define r where "r = cnj (cinner x y) / cinner y y"
  have "0 \<le> cinner (x - scaleC r y) (x - scaleC r y)"
    by (rule cinner_ge_zero)
  also have "\<dots> = cinner x x - r * cinner x y - cnj r * cinner y x + r * cnj r * cinner y y"
    unfolding cinner_diff_left cinner_diff_right cinner_scaleC_left cinner_scaleC_right by algebra
  also have "\<dots> = cinner x x - cinner y x * cnj r"
    unfolding r_def by auto
  also have "\<dots> = cinner x x - cinner x y * cnj (cinner x y) / cinner y y"
    unfolding r_def by (simp add: power2_eq_square)
  finally have "0 \<le> cinner x x - cinner x y * cnj (cinner x y) / cinner y y" .
  hence "cinner x y * cnj (cinner x y) / cinner y y \<le> cinner x x"
    by (simp add: le_diff_eq)
  thus "cinner x y * cnj (cinner x y) \<le> cinner x x * cinner y y"
    by (simp add: pos_divide_le_eq y)
qed

lemma Im_cinner_x_x[simp]: "Im (cinner x x) = 0"
  using comp_Im_same[OF cinner_ge_zero] by simp

lemma cinner_norm_sq: "cinner x x = complex_of_real ((norm x)^2)"
proof -
  define r where "r = Re (cinner x x)"
  have r: "cinner x x = complex_of_real r"
    unfolding r_def
    using Im_cinner_x_x[of x] apply (cases "cinner x x") by (auto simp: complex_of_real_def)
  have rpos: "r \<ge> 0"
    unfolding r_def
    using complex_of_real_nn_iff r r_def by fastforce
  show ?thesis
    unfolding power2_norm_eq_cinner
    unfolding r using rpos by auto
qed

lemma Cauchy_Schwarz_ineq2:
  "cmod (cinner x y) \<le> norm x * norm y"
proof (rule power2_le_imp_le)
  have ineq: "cinner x y * cnj (cinner x y) \<le> cinner x x * cinner y y"
    using Cauchy_Schwarz_ineq .
  have "(cmod (cinner x y))^2 = Re (cinner x y * cnj (cinner x y))"
    by (metis (mono_tags) Re_complex_of_real complex_norm_square)
  also have "\<dots> \<le> Re (cinner x x * cinner y y)"
    using ineq by (rule Re_mono)
  also have "\<dots> = Re (complex_of_real ((norm x)^2) * complex_of_real ((norm y)^2))"
    unfolding cinner_norm_sq by simp
  also have "\<dots> = (norm x * norm y)\<^sup>2"
    by (simp add: power_mult_distrib)
  finally show "(cmod (cinner x y))^2 \<le> (norm x * norm y)\<^sup>2" .
  show "0 \<le> norm x * norm y"
    by (simp add: local.norm_eq_sqrt_cinner)
qed

lemma norm_cauchy_schwarz: "abs (cinner x y) \<le> complex_of_real (norm x) * complex_of_real (norm y)"
  using Cauchy_Schwarz_ineq2 [of x y, THEN complex_of_real_mono]
  unfolding abs_complex_def
  by auto

subclass complex_normed_vector
proof
  fix a :: complex and r :: real and x y :: 'a
  show "norm x = 0 \<longleftrightarrow> x = 0"
    unfolding norm_eq_sqrt_cinner by simp
  show "norm (x + y) \<le> norm x + norm y"
  proof (rule power2_le_imp_le)
    have "cinner x y + cinner y x = complex_of_real (2 * Re (cinner x y))"
      apply (subst (2) cinner_commute)
      by (cases "cinner x y", simp add: complex_add complex_cnj complex_of_real_def)
    also have "\<dots> \<le> complex_of_real (2 * cmod (cinner x y))"
      apply (subst complex_of_real_mono_iff)
      using complex_Re_le_cmod by auto
    also have "\<dots> = 2 * abs (cinner x y)"
      unfolding abs_complex_def by simp
    also have "\<dots> \<le> 2 * complex_of_real (norm x) * complex_of_real (norm y)"
      using norm_cauchy_schwarz
      by (metis add_mono_thms_linordered_semiring(1) mult.assoc mult_2) 
    finally have xyyx: "cinner x y + cinner y x \<le> complex_of_real (2 * norm x * norm y)" by auto

    have "complex_of_real ((norm (x + y))\<^sup>2) = cinner (x+y) (x+y)"
      by (fact power2_norm_eq_cinner')
    also have "\<dots> = cinner x x + cinner x y + cinner y x + cinner y y"
      by (simp add: cinner_add)
    also have "\<dots> = complex_of_real ((norm x)\<^sup>2) + complex_of_real ((norm y)\<^sup>2) + cinner x y + cinner y x"
      unfolding power2_norm_eq_cinner' by simp
    also have "\<dots> \<le> complex_of_real ((norm x)\<^sup>2) + complex_of_real ((norm y)\<^sup>2) + complex_of_real (2 * norm x * norm y)"
      using xyyx by auto
    also have "\<dots> = complex_of_real ((norm x + norm y)\<^sup>2)"
      unfolding power2_sum by auto
    finally show "(norm (x + y))\<^sup>2 \<le> (norm x + norm y)\<^sup>2"
      apply (subst (asm) complex_of_real_mono_iff) by assumption
    show "0 \<le> norm x + norm y"
      unfolding norm_eq_sqrt_cinner by simp
  qed
  show norm_scaleC: "norm (a *\<^sub>C x) = cmod a * norm x" for a
    apply (rule power2_eq_imp_eq)
    by (simp_all add: norm_eq_sqrt_cinner norm_mult power2_eq_square power2_norm_eq_cinner power_mult_distrib)
  show "norm (r *\<^sub>R x) = \<bar>r\<bar> * norm x"
    unfolding scaleR_scaleC norm_scaleC by auto
qed

end

lemma cinner_divide_right:
  fixes a :: "'a :: {complex_inner,complex_div_algebra}"
  shows "cinner a (b / of_complex m) = (cinner a b) / m"
  by (metis (no_types, lifting) cinner_mult_right' divide_inverse divide_self_if inverse_eq_divide of_complex_divide of_complex_eq_0_iff one_neq_zero)

lemma cinner_divide_left:
  fixes a :: "'a :: {complex_inner,complex_div_algebra}"
  shows "cinner (a / of_complex m) b = (cinner a b) / cnj m"
  apply (subst cinner_commute) apply (subst cinner_divide_right) by simp

text \<open>
  Re-enable constraints for \<^term>\<open>open\<close>, \<^term>\<open>uniformity\<close>,
  \<^term>\<open>dist\<close>, and \<^term>\<open>norm\<close>.
\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::topological_space set \<Rightarrow> bool\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniform_space \<times> 'a) filter\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::metric_space \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::real_normed_vector \<Rightarrow> real\<close>)\<close>

lemma bounded_sesquilinear_cinner:
  "bounded_sesquilinear (cinner::'a::complex_inner \<Rightarrow> 'a \<Rightarrow> complex)"
proof
  fix x y z :: 'a and r :: complex
  show "cinner (x + y) z = cinner x z + cinner y z"
    by (rule cinner_add_left)
  show "cinner x (y + z) = cinner x y + cinner x z"
    by (rule cinner_add_right)
  show "cinner (scaleC r x) y = scaleC (cnj r) (cinner x y)"
    unfolding complex_scaleC_def by (rule cinner_scaleC_left)
  show "cinner x (scaleC r y) = scaleC r (cinner x y)"
    unfolding complex_scaleC_def by (rule cinner_scaleC_right)
  show "\<exists>K. \<forall>x y::'a. norm (cinner x y) \<le> norm x * norm y * K"
  proof
    show "\<forall>x y::'a. norm (cinner x y) \<le> norm x * norm y * 1"
      by (simp add: Cauchy_Schwarz_ineq2)
  qed
qed

term bounded_bilinear
thm bounded_bilinear.tendsto

lemmas tendsto_cinner [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]

lemmas isCont_cinner [simp] =
  bounded_bilinear.isCont [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]

lemmas has_derivative_cinner [derivative_intros] =
  bounded_bilinear.FDERIV [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]

lemmas bounded_csemilinear_cinner_left =
  bounded_sesquilinear.bounded_csemilinear_left [OF bounded_sesquilinear_cinner]

lemmas bounded_clinear_cinner_right =
  bounded_sesquilinear.bounded_clinear_right [OF bounded_sesquilinear_cinner]

lemmas bounded_clinear_cinner_left_comp = bounded_csemilinear_cinner_left[THEN bounded_csemilinear_compose2]
lemmas bounded_csemilinear_cinner_left_comp = bounded_csemilinear_cinner_left[THEN bounded_csemilinear_compose1]

lemmas bounded_clinear_cinner_right_comp = bounded_clinear_cinner_right[THEN bounded_clinear_compose]
lemmas bounded_csemilinear_cinner_right_comp = bounded_clinear_cinner_right[THEN bounded_csemilinear_compose3]

lemmas has_derivative_cinner_right [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_clinear_cinner_right[THEN bounded_clinear.bounded_linear]]

lemmas has_derivative_cinner_left [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_csemilinear_cinner_left[THEN bounded_csemilinear.bounded_linear]]

lemma differentiable_cinner [simp]:
  "f differentiable (at x within s) \<Longrightarrow> g differentiable at x within s \<Longrightarrow> 
        (\<lambda>x. cinner (f x) (g x)) differentiable at x within s"
  unfolding differentiable_def by (blast intro: has_derivative_cinner)


subsection \<open>Class instances\<close>

instantiation complex :: complex_inner
begin

definition cinner_complex_def [simp]: "cinner x y = cnj x * y"

instance
proof
  fix x y z r :: complex
  show "cinner x y = cnj (cinner y x)"
    unfolding cinner_complex_def by auto
  show "cinner (x + y) z = cinner x z + cinner y z"
    unfolding cinner_complex_def
    by (simp add: ring_class.ring_distribs(2))
  show "cinner (scaleC r x) y = cnj r * cinner x y"
    unfolding cinner_complex_def complex_scaleC_def by simp
  show "0 \<le> cinner x x"
    apply (rule less_eq_complexI)
    unfolding cinner_complex_def by auto
  show "cinner x x = 0 \<longleftrightarrow> x = 0"
    unfolding cinner_complex_def by simp
  show "norm x = sqrt (cmod (cinner x x))"
    apply (cases x, hypsubst_thin)
    unfolding cinner_complex_def complex_cnj complex_mult complex_norm
    by (simp add: power2_eq_square) 
qed

end

lemma
  shows complex_inner_1_left[simp]: "cinner 1 x = x"
    and complex_inner_1_right[simp]: "cinner x 1 = cnj x"
  by simp_all

lemma norm_eq_square: "norm x = a \<longleftrightarrow> 0 \<le> a \<and> cinner x x = complex_of_real (a\<^sup>2)"
  by (metis cinner_norm_sq norm_ge_zero of_real_eq_iff power2_eq_imp_eq)

lemma norm_le_square: "norm x \<le> a \<longleftrightarrow> 0 \<le> a \<and> cinner x x \<le> complex_of_real (a\<^sup>2)"
  by (metis add.left_neutral add.right_neutral add_mono_thms_linordered_field(4) cinner_norm_sq complex_of_real_mono_iff norm_ge_zero not_le power2_le_imp_le power_mono)

lemma norm_ge_square: "norm x \<ge> a \<longleftrightarrow> a \<le> 0 \<or> cinner x x \<ge> complex_of_real (a\<^sup>2)"
  by (smt complex_of_real_mono_iff norm_ge_zero power2_le_imp_le power2_norm_eq_cinner')

lemma norm_lt_square: "norm x < a \<longleftrightarrow> 0 < a \<and> cinner x x < complex_of_real (a\<^sup>2)"
  by (smt Complex_Inner_Product.norm_eq_square Complex_Inner_Product.norm_le_square less_le)

lemma norm_gt_square: "norm x > a \<longleftrightarrow> a < 0 \<or> cinner x x > complex_of_real (a\<^sup>2)"
  by (smt Complex_Inner_Product.norm_le_square less_le norm_of_real of_real_power power2_norm_eq_cinner'')

text\<open>Dot product in terms of the norm rather than conversely.\<close>

lemmas cinner_simps = cinner_add_left cinner_add_right cinner_diff_right cinner_diff_left
  cinner_scaleC_left cinner_scaleC_right

lemma of_complex_inner_1 [simp]: 
  "cinner (1 :: 'a :: {complex_inner, complex_normed_algebra_1}) (of_complex x) = x"  
  by (simp add: cinner_norm_sq of_complex_def)

lemma of_complex_inner_1' [simp]:
  "cinner (of_complex x) (1 :: 'a :: {complex_inner, complex_normed_algebra_1}) = cnj x"  
  by (simp add: cinner_norm_sq of_complex_def)

lemma summable_of_complex_iff: 
  "summable (\<lambda>x. of_complex (f x) :: 'a :: {complex_normed_algebra_1,complex_inner}) \<longleftrightarrow> summable f"
proof
  assume *: "summable (\<lambda>x. of_complex (f x) :: 'a)"
  interpret bounded_linear "\<lambda>x::'a. cinner 1 x"
    apply (rule bounded_clinear.bounded_linear)
    by (rule bounded_clinear_cinner_right)
  from summable [OF *] show "summable f" by simp
next
  assume sum: "summable f"
  then show "summable (\<lambda>x. of_complex (f x) :: 'a)"
    by (rule summable_of_complex)
qed


subsection \<open>Gradient derivative\<close>

definition
  cgderiv ::
    "['a::complex_inner \<Rightarrow> complex, 'a, 'a] \<Rightarrow> bool"
          ("(cGDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
where
  "cGDERIV f x :> D \<longleftrightarrow> FDERIV f x :> (cinner D)"

lemma cgderiv_deriv [simp]: "cGDERIV f x :> D \<longleftrightarrow> DERIV f x :> (cnj D)"
  by (simp only: cgderiv_def has_field_derivative_def cinner_complex_def[THEN ext])

lemma cGDERIV_DERIV_compose:
  assumes "cGDERIV f x :> df" and "DERIV g (f x) :> cnj dg"
  shows "cGDERIV (\<lambda>x. g (f x)) x :> scaleC dg df"
  apply (insert assms)
  unfolding cgderiv_def has_field_derivative_def
  apply (drule (1) has_derivative_compose)
  unfolding cinner_scaleC_left complex_cnj_cnj
  by assumption

lemma cGDERIV_subst: "\<lbrakk>cGDERIV f x :> df; df = d\<rbrakk> \<Longrightarrow> cGDERIV f x :> d"
  by simp

lemma cGDERIV_const: "cGDERIV (\<lambda>x. k) x :> 0"
  unfolding cgderiv_def cinner_zero_left[THEN ext] by (rule has_derivative_const)

lemma cGDERIV_add:
    "\<lbrakk>cGDERIV f x :> df; cGDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> cGDERIV (\<lambda>x. f x + g x) x :> df + dg"
  unfolding cgderiv_def cinner_add_left[THEN ext] by (rule has_derivative_add)

lemma cGDERIV_minus:
    "cGDERIV f x :> df \<Longrightarrow> cGDERIV (\<lambda>x. - f x) x :> - df"
  unfolding cgderiv_def cinner_minus_left[THEN ext] by (rule has_derivative_minus)

lemma cGDERIV_diff:
    "\<lbrakk>cGDERIV f x :> df; cGDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> cGDERIV (\<lambda>x. f x - g x) x :> df - dg"
  unfolding cgderiv_def cinner_diff_left by (rule has_derivative_diff)

lemmas has_derivative_scaleC[simp, derivative_intros] = 
  bounded_bilinear.FDERIV[OF bounded_cbilinear_scaleC[THEN bounded_cbilinear.bounded_bilinear]]

lemma cGDERIV_scaleC:
    "\<lbrakk>DERIV f x :> df; cGDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> cGDERIV (\<lambda>x. scaleC (f x) (g x)) x
      :> (scaleC (cnj (f x)) dg + scaleC (cnj df) (cnj (g x)))"
  unfolding cgderiv_def has_field_derivative_def cinner_add_left cinner_scaleC_left
  apply (rule has_derivative_subst)
  apply (erule (1) has_derivative_scaleC)
  by (simp add: ac_simps)
  

lemma cGDERIV_mult:
    "\<lbrakk>cGDERIV f x :> df; cGDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> cGDERIV (\<lambda>x. f x * g x) x :> scaleC (cnj (f x)) dg + scaleC (cnj (g x)) df"
  unfolding cgderiv_def
  apply (rule has_derivative_subst)
   apply (erule (1) has_derivative_mult)
  unfolding cinner_add
  unfolding cinner_scaleC_left[THEN ext]
  by (simp add: cinner_add ac_simps)

lemma cGDERIV_inverse:
    "\<lbrakk>cGDERIV f x :> df; f x \<noteq> 0\<rbrakk>
     \<Longrightarrow> cGDERIV (\<lambda>x. inverse (f x)) x :> cnj (- (inverse (f x))\<^sup>2) *\<^sub>C df"
  apply (erule cGDERIV_DERIV_compose, simp)
  by (erule DERIV_inverse [folded numeral_2_eq_2])

(* TODO: 

lemma cGDERIV_norm:
  assumes "x \<noteq> 0" shows "cGDERIV (\<lambda>x. complex_of_real (norm x)) x :> sgn x"

lemmas has_derivative_norm = cGDERIV_norm [unfolded cgderiv_def]
*)

class hilbert_space = complex_inner + complete_space begin
subclass banach by standard
end

class chilbert_space = complex_inner + complete_space begin
subclass hilbert_space by standard
end

end
