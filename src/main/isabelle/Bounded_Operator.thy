theory Bounded_Operator
  imports Complex_Main "HOL-Library.Adhoc_Overloading" "HOL-Library.Rewrite" "HOL-Analysis.L2_Norm"
begin

section \<open>Subspaces\<close>

notation
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) 

definition "has_ell2_norm x = bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)"
lemma has_ell2_norm_setL2: "has_ell2_norm x = bdd_above (setL2 (norm o x) ` Collect finite)"
proof -
(*   have mono: "mono (\<lambda>A. sqrt (\<Sum>i\<in>A. (cmod (x i))\<^sup>2))"
    unfolding mono_def apply (auto intro: sum_mono2)
    apply (rule sum_mono2) *)
  have bdd_above_image_mono': "(\<And>x y. x\<le>y \<Longrightarrow> x:A \<Longrightarrow> y:A \<Longrightarrow> f x \<le> f y) \<Longrightarrow> (\<exists>M\<in>A. \<forall>x \<in> A. x \<le> M) \<Longrightarrow> bdd_above (f`A)" for f::"'a set\<Rightarrow>real" and A
    unfolding bdd_above_def by auto

  have "bdd_above X \<Longrightarrow> bdd_above (sqrt ` X)" for X
    by (simp add: bdd_above_image_mono monoI)
  moreover have "bdd_above X" if bdd_sqrt: "bdd_above (sqrt ` X)" for X
  proof -
    obtain y where y:"y \<ge> sqrt x" if "x:X" for x 
      using bdd_sqrt unfolding bdd_above_def by auto
    have "y*y \<ge> x" if "x:X" for x
      by (metis power2_eq_square sqrt_le_D that y)
    then show "bdd_above X"
      unfolding bdd_above_def by auto
  qed
  ultimately have bdd_sqrt: "bdd_above X \<longleftrightarrow> bdd_above (sqrt ` X)" for X
    by rule

  show "has_ell2_norm x \<longleftrightarrow> bdd_above (setL2 (norm o x) ` Collect finite)"
    unfolding has_ell2_norm_def unfolding setL2_def 
    apply (rewrite asm_rl[of "(\<lambda>A. sqrt (\<Sum>i\<in>A. ((cmod \<circ> x) i)\<^sup>2)) ` Collect finite 
                            = sqrt ` (\<lambda>A. (\<Sum>i\<in>A. (cmod (x i))\<^sup>2)) ` Collect finite"])
      apply auto[1]
    apply (subst bdd_sqrt[symmetric])
    by (simp add: monoI)
qed

typedef 'a vector = "{x::'a\<Rightarrow>complex. has_ell2_norm x}"
  unfolding has_ell2_norm_def by (rule exI[of _ "\<lambda>_.0"], auto)
setup_lifting type_definition_vector

lemma SUP_max:
  fixes f::"'a::order\<Rightarrow>'b::conditionally_complete_lattice"
  assumes "mono f"
  assumes "\<And>x. x:M \<Longrightarrow> x\<le>m"
  assumes "m:M"
  shows "(SUP x:M. f x) = f m"
  apply (rule antisym)
  apply (metis assms(1) assms(2) assms(3) cSUP_least empty_iff monoD)
  by (metis assms(1) assms(2) assms(3) bdd_aboveI bdd_above_image_mono cSUP_upper)


definition "ell2_norm x = sqrt (SUP F:{F. finite F}. sum (\<lambda>i. (norm(x i))^2) F)"

lemma ell2_norm_setL2: 
  assumes "has_ell2_norm x"
  shows "ell2_norm x = (SUP F:{F. finite F}. setL2 (norm o x) F)"
  unfolding ell2_norm_def setL2_def o_def apply (subst continuous_at_Sup_mono)
  using monoI real_sqrt_le_mono apply blast
  using continuous_at_split isCont_real_sqrt apply blast
  using assms unfolding has_ell2_norm_def by auto

lemma has_ell2_norm_finite[simp]: "has_ell2_norm (x::'a::finite\<Rightarrow>_)"
  unfolding has_ell2_norm_def by simp

lemma ell2_norm_finite_def: "ell2_norm (x::'a::finite\<Rightarrow>complex) = sqrt (sum (\<lambda>i. (norm(x i))^2) UNIV)"
proof -
  have mono: "mono (sum (\<lambda>i. (cmod (x i))\<^sup>2))"
    unfolding mono_def apply auto apply (subst sum_mono2) by auto
  show ?thesis
    unfolding ell2_norm_def apply (subst SUP_max[where m=UNIV])
    using mono by auto
qed

lemma setL2_mono2:
  assumes "finite L"
  assumes "K \<le> L"
  shows "setL2 f K \<le> setL2 f L"
  unfolding setL2_def apply (rule real_sqrt_le_mono)
  apply (rule sum_mono2)
  using assms by auto

lemma ell2_norm_finite_def': "ell2_norm (x::'a::finite\<Rightarrow>complex) = setL2 (norm o x) UNIV"
  apply (subst ell2_norm_setL2) apply simp
  apply (subst SUP_max[where m=UNIV])
  by (auto simp: mono_def intro!: setL2_mono2)

lemma ell2_1: assumes  "finite F" shows "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) \<le> 1"
proof - 
  have "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 0" if "a\<notin>F"
    apply (subst sum.cong[where B=F and h="\<lambda>_. 0"]) using that by auto
  moreover have "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 1" if "a\<in>F"
  proof -
    obtain F0 where "a\<notin>F0" and F_F0: "F=insert a F0"
      by (meson \<open>a \<in> F\<close> mk_disjoint_insert) 
    show "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 1"
      unfolding F_F0
      apply (subst sum.insert_remove)
       using F_F0 assms apply auto
      apply (subst sum.cong[where B=F0 and h="\<lambda>_. 0"])
        apply (simp add: \<open>a \<notin> F0\<close>)
       using \<open>a \<notin> F0\<close> apply auto[1]
      by simp
  qed
  ultimately show "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) \<le> 1"
    by linarith
qed


lemma cSUP_leD: "bdd_above (f`A) \<Longrightarrow> (SUP i:A. f i) \<le> y \<Longrightarrow> i \<in> A \<Longrightarrow> f i \<le> y" for y :: "'a::conditionally_complete_lattice"
  by (meson cSUP_upper order_trans)

lemma ell2_norm_0:
  assumes "has_ell2_norm x"
  shows "(ell2_norm x = 0) = (x = (\<lambda>_. 0))"
proof
  assume "x = (\<lambda>_. 0)"
  then show "ell2_norm x = 0"
    unfolding ell2_norm_def apply auto
    by (metis cSUP_const empty_Collect_eq finite.emptyI)
next
  assume norm0: "ell2_norm x = 0"
  show "x = (\<lambda>_. 0)"
  proof
    fix i
    have "sum (\<lambda>i. (cmod (x i))\<^sup>2) {i} \<le> 0" 
      apply (rule cSUP_leD[where A="Collect finite"])
      using norm0 assms unfolding has_ell2_norm_def ell2_norm_def by auto
    then show "x i = 0" by auto
  qed
qed

lemma ell2_norm_smult:
  assumes "has_ell2_norm x"
  shows "has_ell2_norm (\<lambda>i. c * x i)" and "ell2_norm (\<lambda>i. c * x i) = cmod c * ell2_norm x"
proof -
  have setL2_mul: "setL2 (cmod \<circ> (\<lambda>i. c * x i)) F = cmod c * setL2 (cmod \<circ> x) F" for F
  proof -
    have "setL2 (cmod \<circ> (\<lambda>i. c * x i)) F = setL2 (\<lambda>i. (cmod c * (cmod o x) i)) F"
      by (metis comp_def norm_mult)
    also have "\<dots> = cmod c * setL2 (cmod o x) F"
      by (metis norm_ge_zero setL2_right_distrib)
    finally show ?thesis .
  qed

  from assms obtain M where M: "M \<ge> setL2 (cmod o x) F" if "finite F" for F
    unfolding has_ell2_norm_setL2 bdd_above_def by auto
  then have "cmod c * M \<ge> setL2 (cmod o (\<lambda>i. c * x i)) F" if "finite F" for F
    unfolding setL2_mul
    by (simp add: ordered_comm_semiring_class.comm_mult_left_mono that) 
  then show has: "has_ell2_norm (\<lambda>i. c * x i)"
    unfolding has_ell2_norm_setL2 bdd_above_def using setL2_mul[symmetric] by auto

  have "ell2_norm (\<lambda>i. c * x i) = SUPREMUM (Collect finite) (setL2 (cmod \<circ> (\<lambda>i. c * x i)))"
    apply (rule ell2_norm_setL2) by (rule has)
  also have "\<dots> = SUPREMUM (Collect finite) (\<lambda>F. cmod c * setL2 (cmod \<circ> x) F)"
    apply (rule SUP_cong) apply auto by (rule setL2_mul)
  also have "\<dots> = cmod c * ell2_norm x" 
    apply (subst ell2_norm_setL2) apply (fact assms)
    apply (subst continuous_at_Sup_mono[where f="\<lambda>x. cmod c * x"])
    apply (simp add: mono_def ordered_comm_semiring_class.comm_mult_left_mono)
       apply (rule continuous_mult)
    using continuous_const apply blast
       apply simp
      apply blast
     apply (meson assms has_ell2_norm_setL2)
    by auto
  finally show "ell2_norm (\<lambda>i. c * x i) = cmod c * ell2_norm x" .
qed
  

lemma ell2_norm_triangle:
  assumes "has_ell2_norm x" and "has_ell2_norm y"
  shows "has_ell2_norm (\<lambda>i. x i + y i)" and "ell2_norm (\<lambda>i. x i + y i) \<le> ell2_norm x + ell2_norm y"
proof -
  have triangle: "setL2 (cmod \<circ> (\<lambda>i. x i + y i)) F \<le> setL2 (cmod \<circ> x) F + setL2 (cmod \<circ> y) F" (is "?lhs\<le>?rhs") 
    if "finite F" for F
  proof -
    have "?lhs \<le> setL2 (\<lambda>i. (cmod o x) i + (cmod o y) i) F"
      apply (rule setL2_mono)
      by (auto simp: norm_triangle_ineq)
    also have "\<dots> \<le> ?rhs"
      by (rule setL2_triangle_ineq)
    finally show ?thesis .
  qed

  obtain Mx My where Mx: "Mx \<ge> setL2 (cmod o x) F" and My: "My \<ge> setL2 (cmod o y) F" if "finite F" for F
    using assms unfolding has_ell2_norm_setL2 bdd_above_def by auto
  then have MxMy: "Mx + My \<ge> setL2 (cmod \<circ> x) F + setL2 (cmod \<circ> y) F" if "finite F" for F
    using that by fastforce
  then have bdd_plus: "bdd_above ((\<lambda>xa. setL2 (cmod \<circ> x) xa + setL2 (cmod \<circ> y) xa) ` Collect finite)"
    unfolding bdd_above_def by auto
  from MxMy have MxMy': "Mx + My \<ge> setL2 (cmod \<circ> (\<lambda>i. x i + y i)) F" if "finite F" for F 
    using triangle that by fastforce
  then show has: "has_ell2_norm (\<lambda>i. x i + y i)"
    unfolding has_ell2_norm_setL2 bdd_above_def by auto

  have SUP_plus: "(SUP x:A. f x + g x) \<le> (SUP x:A. f x) + (SUP x:A. g x)" 
    if notempty: "A\<noteq>{}" and bddf: "bdd_above (f`A)"and bddg: "bdd_above (g`A)"
    for f g :: "'a set \<Rightarrow> real" and A
  proof -
    have xleq: "x \<le> (SUP x:A. f x) + (SUP x:A. g x)" if x: "x \<in> (\<lambda>x. f x + g x) ` A" for x
    proof -
      obtain a where aA: "a:A" and ax: "x = f a + g a"
        using x by blast
      have fa: "f a \<le> (SUP x:A. f x)"
        by (simp add: bddf aA cSUP_upper)
      moreover have "g a \<le> (SUP x:A. g x)"
        by (simp add: bddg aA cSUP_upper)
      ultimately have "f a + g a \<le> (SUP x:A. f x) + (SUP x:A. g x)" by simp
      with ax show ?thesis by simp
    qed
    show ?thesis
      apply (rule cSup_least) using notempty xleq by auto
  qed
  
  show "ell2_norm (\<lambda>i. x i + y i) \<le> ell2_norm x + ell2_norm y"
    apply (subst ell2_norm_setL2, fact has)
    apply (subst ell2_norm_setL2, fact assms)+
    apply (rule order.trans[rotated])
     apply (rule SUP_plus)
       apply auto[1]
      apply (meson assms(1) has_ell2_norm_setL2)
     apply (meson assms(2) has_ell2_norm_setL2)
    apply (rule cSUP_subset_mono)
       apply auto
    using MxMy unfolding bdd_above_def apply auto[1]
    using triangle by fastforce
qed

(*axiomatization where ell2_norm_triangle:
 "bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)
  \<Longrightarrow>
  bdd_above (sum (\<lambda>i. (cmod (y i))\<^sup>2) ` Collect finite)
  \<Longrightarrow>
  ell2_norm (\<lambda>i. x i + y i) \<le> ell2_norm x + ell2_norm y"
for x y :: "'a\<Rightarrow>complex"
  
axiomatization where ell2_norm_mult:
  "bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)
  \<Longrightarrow>
  ell2_norm (\<lambda>i. a *\<^sub>R x i) = \<bar>a\<bar> * ell2_norm x"
for x :: "'a\<Rightarrow>complex" *)


lift_definition ket :: "'a \<Rightarrow> 'a vector" is "\<lambda>x y. if x=y then 1 else 0"
  unfolding has_ell2_norm_def bdd_above_def apply simp
  apply (rule exI[of _ 1], rule allI, rule impI)
  by (rule ell2_1)

lemma cSUP_eq_maximum:
  fixes z :: "_::conditionally_complete_lattice"
  assumes "\<exists>x\<in>X. f x = z"
  assumes "\<And>x. x \<in> X \<Longrightarrow> f x \<le> z"
  shows "(SUP x:X. f x) = z"
  by (metis (mono_tags, hide_lams) assms(1) assms(2) cSup_eq_maximum imageE image_eqI)

instantiation vector :: (type)real_vector begin
lift_definition zero_vector :: "'a vector" is "\<lambda>_.0" by (auto simp: has_ell2_norm_def)
lift_definition uminus_vector :: "'a vector \<Rightarrow> 'a vector" is uminus by (simp add: has_ell2_norm_def)
lift_definition plus_vector :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> 'a vector" is "\<lambda>f g x. f x + g x"
  by (rule ell2_norm_triangle) 
definition "a - b = a + (-b)" for a b :: "'a vector"
lift_definition scaleR_vector :: "real \<Rightarrow> 'a vector \<Rightarrow> 'a vector" is "\<lambda>r f x. complex_of_real r * f x"
  by (rule ell2_norm_smult)

instance apply intro_classes
          apply (transfer; rule ext; simp)
         apply (transfer; rule ext; simp)
        apply (transfer; rule ext; simp)
       apply (transfer; rule ext; simp)
      apply (unfold minus_vector_def; transfer; rule ext; simp)
     apply (transfer; rule ext; simp add: distrib_left)
    apply (transfer; rule ext; simp add: distrib_right)
   apply (transfer; rule ext; simp add: scaleR_add_left)
  by (transfer; rule ext; simp)
end

instantiation vector :: (type)real_normed_vector begin
lift_definition norm_vector :: "'a vector \<Rightarrow> real" is ell2_norm .
definition "dist x y = norm (x - y)" for x y::"'a vector"
definition "sgn x = x /\<^sub>R norm x" for x::"'a vector"
definition "uniformity = (INF e:{0<..}. principal {(x::'a vector, y). norm (x - y) < e})"
definition "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e:{0<..}. principal {(x, y). norm (x - y) < e}. x' = x \<longrightarrow> y \<in> U)" for U :: "'a vector set"
instance apply intro_classes
  unfolding dist_vector_def sgn_vector_def uniformity_vector_def open_vector_def apply simp_all
    apply transfer apply (fact ell2_norm_0)
   apply transfer apply (fact ell2_norm_triangle)
  apply transfer apply (subst ell2_norm_smult) by auto
end

axiomatization timesScalarVec :: "complex \<Rightarrow> 'a vector \<Rightarrow> 'a vector" where
  timesScalarVec_twice[simp]: "timesScalarVec a (timesScalarVec b \<psi>) = timesScalarVec (a*b) \<psi>"
and uminus_vector: "(-\<psi>) = timesScalarVec (-1) \<psi>"
and one_times_vec[simp]: "timesScalarVec (1::complex) \<psi> = \<psi>" 
for \<psi> :: "'a vector"

lemma ell2_ket[simp]: "norm (ket i) = 1"
  apply transfer unfolding ell2_norm_def real_sqrt_eq_1_iff
  apply (rule cSUP_eq_maximum)
  apply (rule_tac x="{i}" in bexI)
    apply auto
  by (rule ell2_1)

axiomatization orthogonal :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> bool"
  where orthogonal_comm: "orthogonal \<psi> \<phi> = orthogonal \<phi> \<psi>"

axiomatization is_subspace :: "'a vector set \<Rightarrow> bool"
  where is_subspace_0[simp]: "is_subspace {0}"
    and is_subspace_UNIV[simp]: "is_subspace UNIV"
    and is_subspace_orthog[simp]: "is_subspace A \<Longrightarrow> is_subspace {\<psi>. (\<forall>\<phi>\<in>A. orthogonal \<psi> \<phi>)}"
    and is_subspace_inter[simp]: "is_subspace A \<Longrightarrow> is_subspace B \<Longrightarrow> is_subspace (A\<inter>B)"
    and is_subspace_plus: "is_subspace A \<Longrightarrow> is_subspace B \<Longrightarrow> is_subspace {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}"
    and is_subspace_contains_0: "is_subspace A \<Longrightarrow> 0 \<in> A"
    and is_subspace_closed_plus: "is_subspace A \<Longrightarrow> x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (x+y) \<in> A"
    and is_subspace_INF[simp]: "(\<And>x. x \<in> AA \<Longrightarrow> is_subspace x) \<Longrightarrow> is_subspace (\<Inter>AA)"

typedef 'a subspace = "{A::'a vector set. is_subspace A}"
  morphisms subspace_to_set Abs_subspace
  apply (rule exI[of _ "{0}"]) by simp
setup_lifting type_definition_subspace

instantiation subspace :: (type)zero begin (* The subspace {0} *)
lift_definition zero_subspace :: "'a subspace" is "{0::'a vector}" by simp
instance .. end

instantiation subspace :: (type)top begin  (* The full space *)
lift_definition top_subspace :: "'a subspace" is "UNIV::'a vector set" by simp
instance .. end

instantiation subspace :: (type)inf begin  (* Intersection *)
lift_definition inf_subspace :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> 'a subspace" is "op\<inter>" by simp
instance .. end

instantiation subspace :: (type)sup begin  (* Sum of spaces *)
lift_definition sup_subspace :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> 'a subspace" is "\<lambda>A B::'a vector set. {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}" 
  by (rule is_subspace_plus)
instance .. end
instantiation subspace :: (type)plus begin  (* Sum of spaces *)
lift_definition plus_subspace :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> 'a subspace" is "\<lambda>A B::'a vector set. {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}"
  by (rule is_subspace_plus)
instance .. end

lemma subspace_sup_plus: "(sup :: 'a subspace \<Rightarrow> _ \<Rightarrow> _) = op+" 
  unfolding sup_subspace_def plus_subspace_def by simp

instantiation subspace :: (type)Inf begin  (* Intersection *)
lift_definition Inf_subspace :: "'a subspace set \<Rightarrow> 'a subspace" is "Inf :: 'a vector set set \<Rightarrow> 'a vector set" by simp
instance .. end

instantiation subspace :: (type)ord begin  
lift_definition less_eq_subspace :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> bool" is "op\<subseteq>". (* \<le> means inclusion *)
lift_definition less_subspace :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> bool" is "op\<subset>". (* \<le> means inclusion *)
instance .. end

instantiation subspace :: (type)Sup begin (* Sum of spaces *)
definition "Sup_subspace AA = (Inf {B::'a subspace. \<forall>A\<in>AA. B \<ge> A})"
(* lift_definition Sup_subspace :: "'a subspace set \<Rightarrow> 'a subspace" is "\<lambda>AA. Inf (A" by simp *)
(* lift_definition Sup_subspace :: "\<Sqinter>A\<in>{A."  *)
instance .. end

lemma subspace_zero_not_top[simp]: "(0::'a subspace) \<noteq> top"
proof transfer 
  have "ket undefined \<noteq> (0::'a vector)"
    apply transfer
    by (meson one_neq_zero)
  thus "{0::'a vector} \<noteq> UNIV" by auto
qed

(* axiomatization where
 (* subspace_plus_sup: "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y + z \<le> x" *)
    (* subspace_zero_not_top[simp]: "(0::'a subspace) \<noteq> top" *)
(* and tmp_reflex: "x \<le> x" (* Names with tmp_ will be hidden later *) *)
(* and tmp_transitive: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" *)
(* and tmp_antisym: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" *)
(* and tmp_top: "x \<le> top" *)
(* and tmp_pos: "x \<ge> 0" (* zero_le *) *)
(* and tmp_inf1: "inf x y \<le> x" *)
(* and tmp_inf2: "inf x y \<le> y" *)
(* and tmp_inf: "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z" *)
(* and tmp_assoc: "x + y + z = x + (y + z)"  *)
(* and tmp_comm: "x + y = y + x" *)
(* and tmp_mono: "x \<le> y \<Longrightarrow> z + x \<le> z + y" *)
(* and tmp_zero_neutral: "0 + x = x" *)
(* and tmp_Inf1: "x \<in> A \<Longrightarrow> Inf A \<le> x" *)
(* and tmp_Inf2: "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A" *)
 and tmp_Sup1: "x \<in> A \<Longrightarrow> Sup A \<ge> x" 
 and tmp_Sup2: "(\<And>x. x \<in> A \<Longrightarrow> z \<ge> x) \<Longrightarrow> z \<ge> Sup A" 
 and subspace_empty_Sup: "Sup {} = 0"
(* and tmp_Inf3: "Inf {} = (top::'a subspace)"  *)
for x y z :: "'a subspace"  *)

instantiation subspace :: (type)order begin
instance apply intro_classes
  apply transfer apply (simp add: subset_not_subset_eq)
  apply transfer apply simp
  apply transfer apply simp
  apply transfer by simp
end

instantiation subspace :: (type)order_top begin
instance apply intro_classes
  apply transfer by simp
end

instantiation subspace :: (type)order_bot begin
lift_definition bot_subspace :: "'a subspace" is "{0::'a vector}" by (fact is_subspace_0)
instance apply intro_classes
  apply transfer by (simp add: is_subspace_contains_0)
end
lemma subspace_zero_bot: "(0::_ subspace) = bot" 
  unfolding zero_subspace_def bot_subspace_def by simp

instantiation subspace :: (type)ab_semigroup_add begin
instance apply intro_classes
   apply transfer apply auto using add.assoc apply blast apply (metis add.semigroup_axioms semigroup.assoc)
  apply transfer apply auto using add.commute by blast+
end
  
instantiation subspace :: (type)ordered_ab_semigroup_add begin
instance apply intro_classes
  apply transfer by auto
end
 
instantiation subspace :: (type)comm_monoid_add begin
instance apply intro_classes
  apply transfer by auto
end


instantiation subspace :: (type)semilattice_sup begin
instance proof intro_classes
  fix x y z :: "'a subspace"
  show "x \<le> x \<squnion> y"
    apply transfer apply auto apply (rule exI, rule exI[of _ 0]) using is_subspace_contains_0 by auto
  show "y \<le> x \<squnion> y"
    apply transfer apply auto apply (rule exI[of _ 0]) using is_subspace_contains_0 by auto
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    apply transfer apply auto
    apply (rule is_subspace_closed_plus)
    by auto
qed
end

instantiation subspace :: (type)canonically_ordered_monoid_add begin
instance apply intro_classes
  unfolding subspace_sup_plus[symmetric]
  apply auto apply (rule_tac x=b in exI)
  by (simp add: sup.absorb2) 
end
  
instantiation subspace :: (type)semilattice_inf begin
instance apply intro_classes
    apply transfer apply simp
   apply transfer apply simp
  apply transfer by simp
end

instantiation subspace :: (type)lattice begin
instance ..
end

lemma  subspace_plus_sup: "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y + z \<le> x" for x y z :: "'a subspace"
  unfolding subspace_sup_plus[symmetric] by auto

instantiation subspace :: (type)complete_lattice begin
instance proof intro_classes
  fix x z :: "'a subspace" and A
  show Inf_le: "x \<in> A \<Longrightarrow> Inf A \<le> x" for A and x::"'a subspace"
    apply transfer by auto
  show le_Inf: "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A" for A and z::"'a subspace"
    apply transfer by auto
  show "Inf {} = (top::'a subspace)"
    apply transfer by auto
  show "x \<le> Sup A" if "x \<in> A"
    unfolding Sup_subspace_def 
    apply (rule le_Inf)
    using that by auto
  show "(\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z" 
    unfolding Sup_subspace_def
    apply (rule Inf_le)
    by auto
  have "Inf UNIV = (bot::'a subspace)"    
    apply (rule antisym)
     apply (rule Inf_le) apply simp
    apply (rule le_Inf) by simp
  thus "Sup {} = (bot::'a subspace)"
    unfolding Sup_subspace_def by auto
qed
end

lemma subspace_empty_Sup: "Sup {} = (0::'a subspace)"
  unfolding subspace_zero_bot by auto

lemma top_not_bot[simp]: "(top::'a subspace) \<noteq> bot"
  by (metis subspace_zero_bot subspace_zero_not_top) 

lemma inf_assoc_subspace[simp]: "A \<sqinter> B \<sqinter> C = A \<sqinter> (B \<sqinter> C)" for A B C :: "_ subspace"
  unfolding inf.assoc by simp
lemma inf_left_commute[simp]: "A \<sqinter> (B \<sqinter> C) = B \<sqinter> (A \<sqinter> C)" for A B C :: "_ subspace"
  using inf.left_commute by auto

lemma bot_plus[simp]: "bot + x = x" for x :: "'a subspace"
  apply transfer
  unfolding sup_subspace_def[symmetric] by simp
lemma plus_bot[simp]: "x + bot = x" for x :: "'a subspace" unfolding subspace_sup_plus[symmetric] by simp
lemma top_plus[simp]: "top + x = top" for x :: "'a subspace" unfolding subspace_sup_plus[symmetric] by simp
lemma plus_top[simp]: "x + top = top" for x :: "'a subspace" unfolding subspace_sup_plus[symmetric] by simp
    
axiomatization subspace_as_set :: "'a subspace \<Rightarrow> 'a vector set"

definition [code del]: "span A = Inf {S. A \<subseteq> subspace_as_set S}"
(* definition [code del]: "spanState A = Inf {S. state_to_vector ` A \<subseteq> subspace_as_set S}" *)
(* consts span :: "'a set \<Rightarrow> 'b subspace"
adhoc_overloading span (* spanState *) spanVector *)

(* lemma span_vector_state: "spanState A = spanVector (state_to_vector ` A)"
  by (simp add: spanState_def spanVector_def)  *)

axiomatization where span_mult[simp]: "(a::complex)\<noteq>0 \<Longrightarrow> span { timesScalarVec a \<psi> } = span {\<psi>}"
  for \<psi>::"'a vector"

lemma leq_INF[simp]:
  fixes V :: "'a \<Rightarrow> 'b subspace"
  shows "(A \<le> (INF x. V x)) = (\<forall>x. A \<le> V x)"
  by (simp add: le_Inf_iff)

lemma leq_plus_subspace[simp]: "a \<le> a + c" for a::"'a subspace"
  by (simp add: add_increasing2)
lemma leq_plus_subspace2[simp]: "a \<le> c + a" for a::"'a subspace"
  by (simp add: add_increasing)


axiomatization ortho :: "'a subspace \<Rightarrow> 'a subspace" (* Orthogonal complement *)
  where ortho_leq[simp]: "ortho a \<le> ortho b \<longleftrightarrow> a \<ge> b"
    and ortho_twice[simp]: "ortho (ortho x) = x"


lemma ortho_top[simp]: "ortho top = bot"
  apply (rule le_bot)
  apply (subst ortho_twice[symmetric, of bot])
  apply (subst ortho_leq)
  by simp

lemma ortho_bot[simp]: "ortho bot = top"
  apply (rule top_le)
  apply (subst ortho_twice[symmetric, of top])
  apply (subst ortho_leq)
  by simp


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
definition "op+ = plusOp" 
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

axiomatization where adjoint_twice[simp]: "U** = U" for U :: "('a,'b) bounded"

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
  apply (rewrite asm_rl[of "Some = Some o id"]) apply simp
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
