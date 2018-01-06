theory QRHL_Core
  imports Complex_Main "HOL-Library.Adhoc_Overloading" "HOL-Library.Rewrite"
begin

section \<open>Miscellaneous\<close>

definition [code del]: "(sqrt2::complex) = sqrt 2"
lemma sqrt22[simp]: "sqrt2 * sqrt2 = 2" 
 by (simp add: of_real_def scaleR_2 sqrt2_def)
lemma sqrt2_neq0[simp]: "sqrt2 \<noteq> 0" unfolding sqrt2_def by simp
lemma [simp]: "cnj sqrt2 = sqrt2" unfolding sqrt2_def by simp

syntax "Lattices.sup_class.sup" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
syntax "Lattices.inf_class.inf" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)

typedef 'a distr = "{f::'a\<Rightarrow>real. (\<forall>x. f x \<ge> 0) \<and> (\<forall> M. finite M \<longrightarrow> sum f M \<le> 1)}" 
  morphisms prob Abs_distr
  apply (rule exI[of _ "\<lambda>x. 0"]) by auto
setup_lifting type_definition_distr

instantiation distr :: (type)zero begin
lift_definition zero_distr :: "'a distr" is "(\<lambda>_. 0)" by simp
instance .. 
end
 
  
lift_definition supp :: "'a distr \<Rightarrow> 'a set" is "\<lambda>\<mu>. {x. \<mu> x > 0}" .
lift_definition uniform :: "'a set \<Rightarrow> 'a distr" is "\<lambda>M. (\<lambda>m. if m\<in>M then 1/card M else 0)"
proof (rule conjI; rule allI; (rule impI)?)
  fix M and x :: 'a
  show "0 \<le> (if x \<in> M then 1 / real (card M) else 0)" by auto
  fix F
  show "(\<Sum>m\<in>F. if m \<in> M then 1 / real (card M) else 0) \<le> 1" if "finite F"
  proof (cases "finite M")
    case True
    show ?thesis
      apply (subst sum.inter_restrict[symmetric, OF that])
      apply simp
      by (metis Int_lower2 True card_mono divide_le_eq_1 neq0_conv of_nat_0_less_iff of_nat_eq_0_iff of_nat_le_iff)
  next
    case False
    show ?thesis
      apply (subst card_infinite[OF False])
      apply (rewrite asm_rl[of "1/real 0 = 0"]) apply auto[1]
      by auto
  qed
qed


lemma supp_uniform [simp]: "M \<noteq> {} \<Longrightarrow> finite M \<Longrightarrow> supp (uniform M) = M" for M :: "'a set"
  apply transfer apply auto
  using card_gt_0_iff by blast

lemma uniform_infinite: "infinite M \<Longrightarrow> uniform M = 0"
  apply transfer by auto

lemma uniform_empty: "uniform {} = 0"
  apply transfer by simp

axiomatization weight :: "'a distr \<Rightarrow> real" where
  weight_pos[simp]: "weight \<mu> \<ge> 0" 
and weight_leq1[simp]: "weight \<mu> \<le> 1"
and weight_uniform[simp]: "M \<noteq> {} \<Longrightarrow> finite M \<Longrightarrow> weight (uniform M) = 1"

axiomatization "map_distr" :: "('a\<Rightarrow>'b) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" where
  weight_map_distr[simp]: "weight (map_distr f \<mu>) = weight \<mu>"
  and supp_map_distr[simp]: "supp (map_distr f \<mu>) = f ` (supp \<mu>)"
  
axiomatization where  
  compose_map_distr[simp]: "map_distr g (map_distr f \<mu>) = map_distr (\<lambda>x. g (f x)) \<mu>"
and  map_distr_id[simp]: "map_distr (\<lambda>x. x) \<mu> = \<mu>"
  for f::"'a\<Rightarrow>'b" and g::"'b\<Rightarrow>'c"
functor map_distr: map_distr using map_distr_id compose_map_distr unfolding o_def id_def by auto

axiomatization where map_distr_uniform[simp]: "bij_betw f A B \<Longrightarrow> map_distr f (uniform A) = uniform B"
  for f::"'a\<Rightarrow>'b" and g::"'b\<Rightarrow>'c"

typedef bit = "UNIV::bool set"..
setup_lifting type_definition_bit
instantiation bit :: field begin
lift_definition times_bit :: "bit \<Rightarrow> bit \<Rightarrow> bit" is "op&".
lift_definition plus_bit :: "bit \<Rightarrow> bit \<Rightarrow> bit" is "op\<noteq>".
lift_definition zero_bit :: bit is "False".
lift_definition one_bit :: bit is "True".
definition[simp]: "uminus_bit (x::bit) = x"
definition[simp]: "minus_bit = (op+ :: bit\<Rightarrow>_\<Rightarrow>_)"
definition[simp]: "inverse_bit (x::bit) = x"
definition[simp]: "divide_bit = (op* :: bit\<Rightarrow>_\<Rightarrow>_)"
instance by intro_classes (transfer; auto)+
end


lemma bit_cases[cases type:bit]: "(x=0 \<Longrightarrow> P) \<Longrightarrow> (x=1 \<Longrightarrow> P) \<Longrightarrow> P" for x :: bit
  by (metis (full_types) Rep_bit_inverse one_bit.abs_eq zero_bit.abs_eq)
lemma bit_two[simp]: "(2::bit) = 0"
  by (metis add_cancel_left_right bit_cases one_add_one) 
lemma bit_eq_x[simp]: "((a=x) = (b=x)) = (a=b)" for a b x :: bit
  apply transfer by auto
lemma bit_neq[simp]: "(a \<noteq> b) = (a = b+1)" for a b :: bit
  apply (cases a rule:bit_cases; cases b rule:bit_cases) by auto

declare [[coercion "\<lambda>b::bit. if b=0 then (0::nat) else 1"]]

lemma bit_plus_1_eq[simp]: "(a+1=b) = (a=b+1)" for a b :: bit
  by auto

lemma bit_plus_2y[simp]: "(x + y) + y = x" for x :: bit
  apply (cases y) by auto

lemma UNIV_bit: "(UNIV::bit set) = {0,1}" by auto

instantiation bit :: enum begin
definition "enum_bit = [0::bit,1]"
definition "enum_all_bit P \<longleftrightarrow> P (0::bit) \<and> P 1"
definition "enum_ex_bit P \<longleftrightarrow> P (0::bit) \<or> P 1"
instance apply intro_classes
  unfolding enum_bit_def enum_all_bit_def enum_ex_bit_def 
     apply auto
  using bit_cases apply metis
  using bit_cases by metis
end

instantiation bit :: equal begin
lift_definition equal_bit :: "bit \<Rightarrow> bit \<Rightarrow> bool" is "HOL.equal :: bool \<Rightarrow> bool \<Rightarrow> bool" .
instance apply intro_classes 
  apply transfer by (rule equal_eq)
end

section \<open>Subspaces\<close>

typedef 'a vector = "{x::'a\<Rightarrow>complex. bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)}"
  by (rule exI[of _ "\<lambda>_.0"], auto)
setup_lifting type_definition_vector

definition "ell2_norm x = (SUP F:{F. finite F}. sum (\<lambda>i. (norm(x i))^2) F)"

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
  assumes "bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)"
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
      using norm0 assms unfolding ell2_norm_def by auto
    then show "x i = 0" by auto
  qed
qed

axiomatization where ell2_norm_triangle:
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
for x :: "'a\<Rightarrow>complex"


lift_definition ket :: "'a \<Rightarrow> 'a vector" is "\<lambda>x y. if x=y then 1 else 0"
  unfolding bdd_above_def apply simp
  apply (rule exI[of _ 1], rule allI, rule impI)
  by (rule ell2_1)

lemma cSUP_eq_maximum:
  fixes z :: "_::conditionally_complete_lattice"
  assumes "\<exists>x\<in>X. f x = z"
  assumes "\<And>x. x \<in> X \<Longrightarrow> f x \<le> z"
  shows "(SUP x:X. f x) = z"
  by (metis (mono_tags, hide_lams) assms(1) assms(2) cSup_eq_maximum imageE image_eqI)


instantiation vector :: (type)real_vector begin
lift_definition zero_vector :: "'a vector" is "\<lambda>_.0" by auto
lift_definition uminus_vector :: "'a vector \<Rightarrow> 'a vector" is uminus by simp
lift_definition plus_vector :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> 'a vector" is "\<lambda>f g x. f x + g x"
proof -
  fix f g :: "'a \<Rightarrow> complex"  fix fun1 fun2 :: "'a \<Rightarrow> complex"

  assume "bdd_above (sum (\<lambda>i. (cmod (f i))\<^sup>2) ` Collect finite)"
  then obtain bf where bf: "\<forall>F. finite F \<longrightarrow> (\<Sum>i\<in>F. (cmod (f i)^2)) \<le> bf" 
    apply atomize_elim unfolding bdd_above_def by auto
  assume "bdd_above (sum (\<lambda>i. (cmod (g i))\<^sup>2) ` Collect finite)"
  then obtain bg where bg: "\<forall>F. finite F \<longrightarrow> (\<Sum>i\<in>F. (cmod (g i)^2)) \<le> bg"
    apply atomize_elim unfolding bdd_above_def by auto

  have cmod: "cmod (a+b)^2 \<le> 2 * ((cmod a)^2 + (cmod b)^2)" for a b
    by (smt cmod_def cmod_power2 norm_triangle_ineq power2_sum sqrt_le_D sum_squares_bound)
         
  define b where "b = 2 * (bf+bg)"
      
  have "\<forall>F. finite F \<longrightarrow> (\<Sum>i\<in>F. (cmod (f i + g i))\<^sup>2) \<le> b"
  proof (rule allI, rule impI)
    fix F :: "'a set" assume "finite F"
    have h1: "(\<Sum>i\<in>F. (cmod (f i + g i))\<^sup>2) \<le> 2 * ((\<Sum>i\<in>F. (cmod (f i))\<^sup>2) + (\<Sum>i\<in>F. (cmod (g i))\<^sup>2))"
      apply (subst sum.distrib[symmetric])
      apply (subst sum_distrib_left)
      apply (rule sum_mono)
      by (rule cmod)
    moreover have h2: "(\<Sum>i\<in>F. (cmod (f i))\<^sup>2) \<le> bf"
      using \<open>finite F\<close> bf by blast
    moreover have h3: "(\<Sum>i\<in>F. (cmod (g i))\<^sup>2) \<le> bg" 
      using \<open>finite F\<close> bg by blast
    ultimately show "(\<Sum>i\<in>F. (cmod (f i + g i))\<^sup>2) \<le> b" unfolding b_def 
      by auto
    qed
    then have "\<exists>b. \<forall>F. finite F \<longrightarrow> (\<Sum>i\<in>F. (cmod (f i + g i))\<^sup>2) \<le> b" by auto
    then show "bdd_above (sum (\<lambda>i. (cmod (f i + g i))\<^sup>2) ` Collect finite)" 
      unfolding bdd_above_def by auto
qed
definition "a - b = a + (-b)" for a b :: "'a vector"
lift_definition scaleR_vector :: "real \<Rightarrow> 'a vector \<Rightarrow> 'a vector" is "\<lambda>r f x. r *\<^sub>R f x"
proof -
  fix f :: "'a \<Rightarrow> complex" and r :: real
  assume "bdd_above (sum (\<lambda>i. (cmod (f i))\<^sup>2) ` Collect finite)"
  (* assume "\<exists>b. \<forall>F. finite F \<longrightarrow> (\<Sum>i\<in>F. (cmod (f i))\<^sup>2) \<le> b" *)
  then obtain b where b: "\<And>F. finite F \<Longrightarrow> (\<Sum>i\<in>F. (cmod (f i))\<^sup>2) \<le> b" 
    apply atomize_elim unfolding bdd_above_def by auto
  have aux: "(r*x)^2 = r^2 * x^2" for r x :: real unfolding power2_eq_square by auto
  have "(\<Sum>i\<in>F. (cmod (r *\<^sub>R f i))\<^sup>2) \<le> \<bar>r\<bar>\<^sup>2 * b" if "finite F" for F
    apply (subst norm_scaleR)
    apply (subst aux)
    apply (subst sum_distrib_left[symmetric])
    apply (subst mult_left_mono)
    by (auto simp: b that)
  then show "bdd_above (sum (\<lambda>i. (cmod (r *\<^sub>R f i))\<^sup>2) ` Collect finite)"
    unfolding bdd_above_def by auto
qed
instance apply intro_classes
          apply (transfer; rule ext; simp)
         apply (transfer; rule ext; simp)
        apply (transfer; rule ext; simp)
       apply (transfer; rule ext; simp)
      apply (unfold minus_vector_def; transfer; rule ext; simp)
     apply (transfer; rule ext; simp add: scaleR_add_right)
    apply (transfer; rule ext; simp add: scaleR_add_left)
   apply (transfer; rule ext; simp)
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
  apply transfer by (fact ell2_norm_mult)
end

axiomatization timesScalarVec :: "complex \<Rightarrow> 'a vector \<Rightarrow> 'a vector" where
  timesScalarVec_twice[simp]: "timesScalarVec a (timesScalarVec b \<psi>) = timesScalarVec (a*b) \<psi>"
and uminus_vector: "(-\<psi>) = timesScalarVec (-1) \<psi>"
and one_times_vec[simp]: "timesScalarVec (1::complex) \<psi> = \<psi>" 
for \<psi> :: "'a vector"

lemma ell2_ket[simp]: "norm (ket i) = 1"
  apply transfer unfolding ell2_norm_def
  apply (rule cSUP_eq_maximum)
  apply (rule_tac x="{i}" in bexI)
    apply auto
  by (rule ell2_1)

axiomatization orthogonal :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> bool"
  where orthogonal_comm: "orthogonal \<psi> \<phi> = orthogonal \<phi> \<psi>"


(* typedef 'a state = "{x::'a vector. norm x = 1}"
  morphisms state_to_vector Abs_state
  apply (rule exI[of _ "ket undefined"])
  by simp
setup_lifting type_definition_state

lift_definition ket :: "'a \<Rightarrow> 'a state" ("|_\<rangle>") is "ket"
  by (rule ell2_ket)

lemma vector_to_state_ket[simp]: "state_to_vector (ket i) = ket i"
  by (rule ket.rep_eq) *)

axiomatization is_subspace :: "'a vector set \<Rightarrow> bool"
  where is_subspace_0[simp]: "is_subspace {0}"
    and is_subspace_UNIV[simp]: "is_subspace UNIV"
    and is_subspace_orthog[simp]: "is_subspace A \<Longrightarrow> is_subspace {\<psi>. (\<forall>\<phi>\<in>A. orthogonal \<psi> \<phi>)}"
    and is_subspace_inter[simp]: "is_subspace A \<Longrightarrow> is_subspace B \<Longrightarrow> is_subspace (A\<inter>B)"
    and is_subspace_plus: "is_subspace A \<Longrightarrow> is_subspace B \<Longrightarrow> is_subspace {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}"
    and is_subspace_contains_0: "is_subspace A \<Longrightarrow> 0 \<in> A"
    and is_subspace_closed_plus: "is_subspace A \<Longrightarrow> x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> (x+y) \<in> A"
    and is_subspace_INF[simp]: "(\<And>x. x \<in> AA \<Longrightarrow> is_subspace x) \<Longrightarrow> is_subspace (\<Inter>AA)"
    (* and is_subspace_spanex[simp]: "\<exists>A. is_subspace A \<and> M \<subseteq> A \<and> (\<forall>B. is_subspace B \<and> M \<subseteq> B \<longrightarrow> B \<subseteq> A)" *)

(* declare[[coercion state_to_vector]] *)

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

term "(sup :: 'a subspace \<Rightarrow> _ \<Rightarrow> _)"

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

section \<open>Measurements\<close>

typedecl ('a,'b) measurement
axiomatization mproj :: "('a,'b) measurement \<Rightarrow> 'a \<Rightarrow> ('b,'b) bounded"
  and mtotal :: "('a,'b) measurement \<Rightarrow> bool"
  where isProjector_mproj[simp]: "isProjector (mproj M i)"

axiomatization computational_basis :: "('a, 'a) measurement" where
  mproj_computational_basis[simp]: "mproj computational_basis x = proj (ket x)"
and mtotal_computational_basis [simp]: "mtotal computational_basis"


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


section \<open>Quantum predicates\<close>
    
typedecl mem2
type_synonym predicate = "mem2 subspace"

subsection \<open>Classical predicates\<close>
  
definition classical_subspace :: "bool \<Rightarrow> predicate"  ("\<CC>\<ll>\<aa>[_]")
  where "\<CC>\<ll>\<aa>[b] = (if b then top else bot)"
syntax classical_subspace :: "bool \<Rightarrow> predicate"  ("Cla[_]")

lemma classical_true[simp]: "Cla[True] = top" unfolding classical_subspace_def by simp
lemma classical_false[simp]: "Cla[False] = bot" unfolding classical_subspace_def by simp
lemma classical_mono[simp]: "(Cla[a] \<le> Cla[b]) = (a \<longrightarrow> b)" 
  apply (cases a, auto, cases b, auto)
  using bot.extremum_uniqueI top_not_bot by blast 
lemma classical_simp1[simp]: 
  shows "(Cla[b] \<le> A) = (b \<longrightarrow> A = top)"
  using top.extremum_unique by fastforce
lemma classical_inf[simp]: "Cla[x] \<sqinter> Cla[y] = Cla[x \<and> y]"
  by (simp add: classical_subspace_def)
lemma classical_sup[simp]: "Cla[x] \<squnion> Cla[y] = Cla[x \<or> y]"
  by (simp add: classical_subspace_def)
lemma classical_simp2[simp]:
  shows "(Cla[a] \<sqinter> B \<le> C) = (a \<longrightarrow> B \<le> C)"
  apply (cases a) by auto
lemma classical_sort[simp]:
  assumes "NO_MATCH Cla[x] A" 
  shows "A \<sqinter> Cla[b] = Cla[b] \<sqinter> A"
  by (simp add: classical_subspace_def)

lemma Cla_split[split]: "P (Cla[Q]) = ((Q \<longrightarrow> P top) \<and> (\<not> Q \<longrightarrow> P bot))"
  by (cases Q, auto) 
lemma classical_ortho[simp]: "ortho Cla[b] = Cla[\<not> b]"
  by auto

lemma applyOp_Cla[simp]:
  assumes "unitary A"
  shows "A \<cdot> Cla[b] = Cla[b]"
  apply (cases b) using assms by auto

lemma Cla_plus[simp]: "Cla[x] + Cla[y] = Cla[x\<or>y]" unfolding sup_subspace_def[symmetric] by auto
lemma BINF_Cla[simp]: "(INF z:Z. Cla[x z]) = Cla[\<forall>z\<in>Z. x z]" 
proof (rule Inf_eqI)
  show "\<And>i. i \<in> (\<lambda>z. \<CC>\<ll>\<aa>[x z]) ` Z \<Longrightarrow> \<CC>\<ll>\<aa>[\<forall>z\<in>Z. x z] \<le> i" by auto
  fix y assume assm: "\<And>i. i \<in> (\<lambda>z. \<CC>\<ll>\<aa>[x z]) ` Z \<Longrightarrow> y \<le> i"
  show "y \<le> \<CC>\<ll>\<aa>[\<forall>z\<in>Z. x z]"
  proof (cases "\<forall>z\<in>Z. x z")
    case True thus ?thesis by auto
  next case False
    then obtain z where "\<not> x z" and "z\<in>Z" by auto
    hence "Cla[x z] = bot" by simp
    hence "bot \<in> (\<lambda>z. \<CC>\<ll>\<aa>[x z]) ` Z"
      using \<open>z \<in> Z\<close> by force
    hence "y \<le> bot" by (rule assm)
    thus ?thesis
      by (simp add: False)
  qed
qed

lemma free_INF[simp]: "(INF x:X. A) = Cla[X={}] + A"
  apply (cases "X={}") by auto

lemma [simp]: "eigenspace b 0 = Cla[b=0]"
  unfolding eigenspace_def apply auto
  apply (rewrite at "kernel \<hole>" DEADID.rel_mono_strong[where y="(-b) \<cdot> idOp"])
  by (auto simp: subspace_zero_bot uminus_bounded_def)

section \<open>Quantum variables\<close>

typedecl 'a qvariable (* a variable, refers to a location in a memory *)
axiomatization variable_name :: "'a qvariable \<Rightarrow> string"
typedecl 'a qvariables (* represents a tuple of variables, of joint type 'a *)

axiomatization
    qvariable_names :: "'a qvariables \<Rightarrow> string list"
and qvariable_concat :: "'a qvariables \<Rightarrow> 'b qvariables \<Rightarrow> ('a * 'b) qvariables"
and qvariable_singleton :: "'a qvariable \<Rightarrow> 'a qvariables"
and qvariable_unit :: "unit qvariables"

nonterminal qvariable_list_args
syntax
  "qvariable_unit"      :: "qvariable_list_args \<Rightarrow> 'a"        ("(1'[[']])")
  "qvariable_unit"      :: "qvariable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>'\<rbrakk>)")
  "_qvariables"      :: "qvariable_list_args \<Rightarrow> 'a"        ("(1'[[_']])")
  "_qvariables"      :: "qvariable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_'\<rbrakk>)")
  "_qvariable_list_arg"  :: "'a \<Rightarrow> qvariable_list_args"                   ("_")
  "_qvariable_list_args" :: "'a \<Rightarrow> qvariable_list_args \<Rightarrow> qvariable_list_args"     ("_,/ _")

translations
  "_qvariables (_qvariable_list_args x y)" \<rightleftharpoons> "CONST qvariable_concat (CONST qvariable_singleton x) (_qvariables y)"
  "_qvariables (_qvariable_list_arg x)" \<rightleftharpoons> "CONST qvariable_singleton x"
  "_qvariables (_qvariable_list_args x y)" \<leftharpoondown> "CONST qvariable_concat (_qvariables (_qvariable_list_arg x)) (_qvariables y)"
  

axiomatization where
  qvariable_names_cons[simp]: "qvariable_names (qvariable_concat X Y) = qvariable_names X @ qvariable_names Y"
  and qvariable_singleton_name[simp]: "qvariable_names (qvariable_singleton x) = [variable_name x]"
  and qvariable_unit_name[simp]: "qvariable_names qvariable_unit = []"
  for X::"'a qvariables" and Y::"'b qvariables" and x::"'c qvariable"

subsection "Distinct quantum variables"


axiomatization distinct_qvars :: "'a qvariables \<Rightarrow> bool"
axiomatization colocal_pred_qvars :: "predicate \<Rightarrow> 'a qvariables \<Rightarrow> bool"
  and colocal_op_pred :: "(mem2,mem2) bounded \<Rightarrow> predicate \<Rightarrow> bool"
  and colocal_op_qvars :: "(mem2,mem2) bounded \<Rightarrow> 'a qvariables \<Rightarrow> bool"

consts colocal :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
adhoc_overloading colocal colocal_pred_qvars colocal_op_pred colocal_op_qvars (* colocal_qvars_qvars *)

axiomatization where colocal_qvariable_names[simp]:
  "distinct (qvariable_names Q) \<Longrightarrow> distinct_qvars Q" 
  for Q :: "'a qvariables"

axiomatization where
  colocal_top[simp]: "colocal top Q"
  and colocal_bot[simp]: "colocal bot Q"
  and colocal_inf[simp]: "colocal A Q \<Longrightarrow> colocal B Q \<Longrightarrow> colocal (A \<sqinter> B) Q"
  and colocal_sup[simp]: "colocal A Q \<Longrightarrow> colocal B Q \<Longrightarrow> colocal (A \<squnion> B) Q"
  and colocal_plus[simp]: "colocal A Q \<Longrightarrow> colocal B Q \<Longrightarrow> colocal (A + B) Q"
  and colocal_Cla[simp]: "colocal (Cla[b]) Q"
for Q :: "'a qvariables"


axiomatization where colocal_pred_qvars_mult[simp]:
  "colocal_op_qvars U Q \<Longrightarrow> colocal_pred_qvars S Q \<Longrightarrow> colocal_pred_qvars (U\<cdot>S) Q"
for Q :: "'a qvariables"

axiomatization where colocal_ortho[simp]: "colocal (ortho S) Q = colocal S Q"
  for Q :: "'a qvariables"

axiomatization where distinct_qvars_split1: 
  "distinct_qvars (qvariable_concat (qvariable_concat Q R) S) = (distinct_qvars (qvariable_concat Q R) \<and> distinct_qvars (qvariable_concat Q S) \<and> distinct_qvars (qvariable_concat R S))"
  for Q::"'a qvariables" and R::"'b qvariables" and S::"'c qvariables"
axiomatization where distinct_qvars_split2: "distinct_qvars (qvariable_concat S (qvariable_concat Q R)) = (distinct_qvars (qvariable_concat Q R) \<and> distinct_qvars (qvariable_concat Q S) \<and> distinct_qvars (qvariable_concat R S))"
  for Q::"'a qvariables" and R::"'b qvariables" and S::"'c qvariables"
axiomatization where distinct_qvars_swap: "distinct_qvars (qvariable_concat Q R) \<Longrightarrow> distinct_qvars (qvariable_concat R Q)" for Q::"'a qvariables" and R::"'b qvariables"
axiomatization where distinct_qvars_concat_unit1[simp]: "distinct_qvars (qvariable_concat Q \<lbrakk>\<rbrakk>) = distinct_qvars Q" for Q::"'a qvariables" 
axiomatization where distinct_qvars_concat_unit2[simp]: "distinct_qvars (qvariable_concat \<lbrakk>\<rbrakk> Q) = distinct_qvars Q" for Q::"'a qvariables" 
axiomatization where distinct_qvars_unit[simp]: "distinct_qvars \<lbrakk>\<rbrakk>" for Q::"'a qvariables" 
axiomatization where distinct_qvars_single[simp]: "distinct_qvars \<lbrakk>q\<rbrakk>" for q::"'a qvariable"

lemma distinct_qvarsL: "distinct_qvars (qvariable_concat Q R) \<Longrightarrow> distinct_qvars Q"
  by (meson distinct_qvars_concat_unit1 distinct_qvars_split1)
lemma distinct_qvarsR: "distinct_qvars (qvariable_concat Q R) \<Longrightarrow> distinct_qvars R"
  by (meson distinct_qvars_concat_unit1 distinct_qvars_split1)

subsection \<open>Lifting\<close>
  
axiomatization
    liftOp :: "('a,'a) bounded \<Rightarrow> 'a qvariables \<Rightarrow> (mem2,mem2) bounded"
and liftSpace :: "'a subspace \<Rightarrow> 'a qvariables \<Rightarrow> predicate"


consts lift :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" ("_\<guillemotright>_"  [91,91] 90)
syntax lift :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" ("_>>_"  [91,91] 90)
adhoc_overloading
  lift liftOp liftSpace

axiomatization where 
    adjoint_lift[simp]: "adjoint (liftOp U Q) = liftOp (adjoint U) Q" 
and imageOp_lift[simp]: "applyOpSpace (liftOp U Q) top = liftSpace (applyOpSpace U top) Q"
and applyOpSpace_lift[simp]: "applyOpSpace (liftOp U Q) (liftSpace S Q) = liftSpace (applyOpSpace U S) Q"
and top_lift[simp]: "liftSpace top Q = top"
and bot_lift[simp]: "liftSpace bot Q = bot"
and unitary_lift[simp]: "unitary (liftOp U Q) = unitary U"
for U :: "('a,'a) bounded"

axiomatization where lift_inf[simp]: "distinct_qvars Q \<Longrightarrow> S\<guillemotright>Q \<sqinter> T\<guillemotright>Q = (S \<sqinter> T)\<guillemotright>Q" for S::"'a subspace"
axiomatization where lift_leq[simp]: "distinct_qvars Q \<Longrightarrow> (S\<guillemotright>Q \<le> T\<guillemotright>Q) = (S \<le> T)" for S::"'a subspace"
axiomatization where lift_eqSp[simp]: "distinct_qvars Q \<Longrightarrow> (S\<guillemotright>Q = T\<guillemotright>Q) = (S = T)" for S T :: "'a subspace" 
axiomatization where lift_eqOp[simp]: "distinct_qvars Q \<Longrightarrow> (S\<guillemotright>Q = T\<guillemotright>Q) = (S = T)" for S T :: "('a,'a) bounded" 
axiomatization where lift_timesScalarOp[simp]: "distinct_qvars Q \<Longrightarrow> a \<cdot> (A\<guillemotright>Q) = (a \<cdot> A)\<guillemotright>Q" for a::complex and A::"('a,'a)bounded"
axiomatization where lift_plus[simp]: "distinct_qvars Q \<Longrightarrow> S\<guillemotright>Q + T\<guillemotright>Q = (S + T)\<guillemotright>Q" for S T :: "'a subspace"  
axiomatization where lift_plusOp[simp]: "distinct_qvars Q \<Longrightarrow> S\<guillemotright>Q + T\<guillemotright>Q = (S + T)\<guillemotright>Q" for S T :: "('a,'a) bounded"  
lemma lift_uminusOp[simp]: "distinct_qvars Q \<Longrightarrow> - (T\<guillemotright>Q) = (- T)\<guillemotright>Q" for T :: "('a,'a) bounded"  
  unfolding uminus_bounded_def by simp
lemma lift_minusOp[simp]: "distinct_qvars Q \<Longrightarrow> S\<guillemotright>Q - T\<guillemotright>Q = (S - T)\<guillemotright>Q" for S T :: "('a,'a) bounded"  
  unfolding minus_bounded_def by simp
axiomatization where lift_timesOp[simp]: "distinct_qvars Q \<Longrightarrow> S\<guillemotright>Q \<cdot> T\<guillemotright>Q = (S \<cdot> T)\<guillemotright>Q" for S T :: "('a,'a) bounded"  
axiomatization where lift_ortho[simp]: "distinct_qvars Q \<Longrightarrow> ortho (S\<guillemotright>Q) = (ortho S)\<guillemotright>Q" for Q :: "'a qvariables"
axiomatization where lift_tensorOp: "distinct_qvars (qvariable_concat Q R) \<Longrightarrow> (S\<guillemotright>Q) \<cdot> (T\<guillemotright>R) = (S \<otimes> T)\<guillemotright>qvariable_concat Q R" for Q :: "'a qvariables" and R :: "'b qvariables" and S T :: "(_,_) bounded" 
axiomatization where lift_tensorSpace: "distinct_qvars (qvariable_concat Q R) \<Longrightarrow> (S\<guillemotright>Q) = (S \<otimes> top)\<guillemotright>qvariable_concat Q R" for Q :: "'a qvariables" and R :: "'b qvariables" and S :: "_ subspace" 
axiomatization where lift_idOp[simp]: "idOp\<guillemotright>Q = idOp" for Q :: "'a qvariables"
axiomatization where INF_lift: "distinct_qvars Q \<Longrightarrow> (INF x. S x\<guillemotright>Q) = (INF x. S x)\<guillemotright>Q" for Q::"'a qvariables" and S::"'b \<Rightarrow> 'a subspace"
lemma Cla_inf_lift: "distinct_qvars Q \<Longrightarrow> Cla[b] \<sqinter> (S\<guillemotright>Q) = (if b then S else bot)\<guillemotright>Q" by auto
lemma Cla_plus_lift: "distinct_qvars Q \<Longrightarrow> Cla[b] + (S\<guillemotright>Q) = (if b then top else S)\<guillemotright>Q" by auto
axiomatization where Proj_lift[simp]: "distinct_qvars Q \<Longrightarrow> Proj (S\<guillemotright>Q) = (Proj S)\<guillemotright>Q"
  for Q::"'a qvariables"
axiomatization where kernel_lift[simp]: "distinct_qvars Q \<Longrightarrow> kernel (A\<guillemotright>Q) = (kernel A)\<guillemotright>Q" for Q::"'a qvariables"
lemma eigenspace_lift[simp]: "distinct_qvars Q \<Longrightarrow> eigenspace a (A\<guillemotright>Q) = (eigenspace a A)\<guillemotright>Q" for Q::"'a qvariables"
  unfolding eigenspace_def apply (subst lift_idOp[symmetric, of Q]) by (simp del: lift_idOp)

axiomatization where remove_qvar_unit_op:
  "(remove_qvar_unit_op \<cdot> A \<cdot> remove_qvar_unit_op*)\<guillemotright>Q = A\<guillemotright>(qvariable_concat Q \<lbrakk>\<rbrakk>)"
for A::"(_,_)bounded" and Q::"'a qvariables"


axiomatization where colocal_op_pred_lift1[simp]:
 "colocal S Q \<Longrightarrow> colocal (U\<guillemotright>Q) S"
for Q :: "'a qvariables" and U :: "('a,'a) bounded" and S :: predicate

axiomatization where colocal_op_qvars_lift1[simp]:
  "distinct_qvars (qvariable_concat Q R) \<Longrightarrow> colocal (U\<guillemotright>Q) R"
for Q :: "'a qvariables" and R :: "'b qvariables" and U :: "('a,'a) bounded"  

axiomatization where colocal_pred_qvars_lift1[simp]:
  "distinct_qvars (qvariable_concat Q R) \<Longrightarrow> colocal_pred_qvars (S\<guillemotright>Q) R"
for Q :: "'a qvariables" and R :: "'b qvariables"

lemma lift_extendR:
  assumes "distinct_qvars (qvariable_concat Q R)"
  shows "U\<guillemotright>Q = (U\<otimes>idOp)\<guillemotright>(qvariable_concat Q R)"
  by (metis assms lift_idOp lift_tensorOp times_idOp1)

lemma lift_extendL:
  assumes "distinct_qvars (qvariable_concat Q R)"
  shows "U\<guillemotright>Q = (idOp\<otimes>U)\<guillemotright>(qvariable_concat R Q)"
  by (metis assms distinct_qvars_swap lift_idOp lift_tensorOp times_idOp2)

lemma move_plus_meas_rule:
  fixes Q::"'a qvariables"
  assumes "distinct_qvars Q"
  assumes "(Proj C)\<guillemotright>Q \<cdot> A \<le> B"
  shows "A \<le> (B\<sqinter>C\<guillemotright>Q) + (ortho C)\<guillemotright>Q"
  apply (rule move_plus) 
  using Proj_leq[of "C\<guillemotright>Q"] assms by simp


subsection "Rewriting quantum variable lifting"


(* Means that operator A can be used to transform an expression \<dots>\<guillemotright>Q into \<dots>\<guillemotright>R *)
definition "qvar_trafo A Q R = (distinct_qvars Q \<and> distinct_qvars R \<and> (\<forall>C::(_,_)bounded. C\<guillemotright>Q = (A\<cdot>C\<cdot>A*)\<guillemotright>R))" for A::"('a,'b) bounded"

lemma qvar_trafo_id[simp]: "distinct_qvars Q \<Longrightarrow> qvar_trafo idOp Q Q" unfolding qvar_trafo_def by auto

(* Auxiliary lemma, will be removed after generalizing to qvar_trafo_unitary *)
lemma qvar_trafo_coiso: assumes "qvar_trafo A Q R" shows "A \<cdot> A* = idOp"
proof -
  have colocalQ: "distinct_qvars Q" and colocalR: "distinct_qvars R" using assms unfolding qvar_trafo_def by auto
  have "idOp\<guillemotright>Q = (A \<cdot> idOp \<cdot> A*)\<guillemotright>R"
    using assms unfolding qvar_trafo_def by auto 
  hence "idOp\<guillemotright>R = (A \<cdot> A*)\<guillemotright>R" by auto
  hence "idOp = A \<cdot> A*" apply (subst lift_eqOp[symmetric])
    using colocalR by auto
  then show ?thesis ..
qed

lemma qvar_trafo_adj[simp]: assumes "qvar_trafo A Q R" shows "qvar_trafo (A*) R Q"
proof (unfold qvar_trafo_def, auto)
  show colocalQ: "distinct_qvars Q" and colocalR: "distinct_qvars R" using assms unfolding qvar_trafo_def by auto
  show "C\<guillemotright>R = (A* \<cdot> C \<cdot> A)\<guillemotright>Q" for C::"(_,_)bounded"
  proof -
    have "(A* \<cdot> C \<cdot> A)\<guillemotright>Q = (A \<cdot> (A* \<cdot> C \<cdot> A) \<cdot> A*)\<guillemotright>R"
      using assms unfolding qvar_trafo_def by auto 
    also have "\<dots> = ((A \<cdot> A*) \<cdot> C \<cdot> (A \<cdot> A*)*)\<guillemotright>R"
      by (simp add: timesOp_assoc)
    also have "\<dots> = C\<guillemotright>R" apply (subst qvar_trafo_coiso[OF assms])+ by auto 
    finally show ?thesis ..
  qed
qed

lemma qvar_trafo_unitary:
  assumes "qvar_trafo A Q R"
  shows "unitary A"
proof -
  have "qvar_trafo (A*) R Q"
    using assms by (rule qvar_trafo_adj)
  hence "(A*) \<cdot> (A*)* = idOp" by (rule qvar_trafo_coiso)
  hence "A* \<cdot> A = idOp" by simp
  also have "A \<cdot> A* = idOp"
    using assms by (rule qvar_trafo_coiso)
  ultimately show ?thesis unfolding unitary_def by simp
qed

hide_fact qvar_trafo_coiso (* Subsumed by qvar_trafo_unitary *)

axiomatization where assoc_op_lift: "(assoc_op \<cdot> A \<cdot> assoc_op*)\<guillemotright>(qvariable_concat (qvariable_concat Q R) T)
     = A\<guillemotright>(qvariable_concat Q (qvariable_concat R T))" for A::"('a*'b*'c,_)bounded" 
axiomatization where comm_op_lift: "(comm_op \<cdot> A \<cdot> comm_op*)\<guillemotright>(qvariable_concat Q R)
     = A\<guillemotright>(qvariable_concat R Q)" for A::"('a*'b,_)bounded" 
axiomatization where lift_tensor_id: "distinct_qvars (qvariable_concat Q R) \<Longrightarrow> distinct_qvars (qvariable_concat Q R) \<Longrightarrow>
   (\<And>D::(_,_) bounded. (A \<cdot> D \<cdot> A*)\<guillemotright>Q = D\<guillemotright>Q') \<Longrightarrow> (\<And>D::(_,_) bounded. (A' \<cdot> D \<cdot> A'*)\<guillemotright>R = D\<guillemotright>R') \<Longrightarrow> 
  ((A\<otimes>A') \<cdot> C \<cdot> (A\<otimes>A')*)\<guillemotright>qvariable_concat Q R = C\<guillemotright>qvariable_concat Q' R'"
  for A :: "('a,'b) bounded" and A' :: "('c,'d) bounded" and C::"(_,_) bounded" and Q R :: "_ qvariables"


lemma qvar_trafo_assoc_op[simp]:
  assumes "distinct_qvars (qvariable_concat Q (qvariable_concat R T))"
  shows "qvar_trafo assoc_op (qvariable_concat Q (qvariable_concat R T))  (qvariable_concat (qvariable_concat Q R) T)"
proof (unfold qvar_trafo_def, auto)
  show "distinct_qvars (qvariable_concat Q (qvariable_concat R T))" and "distinct_qvars (qvariable_concat (qvariable_concat Q R) T)"
    using assms by (auto intro: distinct_qvars_swap simp: distinct_qvars_split1 distinct_qvars_split2)
  show "C\<guillemotright>qvariable_concat Q (qvariable_concat R T) = (assoc_op \<cdot> C \<cdot> assoc_op*)\<guillemotright>qvariable_concat (qvariable_concat Q R) T" for C::"(_,_)bounded"
    by (rule assoc_op_lift[symmetric])
qed


lemma qvar_trafo_comm_op[simp]:
  assumes "distinct_qvars (qvariable_concat Q R)"
  shows "qvar_trafo comm_op (qvariable_concat Q R) (qvariable_concat R Q)"
proof (unfold qvar_trafo_def, auto simp del: adj_comm_op)
  show "distinct_qvars (qvariable_concat Q R)" and "distinct_qvars (qvariable_concat R Q)"
    using assms by (auto intro: distinct_qvars_swap)
  show "C\<guillemotright>qvariable_concat Q R = (comm_op \<cdot> C \<cdot> comm_op*)\<guillemotright>qvariable_concat R Q" for C::"(_,_)bounded"
    by (rule comm_op_lift[symmetric])
qed

lemma qvar_trafo_bounded:
  fixes C::"(_,_) bounded"
  assumes "qvar_trafo A Q R"
  shows "C\<guillemotright>Q = (A\<cdot>C\<cdot>A*)\<guillemotright>R"
  using assms unfolding qvar_trafo_def by auto

lemma qvar_trafo_subspace:
  fixes S::"'a subspace"
  assumes "qvar_trafo A Q R"
  shows "S\<guillemotright>Q = (A\<cdot>S)\<guillemotright>R"
proof -
  define C where "C = Proj S"
  have "S\<guillemotright>Q = (Proj S \<cdot> top)\<guillemotright>Q" by simp
  also have "\<dots> = (Proj S)\<guillemotright>Q \<cdot> top" by simp
  also have "\<dots> = (A \<cdot> Proj S \<cdot> A*)\<guillemotright>R \<cdot> top"
    apply (subst qvar_trafo_bounded) using assms by auto
  also have "\<dots> = (Proj (A\<cdot>S))\<guillemotright>R \<cdot> top" apply (subst Proj_times) by simp
  also have "\<dots> = (Proj (A\<cdot>S) \<cdot> top)\<guillemotright>R" by auto
  also have "\<dots> = (A\<cdot>S)\<guillemotright>R" by auto
  ultimately show ?thesis by simp
qed

lemma qvar_trafo_mult:
  assumes "qvar_trafo A Q R"
    and "qvar_trafo B R S"
  shows "qvar_trafo (B\<cdot>A) Q S"
proof (unfold qvar_trafo_def, auto)
  show colocalQ: "distinct_qvars Q" and colocalS: "distinct_qvars S" using assms unfolding qvar_trafo_def by auto
  show "C\<guillemotright>Q = (B \<cdot> A \<cdot> C \<cdot> (A* \<cdot> B*))\<guillemotright>S" for C::"(_,_) bounded"
  proof -
    have "C\<guillemotright>Q = (A \<cdot> C \<cdot> A*)\<guillemotright>R" apply (rule qvar_trafo_bounded) using assms by simp
    also have "\<dots> = (B \<cdot> (A \<cdot> C \<cdot> A*) \<cdot> B*)\<guillemotright>S" apply (rule qvar_trafo_bounded) using assms by simp
    also have "\<dots> = (B \<cdot> A \<cdot> C \<cdot> (A* \<cdot> B*))\<guillemotright>S" using timesOp_assoc by metis
    finally show ?thesis .
  qed
qed

lemma qvar_trafo_tensor:
  assumes "distinct_qvars (qvariable_concat Q Q')"
    and "distinct_qvars (qvariable_concat R R')"
    and "qvar_trafo A Q R"
    and "qvar_trafo A' Q' R'"
  shows "qvar_trafo (A\<otimes>A') (qvariable_concat Q Q') (qvariable_concat R R')"
proof (unfold qvar_trafo_def, (rule conjI[rotated])+, rule allI)
  show "distinct_qvars (qvariable_concat Q Q')" and "distinct_qvars (qvariable_concat R R')"
    using assms unfolding qvar_trafo_def by auto
  show "C\<guillemotright>qvariable_concat Q Q' = ((A \<otimes> A') \<cdot> C \<cdot> (A \<otimes> A')*)\<guillemotright>qvariable_concat R R'" for C::"(_,_)bounded"
    apply (rule lift_tensor_id[symmetric])
    using assms unfolding qvar_trafo_def by auto
qed



(* A hint to the simplifier with the meaning:
     - x is a term of the form x'>>Q (where x' is of type subspace or bounded)
     - qvar_trafo A Q R holds (i.e., should be produced as a precondition when rewriting)
     - the whole term should be rewritten into y'>>R for some y' 
  Rewriting the term is done by the simplifier rules declared below.
*)
definition "qvariable_renaming_hint x (A::('a,'b) bounded) (R::'b qvariables) = x"
lemma [cong]: "x=x' \<Longrightarrow> qvariable_renaming_hint x A R = qvariable_renaming_hint x' A R" by simp

(* A copy of qvars_trafo that is protected from unintentional rewriting *)
definition "qvar_trafo_protected = qvar_trafo"
lemma [cong]: "qvar_trafo_protected A Q R = qvar_trafo_protected A Q R" ..

lemma qvariable_renaming_hint_subspace[simp]:
  fixes S::"_ subspace"
  assumes "qvar_trafo_protected A Q R"
  shows "qvariable_renaming_hint (S\<guillemotright>Q) A R = (A\<cdot>S)\<guillemotright>R"
  using assms unfolding qvariable_renaming_hint_def qvar_trafo_protected_def by (rule qvar_trafo_subspace)

lemma qvariable_renaming_hint_bounded[simp]:
  fixes S::"(_,_) bounded"
  assumes "qvar_trafo_protected A Q R"
  shows "qvariable_renaming_hint (S\<guillemotright>Q) A R = (A\<cdot>S\<cdot>A*)\<guillemotright>R"
  using assms unfolding qvariable_renaming_hint_def qvar_trafo_protected_def by (rule qvar_trafo_bounded)

(* A hint to the simplifier with the meaning:
     - x is a term of the form x'>>Q (where x' is of type subspace or bounded)
     - colocal Q R holds (i.e., should be produced as a precondition when rewriting)
     - the whole term should be rewritten into y'>>qvariable_concat Q R for some y'
  Rewriting the term is done by the qvariable_rewriting simproc.
 *)
definition "qvariable_extension_hint x (R::_ qvariables) = x"


lemma qvariable_extension_hint_subspace[simp]:
  fixes S::"_ subspace"
  assumes "distinct_qvars (qvariable_concat Q R)"
  shows "qvariable_extension_hint (S\<guillemotright>Q) R = (S\<otimes>top)\<guillemotright>qvariable_concat Q R"
  unfolding qvariable_extension_hint_def 
  using assms by (rule lift_tensorSpace)

lemma qvariable_extension_hint_bounded[simp]:
  fixes S::"(_,_) bounded"
  assumes "distinct_qvars (qvariable_concat Q R)"
  shows "qvariable_extension_hint (S\<guillemotright>Q) R = (S\<otimes>idOp)\<guillemotright>qvariable_concat Q R"
  unfolding qvariable_extension_hint_def 
  using assms
  by (metis lift_idOp lift_tensorOp times_idOp1)


(* Hint for the simplifier, meaning that:
    - x is of the form x'\<guillemotright>Q
    - colocal Q [], colocal R [] holds
    - the whole expression should be rewritten to x'\<guillemotright>Q\<otimes>R' such that Q\<otimes>R' has the same variables as Q\<otimes>R (duplicates removed)
  Rewriting the term is done by the simplifier rules declared below.
*)
definition "join_qvariables_hint x (R::'a qvariables) = x"

lemma add_join_qvariables_hint: 
  fixes Q :: "'a qvariables" and R :: "'b qvariables" 
    and S :: "'a subspace" and T :: "'b subspace"
    and A :: "('a,'a) bounded" and B :: "('b,'b) bounded"
  shows "NO_MATCH (a,a) (Q,R) \<Longrightarrow> S\<guillemotright>Q \<sqinter> T\<guillemotright>R = join_qvariables_hint (S\<guillemotright>Q) R \<sqinter> join_qvariables_hint (T\<guillemotright>R) Q"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> S\<guillemotright>Q + T\<guillemotright>R = join_qvariables_hint (S\<guillemotright>Q) R + join_qvariables_hint (T\<guillemotright>R) Q"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> A\<guillemotright>Q \<cdot> T\<guillemotright>R = join_qvariables_hint (A\<guillemotright>Q) R \<cdot> join_qvariables_hint (T\<guillemotright>R) Q"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (S\<guillemotright>Q \<le> T\<guillemotright>R) = (join_qvariables_hint (S\<guillemotright>Q) R \<le> join_qvariables_hint (T\<guillemotright>R) Q)"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (S\<guillemotright>Q = T\<guillemotright>R) = (join_qvariables_hint (S\<guillemotright>Q) R = join_qvariables_hint (T\<guillemotright>R) Q)"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (A\<guillemotright>Q = B\<guillemotright>R) = (join_qvariables_hint (A\<guillemotright>Q) R = join_qvariables_hint (B\<guillemotright>R) Q)"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (A\<guillemotright>Q + B\<guillemotright>R) = (join_qvariables_hint (A\<guillemotright>Q) R + join_qvariables_hint (B\<guillemotright>R) Q)"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (A\<guillemotright>Q - B\<guillemotright>R) = (join_qvariables_hint (A\<guillemotright>Q) R - join_qvariables_hint (B\<guillemotright>R) Q)"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (A\<guillemotright>Q \<cdot> B\<guillemotright>R) = (join_qvariables_hint (A\<guillemotright>Q) R \<cdot> join_qvariables_hint (B\<guillemotright>R) Q)"
  unfolding join_qvariables_hint_def by simp_all



(* Hint for the simplifier, meaning that:
    - x is of the form x'>>Q
    - colocal Q [[]] holds
    - the whole expression should be rewritten to y'>>Q' where Q' is a sorted qvariable list
  Rewriting the term is done by the qvariable_rewriting simproc.
 *)
definition "sort_qvariables_hint x = x"

lemma join_qvariables_hint_subspace_conv_aux:
  "join_qvariables_hint (S\<guillemotright>Q) R \<equiv> sort_qvariables_hint (qvariable_extension_hint (S\<guillemotright>Q) R')" for S::"_ subspace"
  unfolding join_qvariables_hint_def qvariable_extension_hint_def sort_qvariables_hint_def by simp

lemma join_qvariables_hint_bounded_conv_aux:
  "join_qvariables_hint (S\<guillemotright>Q) R \<equiv> sort_qvariables_hint (qvariable_extension_hint (S\<guillemotright>Q) R')" for S::"(_,_) bounded"
  unfolding join_qvariables_hint_def qvariable_extension_hint_def sort_qvariables_hint_def by simp

lemma sort_qvariables_hint_subspace_conv_aux:
  "sort_qvariables_hint (S\<guillemotright>Q) \<equiv> qvariable_renaming_hint (S\<guillemotright>Q) A R'" for S::"_ subspace"
  unfolding qvariable_renaming_hint_def sort_qvariables_hint_def by simp

lemma sort_qvariables_hint_bounded_conv_aux:
  "sort_qvariables_hint (S\<guillemotright>Q) \<equiv> qvariable_renaming_hint (S\<guillemotright>Q) A R'" for S::"(_,_) bounded"
  unfolding qvariable_renaming_hint_def sort_qvariables_hint_def by simp

lemma sort_qvariables_hint_remove_aux: "sort_qvariables_hint x \<equiv> x" 
  unfolding sort_qvariables_hint_def by simp


(* For convenience in ML code *)
definition [simp]: "comm_op_pfx = assoc_op* \<cdot> (comm_op\<otimes>idOp) \<cdot> assoc_op"
definition [simp]: "id_tensor A = idOp\<otimes>A"
definition [simp]: "assoc_op_adj = assoc_op*"
definition [simp]: "remove_qvar_unit_op2 = remove_qvar_unit_op \<cdot> comm_op"
definition [simp]: "qvar_trafo_mult (Q::'b qvariables) (B::('b,'c)bounded) (A::('a,'b)bounded) = timesOp B A"


lemma qvar_trafo_protected_mult[simp]: 
  "qvar_trafo_protected A Q R \<Longrightarrow> qvar_trafo_protected B R S \<Longrightarrow> qvar_trafo_protected (qvar_trafo_mult R B A) Q S"
  unfolding qvar_trafo_protected_def apply simp by (rule qvar_trafo_mult)

lemma qvar_trafo_protected_adj_assoc_op[simp]:
  "distinct_qvars (qvariable_concat Q (qvariable_concat R T)) \<Longrightarrow>
    qvar_trafo_protected assoc_op_adj (qvariable_concat (qvariable_concat Q R) T)
                                      (qvariable_concat Q (qvariable_concat R T))"
  unfolding qvar_trafo_protected_def by simp 

lemma qvar_trafo_protected_assoc_op[simp]:
  "distinct_qvars (qvariable_concat Q (qvariable_concat R T)) \<Longrightarrow>
    qvar_trafo_protected assoc_op (qvariable_concat Q (qvariable_concat R T))
                                  (qvariable_concat (qvariable_concat Q R) T)"
  unfolding qvar_trafo_protected_def by simp 

lemma qvar_trafo_protected_comm_op_pfx[simp]:
  assumes [simp]: "distinct_qvars (qvariable_concat Q (qvariable_concat R T))"
  shows "qvar_trafo_protected comm_op_pfx
         (qvariable_concat Q (qvariable_concat R T))
         (qvariable_concat R (qvariable_concat Q T))"
proof -
  have [simp]: "distinct_qvars (qvariable_concat Q R)" 
   and [simp]: "distinct_qvars (qvariable_concat (qvariable_concat R Q) T)"
   and [simp]: "distinct_qvars (qvariable_concat (qvariable_concat Q R) T)"
   and [simp]: "distinct_qvars (qvariable_concat R (qvariable_concat Q T)) "
   and [simp]: "distinct_qvars T" 
    using assms by (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro: distinct_qvars_swap distinct_qvarsL)
  show ?thesis
  unfolding qvar_trafo_protected_def comm_op_pfx_def
  apply (rule qvar_trafo_mult[where R="qvariable_concat (qvariable_concat Q R) T"])
   apply simp
  apply (rule qvar_trafo_mult[where R="qvariable_concat (qvariable_concat R Q) T"])
   apply (rule qvar_trafo_tensor)
  by simp_all
qed

lemma qvar_trafo_protected_remove_qvar_unit_op[simp]:
  assumes "distinct_qvars Q"
  shows "qvar_trafo_protected (remove_qvar_unit_op) (qvariable_concat Q \<lbrakk>\<rbrakk>) Q"
  unfolding qvar_trafo_protected_def qvar_trafo_def
  by (auto simp: assms remove_qvar_unit_op)

lemma qvar_trafo_protected_remove_qvar_unit_op2[simp]:
  assumes [simp]: "distinct_qvars Q"
  shows "qvar_trafo_protected (remove_qvar_unit_op2) (qvariable_concat \<lbrakk>\<rbrakk> Q) Q"
  unfolding qvar_trafo_protected_def remove_qvar_unit_op2_def
  apply (rule qvar_trafo_mult)
   apply (rule qvar_trafo_comm_op)
   apply simp
  unfolding qvar_trafo_def
  by (auto simp: remove_qvar_unit_op)


lemma qvar_trafo_protecterd_id_tensor[simp]:
  assumes [simp]: "distinct_qvars (qvariable_concat Q R)" and [simp]: "distinct_qvars (qvariable_concat Q R')"
    and "qvar_trafo_protected A R R'"
  shows "qvar_trafo_protected (id_tensor A) (qvariable_concat Q R) (qvariable_concat Q R')"
  unfolding qvar_trafo_protected_def id_tensor_def
  apply (rule qvar_trafo_tensor)
     apply simp_all[2]
   apply (rule qvar_trafo_id)
  using assms(2) apply (rule distinct_qvarsL) 
  using assms(3) unfolding qvar_trafo_protected_def by assumption

lemma qvar_trafo_protecterd_comm_op[simp]:
  assumes [simp]: "distinct_qvars (qvariable_concat Q R)"
  shows "qvar_trafo_protected comm_op (qvariable_concat Q R) (qvariable_concat R Q)"
  unfolding qvar_trafo_protected_def by simp                                                  
 

section \<open>Quantum predicates (ctd.)\<close>

subsection \<open>Subspace division\<close>

axiomatization space_div :: "predicate \<Rightarrow> 'a vector \<Rightarrow> 'a qvariables \<Rightarrow> predicate"
                    ("_ \<div> _\<guillemotright>_" [89,89,89] 90)
  where leq_space_div[simp]: "colocal A Q \<Longrightarrow> (A \<le> B \<div> \<psi>\<guillemotright>Q) = (A \<sqinter> span {\<psi>}\<guillemotright>Q \<le> B)"


subsection \<open>Quantum equality\<close>

definition quantum_equality_full :: "('a,'c) bounded \<Rightarrow> 'a qvariables \<Rightarrow> ('b,'c) bounded \<Rightarrow> 'b qvariables \<Rightarrow> predicate" where
  "quantum_equality_full U Q V R = 
                 (eigenspace 1 (comm_op \<cdot> (V*\<cdot>U)\<otimes>(U*\<cdot>V))) \<guillemotright> qvariable_concat Q R"
  for Q :: "'a qvariables" and R :: "'b qvariables"
  and U V :: "(_,'c) bounded"

abbreviation "quantum_equality" :: "'a qvariables \<Rightarrow> 'a qvariables \<Rightarrow> predicate" (infix "\<equiv>\<qq>" 100)
  where "quantum_equality X Y \<equiv> quantum_equality_full idOp X idOp Y"
syntax quantum_equality :: "'a qvariables \<Rightarrow> 'a qvariables \<Rightarrow> predicate" (infix "==q" 100)
syntax "_quantum_equality" :: "qvariable_list_args \<Rightarrow> qvariable_list_args \<Rightarrow> predicate" ("Qeq'[_=_']")
translations
  "_quantum_equality a b" \<rightharpoonup> "CONST quantum_equality (_qvariables a) (_qvariables b)"

lemma quantum_equality_sym:
  assumes "distinct_qvars (qvariable_concat Q R)"
  shows "quantum_equality_full U Q V R = quantum_equality_full V R U Q"
proof -
  have dist: "distinct_qvars (qvariable_concat R Q)"
    using assms by (rule distinct_qvars_swap)
  have a: "comm_op \<cdot> ((V* \<cdot> U) \<otimes> (U* \<cdot> V)) \<cdot> comm_op* = (U* \<cdot> V) \<otimes> (V* \<cdot> U)" by simp
  have op_eq: "((comm_op \<cdot> (V* \<cdot> U) \<otimes> (U* \<cdot> V))\<guillemotright>qvariable_concat Q R) =
               ((comm_op \<cdot> (U* \<cdot> V) \<otimes> (V* \<cdot> U))\<guillemotright>qvariable_concat R Q)"
    apply (subst comm_op_lift[symmetric])
    using a by (simp add: assoc_right)
  show ?thesis
    apply (subst quantum_equality_full_def)
    apply (subst quantum_equality_full_def)
    apply (subst eigenspace_lift[symmetric, OF assms])
    apply (subst eigenspace_lift[symmetric, OF dist])
    using op_eq by simp
qed

axiomatization where colocal_quantum_equality_full[simp]:
  "distinct_qvars (qvariable_concat Q1 (qvariable_concat Q2 Q3)) \<Longrightarrow> colocal (quantum_equality_full U1 Q1 U2 Q2) Q3"
for Q1::"'a qvariables" and Q2::"'b qvariables" and Q3::"'c qvariables"
and U1 U2::"(_,'d)bounded" 

axiomatization where colocal_quantum_eq[simp]: "distinct_qvars (qvariable_concat (qvariable_concat Q1 Q2) R) \<Longrightarrow> colocal (Q1 \<equiv>\<qq> Q2) R"
 for Q1 Q2 :: "'c qvariables" and R :: "'a qvariables"

axiomatization where applyOpSpace_colocal[simp]:
  "colocal U S \<Longrightarrow> U\<noteq>0 \<Longrightarrow> U \<cdot> S = S" for U :: "(mem2,mem2) bounded" and S :: predicate

axiomatization where qeq_collect:
 "quantum_equality_full U Q1 V Q2 = quantum_equality_full (V*\<cdot>U) Q1 idOp Q2"
for U :: "('a,'b) bounded" and V :: "('c,'b) bounded"

lemma qeq_collect_guarded[simp]:
  assumes "NO_MATCH idOp V"
  shows "quantum_equality_full U Q1 V Q2 = quantum_equality_full (V*\<cdot>U) Q1 idOp Q2"
  using qeq_collect by auto

axiomatization where Qeq_mult1[simp]:
  "unitary U \<Longrightarrow> U\<guillemotright>Q1 \<cdot> quantum_equality_full U1 Q1 U2 Q2 = quantum_equality_full (U1\<cdot>U*) Q1 U2 Q2"
 for U::"('a,'a) bounded" and U2 :: "('b,'c) bounded"  

axiomatization where Qeq_mult2[simp]:
  "unitary U \<Longrightarrow> U\<guillemotright>Q2 \<cdot> quantum_equality_full U1 Q1 U2 Q2 = quantum_equality_full U1 Q1 (U2\<cdot>U*) Q2"
 for U::"('a,'a) bounded" and U1 :: "('b,'c) bounded"  

(* Proof in paper *)
axiomatization where quantum_eq_unique[simp]: "distinct_qvars (qvariable_concat Q R) \<Longrightarrow>
  isometry U \<Longrightarrow> isometry (adjoint V) \<Longrightarrow> 
  quantum_equality_full U Q V R \<sqinter> span{\<psi>}\<guillemotright>Q
  = liftSpace (span{\<psi>}) Q \<sqinter> liftSpace (span{V* \<cdot> U \<cdot> \<psi>}) R"
  for Q::"'a qvariables" and R::"'b qvariables"
    and U::"('a,'c) bounded" and V::"('b,'c) bounded"
    and \<psi>::"'a vector"

(* Proof in paper *)
axiomatization where
  quantum_eq_add_state: 
    "distinct_qvars (qvariable_concat Q (qvariable_concat R T)) \<Longrightarrow> norm \<psi> = 1 \<Longrightarrow>
    quantum_equality_full U Q V R \<sqinter> span {\<psi>}\<guillemotright>T
             = quantum_equality_full (U \<otimes> idOp) (qvariable_concat Q T) (addState \<psi> \<cdot> V) R"
    for U :: "('a,'c) bounded" and V :: "('b,'c) bounded" and \<psi> :: "'d vector"
    and Q :: "'a qvariables"    and R :: "'b qvariables"    and T :: "'d qvariables"

section \<open>Common quantum objects\<close>

definition [code del]: "CNOT = classical_operator (Some o (\<lambda>(x::bit,y). (x,y+x)))"
lemma unitaryCNOT[simp]: "unitary CNOT"
  unfolding CNOT_def apply (rule unitary_classical_operator)
  apply (rule o_bij[where g="\<lambda>(x,y). (x,y+x)"]; rule ext)
  unfolding o_def id_def by auto

lemma adjoint_CNOT[simp]: "CNOT* = CNOT"
proof -
  let ?f = "\<lambda>(x::bit,y). (x,y+x)"
  have[simp]: "?f o ?f = id"
    unfolding o_def id_def by auto
  have[simp]: "bij ?f"
    apply (rule o_bij[where g="?f"]; rule ext) by auto
  have[simp]: "inj ?f"
    apply (rule bij_is_inj) by simp
  have[simp]: "surj ?f"
    apply (rule bij_is_surj) by simp
  have inv_f[simp]: "Hilbert_Choice.inv ?f = ?f"
    apply (rule inv_unique_comp) by auto
  have [simp]: "inv_option (Some \<circ> ?f) = Some \<circ> ?f"
    apply (subst inv_option_Some) by simp_all
  show ?thesis
    unfolding CNOT_def
    apply (subst classical_operator_adjoint)
    by auto
qed

lemma CNOT_CNOT[simp]: "CNOT \<cdot> CNOT = idOp"
  using unitaryCNOT unfolding unitary_def adjoint_CNOT by simp

definition [code del]: "pauliX = classical_operator (Some o (\<lambda>x::bit. x+1))"
lemma unitaryX[simp]: "unitary pauliX"
  unfolding pauliX_def apply (rule unitary_classical_operator)
  apply (rule o_bij[where g="\<lambda>x. x+1"]; rule ext)
  unfolding o_def id_def by auto

lemma adjoint_X[simp]: "pauliX* = pauliX"
proof -
  let ?f = "\<lambda>x::bit. x+1"
  have[simp]: "?f o ?f = id"
    unfolding o_def id_def by auto
  have[simp]: "bij ?f"
    apply (rule o_bij[where g="?f"]; rule ext) by auto
  have[simp]: "inj ?f"
    apply (rule bij_is_inj) by simp
  have[simp]: "surj ?f"
    apply (rule bij_is_surj) by simp
  have inv_f[simp]: "Hilbert_Choice.inv ?f = ?f"
    apply (rule inv_unique_comp) by auto
  have [simp]: "inv_option (Some \<circ> ?f) = Some \<circ> ?f"
    apply (subst inv_option_Some) by simp_all
  show ?thesis
    unfolding pauliX_def
    apply (subst classical_operator_adjoint)
    by auto
qed


lemma X_X[simp]: "pauliX \<cdot> pauliX = idOp"
  using unitaryX unfolding unitary_def adjoint_CNOT by simp

axiomatization hadamard :: "(bit,bit) bounded" where
  unitaryH[simp]: "unitary hadamard"
and adjoint_H[simp]: "hadamard* = hadamard"

lemma H_H[simp]: "hadamard \<cdot> hadamard = idOp"
  using unitaryH unfolding unitary_def by simp

definition "hadamard' = sqrt2 \<cdot> hadamard"
lemma H_H': "hadamard = (1/sqrt2) \<cdot> hadamard'" unfolding hadamard'_def by simp
lemma [simp]: "isometry (1 / sqrt2 \<cdot> hadamard')"
  unfolding hadamard'_def by simp


definition [code del]: "pauliZ = hadamard \<cdot> pauliX \<cdot> hadamard"
lemma unitaryZ[simp]: "unitary pauliZ"
  unfolding pauliZ_def by simp

lemma adjoint_Z[simp]: "pauliZ* = pauliZ"
  unfolding pauliZ_def apply simp apply (subst timesOp_assoc) by simp

lemma Z_Z[simp]: "pauliZ \<cdot> pauliZ = idOp"
  using unitaryZ unfolding unitary_def by simp

axiomatization pauliY :: "(bit,bit) bounded"
  where unitaryY[simp]: "unitary pauliY"
    and Y_Y[simp]: "pauliY \<cdot> pauliY = idOp"
    and adjoint_Y[simp]: "pauliY* = pauliY"

axiomatization EPR :: "(bit*bit) vector" 
  where EPR_normalized[simp]: "norm EPR = 1"

definition[code del]: "EPR' = timesScalarVec sqrt2 EPR"

lemma EPR_EPR': "EPR = timesScalarVec (1/sqrt2) EPR'"
  unfolding EPR'_def by simp

lemma norm_EPR'[simp]: "norm (1/sqrt2 \<cdot> EPR') = 1"
  unfolding EPR'_def by simp


section \<open>Misc\<close>

lemma bij_add_const[simp]: "bij (\<lambda>x. x+(y::_::ab_group_add))" 
  apply (rule bijI') apply simp
  apply (rename_tac z) apply (rule_tac x="z-y" in exI)
  by auto


declare imp_conjL[simp]


section "ML Code"

ML_file \<open>qrhl.ML\<close>

section "Simprocs"

(* A simproc that utters warnings whenever the simplifier tries to prove a distinct_qvars statement with distinct, explicitly listed qvariables but can't *)
syntax "_declared_qvars" :: "qvariable_list_args \<Rightarrow> bool" ("declared'_qvars \<lbrakk>_\<rbrakk>")
syntax "_declared_qvars" :: "qvariable_list_args \<Rightarrow> bool" ("declared'_qvars [[_]]")
parse_translation \<open>[("_declared_qvars", QRHL.declared_qvars_parse_tr)]\<close>

simproc_setup warn_declared_qvars ("variable_name q") = QRHL.warn_declared_qvars_simproc

simproc_setup "qvariable_rewriting" ("join_qvariables_hint a b" | "sort_qvariables_hint a") = QRHL.qvariable_rewriting_simproc

section \<open>Programs\<close>

typedecl program
typedecl program_state

axiomatization probability :: "string \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real"
syntax "_probability" :: "ident \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" ("Pr[_:_'(_')]")
parse_translation \<open>[("_probability", fn ctx => fn [Const(v,_),p,rho] =>
  @{const probability} $ HOLogic.mk_string v $ p $ rho)]\<close>

(* Must come after loading qrhl.ML *)                                                                          
print_translation \<open>[(@{const_syntax probability}, fn ctx => fn [str,p,rho] =>
  Const(@{syntax_const "_probability"},dummyT) $ Const(QRHL.dest_string_syntax str,dummyT) $ p $ rho)]\<close>


end