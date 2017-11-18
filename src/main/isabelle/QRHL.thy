theory QRHL
  imports Complex_Main "HOL-Library.Adhoc_Overloading" "HOL-Library.Rewrite"
begin
  
section \<open>Miscellaneous\<close>
  
syntax "Lattices.sup_class.sup" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
syntax "Lattices.inf_class.inf" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)

term "comm_monoid_set"

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
and map_distr_uniform_eq[simp]: "(map_distr f (uniform A) = uniform B) = (bij_betw f A B \<or> (infinite A \<and> infinite B))"
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
instantiation bit :: finite begin
instance by (intro_classes, transfer, simp)
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


lift_definition basis_vector :: "'a \<Rightarrow> 'a vector" is "\<lambda>x y. if x=y then 1 else 0"
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

lemma ell2_basis_vector[simp]: "norm (basis_vector i) = 1"
  apply transfer unfolding ell2_norm_def
  apply (rule cSUP_eq_maximum)
  apply (rule_tac x="{i}" in bexI)
    apply auto
  by (rule ell2_1)

axiomatization orthogonal :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> bool"
  where orthogonal_comm: "orthogonal \<psi> \<phi> = orthogonal \<phi> \<psi>"


typedef 'a state = "{x::'a vector. norm x = 1}"
  morphisms state_to_vector Abs_state
  apply (rule exI[of _ "basis_vector undefined"])
  by simp
setup_lifting type_definition_state

lift_definition ket :: "'a \<Rightarrow> 'a state" ("|_\<rangle>") is "basis_vector"
  by (rule ell2_basis_vector)

lemma vector_to_state_ket[simp]: "state_to_vector (ket i) = basis_vector i"
  by (rule ket.rep_eq)

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

declare[[coercion state_to_vector]]

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
  have "basis_vector undefined \<noteq> (0::'a vector)"
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

lemma inf_assoc_subspace[simp]: "A \<sqinter> (B \<sqinter> C) = A \<sqinter> B \<sqinter> C" for A B C :: "_ subspace"
  unfolding inf.assoc by simp

lemma bot_plus[simp]: "bot + x = x" for x :: "'a subspace"
  apply transfer
  unfolding sup_subspace_def[symmetric] by simp
lemma plus_bot[simp]: "x + bot = x" for x :: "'a subspace" unfolding subspace_sup_plus[symmetric] by simp
lemma top_plus[simp]: "top + x = top" for x :: "'a subspace" unfolding subspace_sup_plus[symmetric] by simp
lemma plus_top[simp]: "x + top = top" for x :: "'a subspace" unfolding subspace_sup_plus[symmetric] by simp
    
axiomatization subspace_as_set :: "'a subspace \<Rightarrow> 'a vector set"
    
definition "spanVector A = Inf {S. A \<subseteq> subspace_as_set S}"
definition "spanState A = Inf {S. state_to_vector ` A \<subseteq> subspace_as_set S}"
consts span :: "'a set \<Rightarrow> 'b subspace"
adhoc_overloading span spanState spanVector

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
where
 applyOp_0[simp]: "applyOpSpace U 0 = 0"
and times_applyOp: "applyOp (timesOp A B) \<psi> = applyOp A (applyOp B \<psi>)"
axiomatization where
  timesOp_assoc: "timesOp A (timesOp B C) = timesOp (timesOp A B) C" 
and times_adjoint[simp]: "adjoint (timesOp A B) = timesOp (adjoint B) (adjoint A)"
for A :: "('b,'a) bounded" and B :: "('c,'b) bounded" and C :: "('d,'c) bounded"

lemma applyOp_bot[simp]: "applyOpSpace U bot = bot"
  by (simp add: subspace_zero_bot[symmetric])

axiomatization where equal_basis: "(\<And>x. applyOp A (basis_vector x) = applyOp B (basis_vector x)) \<Longrightarrow> A = B" for A::"('a,'b) bounded"

axiomatization where adjoint_twice[simp]: "U** = U" for U :: "('a,'b) bounded"

consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)
adhoc_overloading
  cdot timesOp applyOp applyOpSpace

axiomatization where
  cdot_plus_distrib[simp]: "U \<cdot> (A + B) = U \<cdot> A + U \<cdot> B"
for A B :: "'a subspace" and U :: "('a,'b) bounded"

lemma apply_idOp[simp]: "applyOp idOp \<psi> = \<psi>"
  by (simp add: idOp.rep_eq)

axiomatization 
    (* idOp :: "('a,'a) bounded" *)
where
    (* apply_idOp[simp]: "applyOp idOp \<psi> = \<psi>" *)
    apply_idOp_space[simp]: "applyOpSpace idOp S = S"
and apply_0[simp]: "applyOp U 0 = 0"
and times_idOp1[simp]: "U \<cdot> idOp = U"
and times_idOp2[simp]: "idOp \<cdot> V = V"
(* and image_id[simp]: "imageOp idOp = top" *)
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
definition "inv_option \<pi> = (\<lambda>y. if Some y \<in> range \<pi> then Some (inv \<pi> (Some y)) else None)"
lemma inj_option_Some[simp]: "inj_option (Some o \<pi>) = inj \<pi>"
  unfolding inj_option_def inj_def by simp
lemma inv_option_Some: "surj \<pi> \<Longrightarrow> inv_option (Some o \<pi>) = Some o (inv \<pi>)"
  unfolding inv_option_def o_def inv_def apply (rule ext) by auto

(* TODO: document classical_operator *)

definition "cobounded_partial_fun f = (\<exists>n. \<forall>y. finite {x. f x = Some y} \<and> card {x. f x = Some y} \<le> n)"

lemma assumes "cobounded_partial_fun \<pi>" and "cobounded_partial_fun \<rho>" shows "cobounded_partial_fun (\<pi> \<circ>\<^sub>m \<rho>)"
proof -
  from assms obtain n where finite_pi: "finite {x. \<pi> x = Some y}" and n:"card {x. \<pi> x = Some y} \<le> n" for y 
    unfolding cobounded_partial_fun_def by auto
  from assms obtain m where finite_rho: "finite {x. \<rho> x = Some y}" and m:"card {x. \<rho> x = Some y} \<le> m" for y 
    unfolding cobounded_partial_fun_def by auto
      { fix y
        have nested: "{x. (\<pi> \<circ>\<^sub>m \<rho>) x = Some y} = (\<Union>z\<in>{z. \<pi> z = Some y}. {x. \<rho> x = Some z})"
          (is "?comp = (\<Union>z\<in>?piset. ?rhoset z)")
          apply auto unfolding map_comp_def
          by (metis option.case_eq_if option.distinct(1) option.exhaust_sel) 
        let ?rhoset' = "\<lambda>z. {(x,z) | x. \<rho> x = Some z}"
        have m': "card (?rhoset' z) \<le> m" for z
          using m 
          apply (rewrite asm_rl[of "?rhoset' z = (\<lambda>x. (x,z)) ` ?rhoset z"], (auto)[1])
          apply (subst card_image) unfolding inj_on_def by auto
        have finite: "finite {x. (\<pi> \<circ>\<^sub>m \<rho>) x = Some y}"
          unfolding nested apply (rule finite_UN_I)
          using both_ok by auto
        have "card ?comp = card (\<Union>z\<in>?piset. ?rhoset z)"
          unfolding nested by simp
        also have "... = card (fst ` (\<Union>z\<in>?piset. ?rhoset' z))"
          unfolding image_UN 
          apply (subst (2) image_Collect)
          by auto
        also have "... \<le> card (\<Union>z\<in>?piset. ?rhoset' z)"
          apply (rule card_image_le) apply (rule finite_UN_I) using both_ok by auto
        also have "... = (\<Sum>i\<in>?piset. card {(x, i) |x. \<rho> x = Some i})"
          apply (rule card_UN_disjoint)
          using finite_pi finite_rho by auto
        also have "... \<le> (\<Sum>i\<in>?piset. m)"
          apply (rule sum_mono) using m' by simp 
        also have "\<dots> = card ?piset * m" 
          by simp
        also have "\<dots> \<le> n * m"
          using n by auto
        finally have card: "card ?comp \<le> n * m" by assumption
        note finite card
      }
      then show ?thesis  by auto
proof -

|| A ket(i) ||_1,2 \<le> B
|| A (sum x_i ket(i)) ||_2
\<le>
sum x_i || A ket i || 
\<le> 
B sum x_i


axiomatization classical_operator :: "('a\<Rightarrow>'b option) \<Rightarrow> ('a,'b) bounded" where
 classical_operator_basis: "cobounded_partial_fun \<pi> \<Longrightarrow>
    applyOp (classical_operator \<pi>) (basis_vector x) = (case \<pi> x of Some y \<Rightarrow> basis_vector y | None \<Rightarrow> 0)"
and
   classical_operator_invalid: "\<not> (\<exists>n. \<forall>y. finite {x. \<pi> x = Some y} \<and> card {x. \<pi> x = Some y} \<le> n) \<Longrightarrow>
    classical_operator \<pi> = 0"
axiomatization where classical_operator_adjoint: 
  "inj_option \<pi> \<Longrightarrow> adjoint (classical_operator \<pi>) = classical_operator (inv_option \<pi>)"
for \<pi> :: "'a \<Rightarrow> 'b option"


lemma classical_operator_mult[simp]:
  "classical_operator \<pi> \<cdot> classical_operator \<rho> = classical_operator (map_comp \<pi> \<rho>)"
proof (rule equal_basis)
  fix x
  consider (both_ok) "\<exists>n. \<forall>y. finite {x. \<pi> x = Some y} \<and> card {x. \<pi> x = Some y} \<le> n" and 
           "\<exists>n. \<forall>y. finite {x. \<rho> x = Some y} \<and> card {x. \<rho> x = Some y} \<le> n"
           | (pi_unbounded) "\<not> (\<exists>n. \<forall>y. finite {x. \<pi> x = Some y} \<and> card {x. \<pi> x = Some y} \<le> n)"
           | (rho_unbounded) "\<not> (\<exists>n. \<forall>y. finite {x. \<rho> x = Some y} \<and> card {x. \<rho> x = Some y} \<le> n)" 
    apply atomize_elim by auto
  then show "classical_operator \<pi> \<cdot> classical_operator \<rho> \<cdot> basis_vector x =
        classical_operator (\<pi> \<circ>\<^sub>m \<rho>) \<cdot> basis_vector x"
  proof (cases)
    case both_ok
    have comp_ok: "\<exists>n. \<forall>y. finite {x. (\<pi> \<circ>\<^sub>m \<rho>) x = Some y} \<and> card {x. (\<pi> \<circ>\<^sub>m \<rho>) x = Some y} \<le> n"
    proof -
      from both_ok obtain n where finite_pi: "finite {x. \<pi> x = Some y}" and n:"card {x. \<pi> x = Some y} \<le> n" for y by auto
      from both_ok obtain m where finite_rho: "finite {x. \<rho> x = Some y}" and m:"card {x. \<rho> x = Some y} \<le> m" for y by auto
      { fix y
        have nested: "{x. (\<pi> \<circ>\<^sub>m \<rho>) x = Some y} = (\<Union>z\<in>{z. \<pi> z = Some y}. {x. \<rho> x = Some z})"
          (is "?comp = (\<Union>z\<in>?piset. ?rhoset z)")
          apply auto unfolding map_comp_def
          by (metis option.case_eq_if option.distinct(1) option.exhaust_sel) 
        let ?rhoset' = "\<lambda>z. {(x,z) | x. \<rho> x = Some z}"
        have m': "card (?rhoset' z) \<le> m" for z
          using m 
          apply (rewrite asm_rl[of "?rhoset' z = (\<lambda>x. (x,z)) ` ?rhoset z"], (auto)[1])
          apply (subst card_image) unfolding inj_on_def by auto
        have finite: "finite {x. (\<pi> \<circ>\<^sub>m \<rho>) x = Some y}"
          unfolding nested apply (rule finite_UN_I)
          using both_ok by auto
        have "card ?comp = card (\<Union>z\<in>?piset. ?rhoset z)"
          unfolding nested by simp
        also have "... = card (fst ` (\<Union>z\<in>?piset. ?rhoset' z))"
          unfolding image_UN 
          apply (subst (2) image_Collect)
          by auto
        also have "... \<le> card (\<Union>z\<in>?piset. ?rhoset' z)"
          apply (rule card_image_le) apply (rule finite_UN_I) using both_ok by auto
        also have "... = (\<Sum>i\<in>?piset. card {(x, i) |x. \<rho> x = Some i})"
          apply (rule card_UN_disjoint)
          using finite_pi finite_rho by auto
        also have "... \<le> (\<Sum>i\<in>?piset. m)"
          apply (rule sum_mono) using m' by simp 
        also have "\<dots> = card ?piset * m" 
          by simp
        also have "\<dots> \<le> n * m"
          using n by auto
        finally have card: "card ?comp \<le> n * m" by assumption
        note finite card
      }
      then show ?thesis  by auto
    qed
    show ?thesis
    proof (cases "\<rho> x")
      case None
      then show ?thesis 
        unfolding times_applyOp classical_operator_basis[OF both_ok(2)] classical_operator_basis[OF comp_ok] 
        by simp
    next
      case (Some y)
      show ?thesis 
        unfolding classical_operator_basis[OF comp_ok] 
        by (simp add: classical_operator_basis[OF both_ok(1)] 
            classical_operator_basis[OF both_ok(2)] times_applyOp Some map_comp_def)
    qed
  next
    case pi_unbounded
    show ?thesis 
      apply (subst classical_operator_invalid[of \<pi>]) using pi_unbounded apply simp
      by doesnotwork
  next
    case rho_unbounded
    then show ?thesis
      apply (subst classical_operator_invalid[of \<rho>]) using rho_unbounded apply simp
      sorry
  qed

  cases pi rho comp
        0   0   0  \<rightarrow> ok
        0   0   1  \<rightarrow> ok (imposs)
        1   *   1  \<rightarrow> ok
        *   1   1  \<rightarrow> ok
        0   1   0  \<rightarrow> bad
        1   0   0  \<rightarrow> bad
        1   1   0  \<rightarrow> bad
        
qed

lemma classical_operator_Some[simp]: "classical_operator Some = idOp"
  apply (rule equal_basis) unfolding classical_operator_basis by auto

(* fun powerOp :: "('a,'a) bounded \<Rightarrow> nat \<Rightarrow> ('a,'a) bounded" where 
  "powerOp U 0 = idOp"
| "powerOp U (Suc i) = U \<cdot> powerOp U i" *)

definition "unitary U = (U \<cdot> (U*) = idOp \<and> U* \<cdot> U = idOp)"  
definition "isometry U = (U* \<cdot> U = idOp)"  

lemma unitary_isometry[simp]: "unitary U \<Longrightarrow> isometry U"
  unfolding unitary_def isometry_def by simp

lemma unitary_adjoint[simp]: "unitary (U*) = unitary U" for U::"('a,'b)bounded"
  unfolding unitary_def by auto

lemma unitary_times[simp]: "unitary A \<Longrightarrow> unitary B \<Longrightarrow> unitary (A\<cdot>B)"
  unfolding unitary_def apply simp
  apply (subst timesOp_assoc)  
  apply (subst timesOp_assoc[symmetric])  
  apply simp
  apply (subst timesOp_assoc)  
  apply (subst timesOp_assoc[symmetric])  
  by simp

lemma isometry_times[simp]: "isometry A \<Longrightarrow> isometry B \<Longrightarrow> isometry (A\<cdot>B)"
  unfolding isometry_def apply simp
  apply (subst timesOp_assoc)  
  apply (subst timesOp_assoc[symmetric])  
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
    apply (subst classical_operator_adjoint)
    using assms apply simp
    apply simp
    apply (subst comp)
    apply (rule equal_basis)
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
    apply (subst classical_operator_adjoint)
     apply (simp add: \<open>inj \<pi>\<close>)
    apply simp
    apply (subst comp)
    by simp
qed



axiomatization where unitary_image[simp]: "unitary U \<Longrightarrow> applyOpSpace U top = top"
  for U :: "('a,'a) bounded"

lemma unitary_id[simp]: "unitary idOp"
  unfolding unitary_def by simp

section \<open>Projectors\<close>

definition "isProjector P = (P=P* \<and> P=P\<cdot>P)"
axiomatization proj :: "'a vector \<Rightarrow> ('a,'a) bounded"
  where isProjector_proj[simp]: "isProjector (proj x)"
and imageOp_proj [simp]: "applyOpSpace (proj \<psi>) top = span {\<psi>}" for \<psi> :: "'a vector"

section \<open>Measurements\<close>

typedecl ('a,'b) measurement
axiomatization mproj :: "('a,'b) measurement \<Rightarrow> 'a \<Rightarrow> ('b,'b) bounded"
  and mtotal :: "('a,'b) measurement \<Rightarrow> bool"
  where isProjector_mproj[simp]: "isProjector (mproj M i)"

axiomatization computational_basis :: "('a, 'a) measurement" where
  mproj_computational_basis[simp]: "mproj computational_basis x = proj (basis_vector x)"
and mtotal_computational_basis [simp]: "mtotal computational_basis"

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

definition "qvariables_distinct X == distinct (qvariable_names X)"

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
  
axiomatization colocal_pred_qvars :: "predicate \<Rightarrow> 'a qvariables \<Rightarrow> bool"
  and colocal_qvars_qvars :: "'a qvariables \<Rightarrow> 'b qvariables \<Rightarrow> bool"
  and colocal_qvar_qvars :: "'a qvariable \<Rightarrow> 'b qvariables \<Rightarrow> bool" (* TODO remove or docu *)

consts colocal :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
adhoc_overloading colocal colocal_pred_qvars colocal_qvars_qvars (* colocal_qvar_qvars *)
  
axiomatization where 
  colocal_qvariable_names[simp]: "set (qvariable_names Q) \<inter> set (qvariable_names R) = {} \<Longrightarrow> colocal Q R" 
  for Q :: "'a qvariables" and R :: "'b qvariables"

axiomatization where
  colocal_top[simp]: "colocal top Q"
  and colocal_bot[simp]: "colocal bot Q"
  and colocal_inf[simp]: "colocal A Q \<Longrightarrow> colocal B Q \<Longrightarrow> colocal (A \<sqinter> B) Q"
  and colocal_sup[simp]: "colocal A Q \<Longrightarrow> colocal B Q \<Longrightarrow> colocal (A \<squnion> B) Q"
  and colocal_plus[simp]: "colocal A Q \<Longrightarrow> colocal B Q \<Longrightarrow> colocal (A + B) Q"
  and colocal_Cla[simp]: "colocal (Cla[b]) Q"
for Q :: "'a qvariables"

subsection \<open>Quantum equality\<close>

axiomatization quantum_equality_full :: "('a,'c) bounded \<Rightarrow> 'a qvariables \<Rightarrow> ('b,'c) bounded \<Rightarrow> 'b qvariables \<Rightarrow> predicate"
abbreviation "quantum_equality" :: "'a qvariables \<Rightarrow> 'a qvariables \<Rightarrow> predicate" (infix "\<equiv>\<qq>" 100)
  where "quantum_equality X Y \<equiv> quantum_equality_full idOp X idOp Y"
syntax quantum_equality :: "'a qvariables \<Rightarrow> 'a qvariables \<Rightarrow> predicate" (infix "==q" 100)
syntax "_quantum_equality" :: "qvariable_list_args \<Rightarrow> qvariable_list_args \<Rightarrow> predicate" ("Qeq'[_=_']")
translations
  "_quantum_equality a b" \<rightharpoonup> "CONST quantum_equality (_qvariables a) (_qvariables b)"

axiomatization where colocal_quantum_eq[simp]: "colocal Q1 R \<Longrightarrow> colocal Q2 R \<Longrightarrow> colocal (Q1 \<equiv>\<qq> Q2) R"
 for Q1 Q2 :: "'c qvariables" and R :: "'a qvariables"


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

axiomatization where lift_idOp[simp]: "idOp\<guillemotright>Q = idOp" for Q :: "'a qvariables"


axiomatization where Qeq_mult1[simp]:
  "unitary U \<Longrightarrow> U\<guillemotright>Q1 \<cdot> quantum_equality_full U1 Q1 U2 Q2 = quantum_equality_full (U1\<cdot>U*) Q1 U2 Q2"
 for U::"('a,'a) bounded" and U2 :: "('b,'c) bounded"  

axiomatization where Qeq_mult2[simp]:
  "unitary U \<Longrightarrow> U\<guillemotright>Q2 \<cdot> quantum_equality_full U1 Q1 U2 Q2 = quantum_equality_full U1 Q1 (U2\<cdot>U*) Q2"
 for U::"('a,'a) bounded" and U1 :: "('b,'c) bounded"  

axiomatization where qeq_collect:
 "quantum_equality_full U Q1 V Q2 = quantum_equality_full (V*\<cdot>U) Q1 idOp Q2"
for U :: "('a,'b) bounded" and V :: "('c,'b) bounded"

lemma qeq_collect_guarded[simp]:
  assumes "NO_MATCH idOp V"
  shows "quantum_equality_full U Q1 V Q2 = quantum_equality_full (V*\<cdot>U) Q1 idOp Q2"
  using qeq_collect by auto

axiomatization where quantum_eq_unique [simp]: "quantum_equality Q R \<sqinter> liftSpace (span{\<psi>}) Q = liftSpace (span{\<psi>}) Q \<sqinter> liftSpace (span{\<psi>}) R"
  for Q R :: "'a qvariables" and \<psi> :: "'a vector"

subsection \<open>Subspace division\<close>

axiomatization space_div :: "predicate \<Rightarrow> 'a state \<Rightarrow> 'a qvariables \<Rightarrow> predicate"
                    ("_ \<div> _\<guillemotright>_" [89,89,89] 90)
  where leq_space_div[simp]: "colocal A Q \<Longrightarrow> (A \<le> B \<div> \<psi>\<guillemotright>Q) = (A \<sqinter> span {\<psi>}\<guillemotright>Q \<le> B)"
  
section \<open>Common quantum objects\<close>

definition "CNOT = classical_operator (Some o (\<lambda>(x::bit,y). (x,y+x)))"
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
  have inv_f[simp]: "inv ?f = ?f"
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

definition "X = classical_operator (Some o (\<lambda>x::bit. x+1))"
lemma unitaryX[simp]: "unitary X"
  unfolding X_def apply (rule unitary_classical_operator)
  apply (rule o_bij[where g="\<lambda>x. x+1"]; rule ext)
  unfolding o_def id_def by auto

lemma adjoint_X[simp]: "X* = X"
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
  have inv_f[simp]: "inv ?f = ?f"
    apply (rule inv_unique_comp) by auto
  have [simp]: "inv_option (Some \<circ> ?f) = Some \<circ> ?f"
    apply (subst inv_option_Some) by simp_all
  show ?thesis
    unfolding X_def
    apply (subst classical_operator_adjoint)
    by auto
qed


lemma X_X[simp]: "X \<cdot> X = idOp"
  using unitaryX unfolding unitary_def adjoint_CNOT by simp

axiomatization H :: "(bit,bit) bounded" where
  unitaryH[simp]: "unitary H"
and adjoint_H[simp]: "H* = H"

lemma H_H[simp]: "H \<cdot> H = idOp"
  using unitaryH unfolding unitary_def by simp


definition "Z = H \<cdot> X \<cdot> H"
lemma unitaryZ[simp]: "unitary Z"
  unfolding Z_def by simp

lemma adjoint_Z[simp]: "Z* = Z"
  unfolding Z_def apply simp apply (subst timesOp_assoc) by simp

lemma Z_Z[simp]: "Z \<cdot> Z = idOp"
  using unitaryZ unfolding unitary_def by simp

axiomatization Y :: "(bit,bit) bounded"
  where unitaryY[simp]: "unitary Y"
    and Y_Y[simp]: "Y \<cdot> Y = idOp"
    and adjoint_Y[simp]: "Y* = Y"

section \<open>Misc\<close>

lemma bij_add_const[simp]: "bij (\<lambda>x. x+(y::_::ab_group_add))" 
  apply (rule bijI') apply simp
  apply (rename_tac z) apply (rule_tac x="z-y" in exI)
  by auto


declare imp_conjL[simp]


ML_file \<open>qrhl.ML\<close>
  

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
