theory QRHL
  imports Complex_Main "HOL-Library.Adhoc_Overloading"
begin
  
section \<open>Miscellaneous\<close>
  
syntax "Lattices.sup_class.sup" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
syntax "Lattices.inf_class.inf" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)

typedef 'a distr = "{f::'a\<Rightarrow>real. (\<forall>x. f x \<ge> 0) \<and> (\<forall> M. sum f M \<le> 1)}" 
  morphisms prob Abs_distr
  apply (rule exI[of _ "\<lambda>x. 0"]) by auto
instantiation distr :: (type)zero begin
definition "0 = Abs_distr (\<lambda>_. 0)"
instance .. 
end
 
  
definition "supp \<mu> = {x. prob \<mu> x > 0}" 
definition uniform :: "'a set \<Rightarrow> 'a distr" where
  "uniform M = Abs_distr (\<lambda>m. if m\<in>M then 1/card M else 0)"
axiomatization where supp_uniform [simp]: "M \<noteq> {} \<Longrightarrow> finite M \<Longrightarrow> supp (uniform M) = M" for M :: "'a set"
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

lemma bit_cases: "(x=0 \<Longrightarrow> P) \<Longrightarrow> (x=1 \<Longrightarrow> P) \<Longrightarrow> P" for x :: bit
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

typedef 'a state = "{x::'a vector. norm x = 1}"
  morphisms state_to_vector Abs_state
  apply (rule exI[of _ "basis_vector undefined"])
  by simp
setup_lifting type_definition_state

lift_definition ket :: "'a \<Rightarrow> 'a state" ("|_\<rangle>") is "basis_vector"
  by (rule ell2_basis_vector)

lemma vector_to_state_ket[simp]: "state_to_vector (ket i) = basis_vector i"
  by (rule ket.rep_eq)

declare[[coercion state_to_vector]]


typedecl 'a subspace
  
instantiation subspace :: (type)zero begin instance .. end (* The subspace {0} *)
instantiation subspace :: (type)top begin instance .. end (* The full space *)
instantiation subspace :: (type)inf begin instance .. end (* Intersection *)
instantiation subspace :: (type)Inf begin instance .. end (* Intersection *)
instantiation subspace :: (type)plus begin instance .. end (* Sum of spaces *)
instantiation subspace :: (type)Sup begin instance .. end (* Sum of spaces *)

consts tmp_subspace_less_eq :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> bool"
instantiation subspace :: (type)ord begin  
definition "(a \<le> b) = tmp_subspace_less_eq a b" (* \<le> means inclusion *)
definition "(a < b) = (a \<le> b \<and> \<not> (b \<le> a))" for a :: "'a subspace"
instance .. end
hide_fact less_eq_subspace_def
hide_const tmp_subspace_less_eq

axiomatization ortho :: "'a subspace \<Rightarrow> 'a subspace" (* Orthogonal complement *)
  
axiomatization where
    subspace_zero_not_top[simp]: "(0::'a subspace) \<noteq> top"
and tmp_reflex: "x \<le> x" (* Names with tmp_ will be hidden later *)
and tmp_transitive: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
and tmp_antisym: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
and tmp_top: "x \<le> top"
and tmp_pos: "x \<ge> 0" (* zero_le *)
and tmp_inf1: "inf x y \<le> x"
and tmp_inf2: "inf x y \<le> y"
and tmp_inf: "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z"
and tmp_assoc: "x + y + z = x + (y + z)" 
and tmp_comm: "x + y = y + x"
and tmp_mono: "x \<le> y \<Longrightarrow> z + x \<le> z + y"
and tmp_zero_neutral: "0 + x = x"
and subspace_plus_sup: "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y + z \<le> x"
and tmp_Inf1: "x \<in> A \<Longrightarrow> Inf A \<le> x"
and tmp_Inf2: "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A"
and tmp_Sup1: "x \<in> A \<Longrightarrow> Sup A \<ge> x"
and tmp_Sup2: "(\<And>x. x \<in> A \<Longrightarrow> z \<ge> x) \<Longrightarrow> z \<ge> Sup A"
and tmp_Inf3: "Inf {} = (top::'a subspace)" 
and subspace_empty_Sup: "Sup {} = (0::'a subspace)"
for x y z :: "'a subspace"

instantiation subspace :: (type)order begin
instance apply intro_classes
    by (fact less_subspace_def, fact tmp_reflex, fact tmp_transitive, fact tmp_antisym)
end
hide_fact tmp_reflex tmp_transitive tmp_antisym

instantiation subspace :: (type)order_top begin
instance apply intro_classes by (fact tmp_top)
end
hide_fact tmp_top

instantiation subspace :: (type)order_bot begin
definition "(bot::'a subspace) = 0"
instance apply intro_classes unfolding bot_subspace_def by (fact tmp_pos)
end

instantiation subspace :: (type)ab_semigroup_add begin
instance apply intro_classes by (fact tmp_assoc, fact tmp_comm)
end
hide_fact tmp_assoc tmp_comm
  
instantiation subspace :: (type)ordered_ab_semigroup_add begin
instance apply intro_classes by (fact tmp_mono)
end
hide_fact tmp_mono
 
instantiation subspace :: (type)comm_monoid_add begin
instance apply intro_classes by (fact tmp_zero_neutral)
end
hide_fact tmp_zero_neutral
     
  
instantiation subspace :: (type)semilattice_sup begin
definition "sup a b = a+b" for a::"'a subspace"
instance apply intro_classes
  using add_left_mono sup_subspace_def tmp_pos apply fastforce
  using add_right_mono sup_subspace_def tmp_pos apply fastforce
  by (simp add: subspace_plus_sup sup_subspace_def)
end

instantiation subspace :: (type)canonically_ordered_monoid_add begin
instance apply intro_classes
  by (metis add.commute add.right_neutral add_left_mono antisym_conv subspace_plus_sup tmp_pos)
end
hide_fact tmp_pos
  
instantiation subspace :: (type)semilattice_inf begin
instance apply intro_classes by (fact tmp_inf1, fact tmp_inf2, fact tmp_inf)
end
hide_fact tmp_inf1 tmp_inf2 tmp_inf

instantiation subspace :: (type)lattice begin
instance ..
end

instantiation subspace :: (type)complete_lattice begin
instance apply intro_classes
       apply (fact tmp_Inf1, fact tmp_Inf2, fact tmp_Sup1, fact tmp_Sup2, fact tmp_Inf3)
    unfolding bot_subspace_def by (fact subspace_empty_Sup)
end
hide_fact tmp_Inf1 tmp_Inf2 tmp_Sup1 tmp_Sup2 tmp_Inf3
  
  
lemma top_not_bot[simp]: "(top::'a subspace) \<noteq> bot" 
  using subspace_zero_not_top bot_subspace_def by metis

lemma inf_assoc_subspace[simp]: "A \<sqinter> (B \<sqinter> C) = A \<sqinter> B \<sqinter> C" for A B C :: "_ subspace"
  unfolding inf.assoc by simp

lemma bot_plus[simp]: "bot + x = x" for x :: "'a subspace" unfolding sup_subspace_def[symmetric] by simp
lemma plus_bot[simp]: "x + bot = x" for x :: "'a subspace" unfolding sup_subspace_def[symmetric] by simp
lemma top_plus[simp]: "top + x = top" for x :: "'a subspace" unfolding sup_subspace_def[symmetric] by simp
lemma plus_top[simp]: "x + top = top" for x :: "'a subspace" unfolding sup_subspace_def[symmetric] by simp
    
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

subsection \<open>Bounded operators\<close>
  
typedef ('a,'b) bounded = "{A::'a vector\<Rightarrow>'b vector. bounded_linear A}"
  morphisms applyOp Abs_bounded
  using bounded_linear_zero by blast
setup_lifting type_definition_bounded

lift_definition idOp :: "('a,'a)bounded" is id
  by (metis bounded_linear_ident comp_id fun.map_ident)
 
axiomatization
  adjoint :: "('a,'b) bounded \<Rightarrow> ('b,'a) bounded" ("_*" [99] 100)
and timesOp :: "('b,'c) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'c) bounded" 
(* and applyOp :: "('a,'b) bounded \<Rightarrow> 'a vector \<Rightarrow> 'b vector" *)
and applyOpSpace :: "('a,'b) bounded \<Rightarrow> 'a subspace \<Rightarrow> 'b subspace"
where
 applyOp_0[simp]: "applyOpSpace U 0 = 0"

lemma applyOp_bot[simp]: "applyOpSpace U bot = bot"
  by (simp add: bot_subspace_def)

axiomatization where adjoint_twice[simp]: "U** = U" for U :: "('a,'b) bounded"

abbreviation "imageOp U \<equiv> applyOpSpace U top"

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
and times_idOp1[simp]: "U \<cdot> idOp = U"
and times_idOp2[simp]: "idOp \<cdot> V = V"
and image_id[simp]: "imageOp idOp = top"
and idOp_adjoint[simp]: "idOp* = idOp"
for \<psi> :: "'a vector" and S :: "'a subspace" and U :: "('a,'b) bounded" and V :: "('b,'a) bounded"

axiomatization where mult_INF[simp]: "U \<cdot> (INF x. V x) = (INF x. U \<cdot> V x)" 
  for V :: "'a \<Rightarrow> 'b subspace" and U :: "('b,'c) bounded"

lemma mult_inf_distrib[simp]: "U \<cdot> (B \<sqinter> C) = (U \<cdot> B) \<sqinter> (U \<cdot> C)" 
  for U :: "('a,'b) bounded" and B C :: "'a subspace"
  using mult_INF[where V="\<lambda>x. if x then B else C" and U=U] 
  unfolding INF_UNIV_bool_expand
  by simp

fun powerOp :: "('a,'a) bounded \<Rightarrow> nat \<Rightarrow> ('a,'a) bounded" where 
  "powerOp U 0 = idOp"
| "powerOp U (Suc i) = U \<cdot> powerOp U i"

definition "unitary U = (U \<cdot> (U*) = idOp \<and> U* \<cdot> U = idOp)"  
definition "isometry U = (U* \<cdot> U = idOp)"  

lemma unitary_isometry[simp]: "unitary U \<Longrightarrow> isometry U"
  unfolding unitary_def isometry_def by simp

lemma unitary_adjoint[simp]: "unitary (U*) = unitary U" for U::"('a,'b)bounded"
  unfolding unitary_def by auto

axiomatization where unitary_image[simp]: "unitary U \<Longrightarrow> imageOp U = top"
  for U :: "('a,'a) bounded"

lemma unitary_id[simp]: "unitary idOp"
  unfolding unitary_def by simp

section \<open>Projectors\<close>

definition "isProjector P = (P=P* \<and> P=P\<cdot>P)"
axiomatization proj :: "'a vector \<Rightarrow> ('a,'a) bounded"
  where isProjector_proj[simp]: "isProjector (proj x)"
and imageOp_proj [simp]: "imageOp (proj \<psi>) = span {\<psi>}" for \<psi> :: "'a vector"

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
(* and qvariable_cons :: "'a qvariable \<Rightarrow> 'b qvariables \<Rightarrow> ('a \<times> 'b) qvariables" *)
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
  
axiomatization colocal_ass_qvars :: "predicate \<Rightarrow> 'a qvariables \<Rightarrow> bool"
  and colocal_qvars_qvars :: "'a qvariables \<Rightarrow> 'b qvariables \<Rightarrow> bool"
  and colocal_qvar_qvars :: "'a qvariable \<Rightarrow> 'b qvariables \<Rightarrow> bool"

consts colocal :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
adhoc_overloading colocal colocal_ass_qvars colocal_qvars_qvars colocal_qvar_qvars
  
axiomatization where 
  colocal_qvariable_names[simp]: "set (qvariable_names Q) \<inter> set (qvariable_names R) = {} \<Longrightarrow> colocal Q R" 
  for Q :: "'a qvariables" and R :: "'b qvariables"

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
and imageOp_lift[simp]: "imageOp (liftOp U Q) = liftSpace (imageOp U) Q"
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

axiomatization space_div :: "predicate \<Rightarrow> 'a state \<Rightarrow> 'a qvariables \<Rightarrow> predicate" ("_ \<div> _\<guillemotright>_" [89,89,89] 90)
  where leq_space_div[simp]: "colocal A Q \<Longrightarrow> (A \<le> B \<div> \<psi>\<guillemotright>Q) = (A \<sqinter> span {\<psi>}\<guillemotright>Q \<le> B)"
  
section \<open>Common quantum objects\<close>

axiomatization EPR :: "(bit*bit) vector"

axiomatization CNOT :: "(bit*bit, bit*bit) bounded" where
  unitaryCNOT[simp]: "unitary CNOT"
axiomatization H :: "(bit,bit) bounded" 
  and X :: "(bit,bit) bounded"
  and Y :: "(bit,bit) bounded"
  and Z :: "(bit,bit) bounded"
  where
  unitaryH[simp]: "unitary H"
and unitaryX[simp]: "unitary X"
and unitaryY[simp]: "unitary Y"
and unitaryZ[simp]: "unitary Z"
and CNOT_CNOT[simp]: "CNOT \<cdot> CNOT = idOp"
and H_H[simp]: "H \<cdot> H = idOp"
and X_X[simp]: "X \<cdot> X = idOp"
and Y_Y[simp]: "Y \<cdot> Y = idOp"
and Z_Z[simp]: "Z \<cdot> Z = idOp"
and adjoint_CNOT[simp]: "CNOT* = CNOT"
and adjoint_H[simp]: "H* = H"
and adjoint_X[simp]: "X* = X"
and adjoint_Y[simp]: "Y* = Y"
and adjoint_Z[simp]: "Z* = Z"

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
