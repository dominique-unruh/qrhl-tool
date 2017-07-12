theory QRHL
imports Complex_Main
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

(*instantiation "fun" :: (type,zero)zero begin
definition[simp]: "zero_fun (x::'a) = (0::'b)"
instance .. 
end*)
    
ML {* @{type_name "distr"} *}
  
section \<open>Subspaces\<close>
  
typedef 'a state = "{x::'a\<Rightarrow>complex. \<exists>b. \<forall>F. finite F \<longrightarrow> sum (\<lambda>i. (norm(x i))^2) F \<le> b }"
  by (rule exI[of _ "\<lambda>_.0"], auto)
setup_lifting type_definition_state

instantiation state :: (type)real_vector begin
lift_definition zero_state :: "'a state" is "\<lambda>_.0" by auto
lift_definition uminus_state :: "'a state \<Rightarrow> 'a state" is uminus by auto
lift_definition plus_state :: "'a state \<Rightarrow> 'a state \<Rightarrow> 'a state" is "\<lambda>f g x. f x + g x"
proof -
  fix f g :: "'a \<Rightarrow> complex"  fix fun1 fun2 :: "'a \<Rightarrow> complex"
    
  assume "\<exists>bf. \<forall>F. finite F \<longrightarrow> (\<Sum>i\<in>F. ((cmod (f i))^2)) \<le> bf"
  then obtain bf where bf: "\<forall>F. finite F \<longrightarrow> (\<Sum>i\<in>F. (cmod (f i)^2)) \<le> bf" ..
  assume "\<exists>bg. \<forall>F. finite F \<longrightarrow> (\<Sum>i\<in>F. ((cmod (g i))^2)) \<le> bg"
  then obtain bg where bg: "\<forall>F. finite F \<longrightarrow> (\<Sum>i\<in>F. (cmod (g i)^2)) \<le> bg" ..

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
  then show "\<exists>b. \<forall>F. finite F \<longrightarrow> (\<Sum>i\<in>F. (cmod (f i + g i))\<^sup>2) \<le> b" by auto
qed
definition "a - b = a + (-b)" for a b :: "'a state"
lift_definition scaleR_state :: "real \<Rightarrow> 'a state \<Rightarrow> 'a state" is "\<lambda>r f x. r *\<^sub>R f x"
proof -
  fix f :: "'a \<Rightarrow> complex" and r :: real
  assume "\<exists>b. \<forall>F. finite F \<longrightarrow> (\<Sum>i\<in>F. (cmod (f i))\<^sup>2) \<le> b"
  then obtain b where b: "\<And>F. finite F \<Longrightarrow> (\<Sum>i\<in>F. (cmod (f i))\<^sup>2) \<le> b" by auto
  have aux: "(r*x)^2 = r^2 * x^2" for r x :: real unfolding power2_eq_square by auto
  have "(\<Sum>i\<in>F. (cmod (r *\<^sub>R f i))\<^sup>2) \<le> \<bar>r\<bar>\<^sup>2 * b" if "finite F" for F
    apply (subst norm_scaleR)
    apply (subst aux)
    apply (subst sum_distrib_left[symmetric])
    apply (subst mult_left_mono)
    by (auto simp: b that)
  then show "\<exists>b. \<forall>F. finite F \<longrightarrow> (\<Sum>i\<in>F. (cmod (r *\<^sub>R f i))\<^sup>2) \<le> b"
    by auto
qed
instance apply intro_classes
          apply (transfer; rule ext; simp)
         apply (transfer; rule ext; simp)
        apply (transfer; rule ext; simp)
       apply (transfer; rule ext; simp)
      apply (unfold minus_state_def; transfer; rule ext; simp)
     apply (transfer; rule ext; simp add: scaleR_add_right)
    apply (transfer; rule ext; simp add: scaleR_add_left)
   apply (transfer; rule ext; simp)
  by (transfer; rule ext; simp)
end

  (* TODO: states should be normalized! *)

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

typedecl ('a,'b) isometry
type_synonym 'a isometry2 = "('a,'a) isometry"
    
section \<open>Quantum variables\<close>

typedecl 'a qvariable (* a variable, refers to a location in a memory *)
axiomatization variable_name :: "'a qvariable \<Rightarrow> string"
typedecl 'a qvariables (* represents a tuple of variables, of joint type 'a *)

axiomatization
    qvariable_names :: "'a qvariables \<Rightarrow> string list"
and qvariable_cons :: "'a qvariables \<Rightarrow> 'b qvariables \<Rightarrow> ('a \<times> 'b) qvariables"
and qvariable_singleton :: "'a qvariable \<Rightarrow> 'a qvariables"

nonterminal qvariable_list_args
syntax
  "_qvariables"      :: "qvariable_list_args \<Rightarrow> 'a"        ("(1'[[_']])")
  "_qvariables"      :: "qvariable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_'\<rbrakk>)")
  "_qvariable_list_arg"  :: "'a \<Rightarrow> qvariable_list_args"                   ("_")
  "_qvariable_list_args" :: "'a \<Rightarrow> qvariable_list_args \<Rightarrow> qvariable_list_args"     ("_,/ _")

translations
  "_qvariables (_qvariable_list_args x y)" \<rightleftharpoons> "CONST qvariable_cons (_qvariables (_qvariable_list_arg x)) (_qvariables y)"
  "_qvariables (_qvariable_list_arg x)" \<rightleftharpoons> "CONST qvariable_singleton x"
  

axiomatization where
  qvariable_names_cons: "qvariables_names (qvariable_cons X Y) = qvariable_names X @ qvariable_names Y"
  and qvariable_singleton_name: "qvariable_names (qvariable_singleton x) = [qvariable_name x]"
  for X::"'a qvariables" and Y::"'b qvariables" and x::"'c qvariable"

definition "qvariables_distinct X == distinct (qvariable_names X)"
  
section \<open>Assertions\<close>
    
typedecl mem2
type_synonym assertion = "mem2 subspace"

subsection \<open>Classical assertions\<close>
  
definition classical_subspace :: "bool \<Rightarrow> assertion"  ("\<CC>\<ll>\<aa>[_]")
  where "\<CC>\<ll>\<aa>[b] = (if b then top else bot)"
syntax classical_subspace :: "bool \<Rightarrow> assertion"  ("Cla[_]")
    
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


subsection \<open>Quantum equality\<close>

axiomatization quantum_equality :: "'a qvariables \<Rightarrow> 'a qvariables \<Rightarrow> assertion" (infix "\<equiv>\<qq>" 100)
syntax quantum_equality :: "'a qvariables \<Rightarrow> 'a qvariables \<Rightarrow> assertion" (infix "==q" 100)
syntax "_quantum_equality" :: "qvariable_list_args \<Rightarrow> qvariable_list_args \<Rightarrow> assertion" ("Qeq'[_=_']")
translations
  "_quantum_equality a b" \<rightharpoonup> "CONST quantum_equality (_qvariables a) (_qvariables b)"

subsection \<open>Subspace division\<close>

axiomatization space_div :: "assertion \<Rightarrow> 'a state \<Rightarrow> 'a qvariables \<Rightarrow> assertion" ("_ \<div> _@_")
  
(* term "space_div (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) EPR \<lbrakk>A1, B1\<rbrakk>" *)
  
section \<open>Common quantum objects\<close>

axiomatization EPR :: "(bit*bit) state"
lift_definition ket :: "'a \<Rightarrow> 'a state" ("|_\<rangle>") is "\<lambda>x y. if x=y then 1 else 0"
proof (rule exI[of _ 1], rule allI, rule impI)
  fix a::'a and F::"'a set" assume "finite F"
  have "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 0" if "a\<notin>F"
    apply (subst sum.cong[where B=F and h="\<lambda>_. 0"]) using that by auto
  moreover have "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 1" if "a\<in>F"
  proof -
    obtain F0 where "a\<notin>F0" and F_F0: "F=insert a F0"
      by (meson \<open>a \<in> F\<close> mk_disjoint_insert) 
    show "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 1"
      unfolding F_F0
      apply (subst sum.insert_remove)
       using F_F0 `finite F` apply auto
      apply (subst sum.cong[where B=F0 and h="\<lambda>_. 0"])
        apply (simp add: \<open>a \<notin> F0\<close>)
       using \<open>a \<notin> F0\<close> apply auto[1]
      by simp
  qed
  ultimately show "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) \<le> 1"
    by linarith
qed

axiomatization CNOT :: "(bit*bit) isometry2"
axiomatization H :: "bit isometry2"
  
ML_file \<open>qrhl.ML\<close>
  
section \<open>Experiments\<close>
  
definition test where "test (x::int) = x"

lemma testsimp[simp]: "test x = x"
  using test_def by auto

end
