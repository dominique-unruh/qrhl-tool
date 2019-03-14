theory LValue
  imports Main "HOL-Library.Rewrite" (* "HOL-Cardinals.Cardinals" *)
    (* "Jordan_Normal_Form.Matrix_Impl" *) Complex_Main
    (* "HOL-Library.Indicator_Function" *)
begin

(* no_syntax "\<^const>Group.m_inv" :: "('a, 'b) monoid_scheme => 'a => 'a" ("inv\<index> _" [81] 80) *)

typedef 'a index = "UNIV::'a set" ..
typedef 'a factor = "UNIV::'a set" ..
typedef 'a target = "UNIV::'a set" ..

inductive_set dependent_functions' :: "'b \<Rightarrow> 'a set \<Rightarrow> ('a\<Rightarrow>'b set) \<Rightarrow> ('a\<Rightarrow>'b) set"
  for undef :: 'b and domain :: "'a set" and range :: "'a \<Rightarrow> 'b set" where
  "\<lbrakk> \<And>a. a\<notin>domain \<Longrightarrow> f a = undef;
     \<And>a. a\<in>domain \<Longrightarrow> f a \<in> range a \<rbrakk>
   \<Longrightarrow> f \<in> dependent_functions' undef domain range"

abbreviation "dependent_functions == dependent_functions' undefined" 

definition "restrict f S x = (if x\<in>S then f x else undefined)"

lemma restrict_simp[simp]:
  "x : D \<Longrightarrow> restrict f D x = f x"
  unfolding restrict_def by simp

lemma restrict_simp_outside[simp]:
  "x \<notin> D \<Longrightarrow> restrict f D x = undefined"
  unfolding restrict_def by simp

lemma restrict_image[simp]: "restrict f X ` X = f ` X"
  apply (rule image_cong, simp)
  unfolding restrict_def by simp

lemma inj_on_restrict: "inj_on (restrict f X) X = inj_on f X"
proof
  assume inj: "inj_on (restrict f X) X"
  show "inj_on f X"
    apply (rule inj_onI)
    apply (rule inj[THEN inj_onD])
    unfolding restrict_def by auto
next
  assume inj: "inj_on f X"
  show "inj_on (restrict f X) X"
    apply (rule inj_onI)
    apply (rule inj[THEN inj_onD])
    unfolding restrict_def by auto
qed


lemma dependent_functions_restrict:
  assumes "f \<in> dependent_functions D R"
  assumes D': "D' \<subseteq> D"
  shows "restrict f D' \<in> dependent_functions D' R"
  apply (rule dependent_functions'.intros)
  unfolding restrict_def apply auto
  by (meson assms contra_subsetD dependent_functions'.cases)

lemma dependent_functions_restrict_twice[simp]:
  "restrict (restrict f D) D'
      = restrict f (D\<inter>D')"
  unfolding restrict_def by auto

lemma dependent_functions_restrict_surj:
  assumes D: "D \<subseteq> D'"
  assumes A: "\<And>i. i\<in>D' \<Longrightarrow> A i \<noteq> {}"
  shows "(\<lambda>f. restrict f D) ` dependent_functions D' A = dependent_functions D A"
proof auto
  fix f assume f: "f \<in> dependent_functions D' A"
  show "restrict f D \<in> dependent_functions D A"
    unfolding restrict_def 
    apply (rule dependent_functions'.intros)
    using f apply cases apply simp
    using f apply cases using D by auto
next
  fix f assume f: "f \<in> dependent_functions D A"
  define f' where "f' i = (if i\<in>D then f i else if i\<in>D' then (SOME x. x:A i) else undefined)" for i
  have "f = restrict f' D"
    unfolding restrict_def f'_def
    apply (rule ext) using f apply cases by auto
  moreover have "f' \<in> dependent_functions D' A"
    unfolding f'_def 
    apply (rule dependent_functions'.intros) 
    using D apply auto
    apply (meson dependent_functions'.cases f)
    by (simp add: A some_in_eq)
  ultimately show "f \<in> (\<lambda>f. restrict f D) ` dependent_functions D' A"
    by (rule image_eqI[where x=f'])
qed

    

lemma dependent_functions_nonempty:
  assumes "\<And>i. i\<in>I \<Longrightarrow> A i \<noteq> {}"
  shows "dependent_functions' u I A \<noteq> {}"
proof -
  from assms obtain f where f: "f i \<in> A i" if "i\<in>I" for i
    apply atomize_elim apply (rule choice) by auto
  have "(\<lambda>i. if i:I then f i else u) : dependent_functions' u I A"
    apply (rule dependent_functions'.intros)
    using f by auto
  thus ?thesis
    by auto
qed

definition "leq_card A B = (\<exists>f. inj_on f A \<and> f`A \<subseteq> B)" (* Equivalent to (card_of A \<le>o card_of B). TODO use that? *)

lemma leq_cardI: assumes "inj_on f A" and "f`A \<subseteq> B" shows "leq_card A B"
  unfolding leq_card_def using assms by auto
lemma leq_cardI_surj: assumes "f`B \<supseteq> A" shows "leq_card A B"
  unfolding leq_card_def using assms
  by (meson image_subsetI inj_on_inv_into inv_into_into rev_subsetD) 
lemma leq_cardI_bij: assumes "bij_betw f A B" shows "leq_card A B"
  using assms bij_betw_imp_inj_on bij_betw_imp_surj_on leq_card_def by fastforce
lemma leq_cardI_bij': assumes "bij_betw f B A" shows "leq_card A B"
  using assms bij_betw_inv leq_cardI_bij by blast

(* lemma leq_card_fst: assumes "A2\<noteq>{}" assumes "leq_card (A1\<times>A2) B" shows "leq_card A1 B"
   *)

(* lemma leq_card_prod: assumes "B\<noteq>{}" shows "leq_card A (A\<times>B)"
   *)

lemma leq_card_prod2: assumes "A\<noteq>{}" shows "leq_card B (A\<times>B)"
proof -
  obtain a where a: "a \<in> A" using assms by auto
  show ?thesis
    unfolding leq_card_def
    apply (rule exI[of _ "%b. (a,b)"])
    by (auto simp: a inj_on_def)
qed

lemma leq_card_trans[trans]: assumes "leq_card A B" and "leq_card B C" shows "leq_card A C"
  unfolding leq_card_def proof -
  from assms obtain f1 f2 where inj_f1: "inj_on f1 A" and rg_f1: "f1 ` A \<subseteq> B" 
    and inj_f2: "inj_on f2 B" and rg_f2: "f2 ` B \<subseteq> C"
    apply atomize_elim unfolding leq_card_def by auto
  from inj_f1 have "inj_on (f2 o f1) A"
    apply (rule comp_inj_on)
    using inj_f2 inj_on_subset rg_f1 by auto
  moreover
  from rg_f1 rg_f2 have "(f2 o f1) ` A \<subseteq> C"
    by fastforce
  ultimately show "\<exists>f. inj_on f A \<and> f ` A \<subseteq> C" by auto
qed
lemma leq_card_refl[intro]: "leq_card A A"
  unfolding leq_card_def by force

lemma leq_card_UNIV[simp]: "leq_card (A::'a set) (UNIV::'a set)"
  unfolding leq_card_def apply (rule exI[of _ id]) by simp

lemma bij_betw_dependent_functions: 
  assumes bij_f: "\<And>i. i \<in> I \<Longrightarrow> bij_betw (f i) (A i) (B i)"
  assumes f_undef: "\<And>i x. i \<notin> I \<Longrightarrow> f i x = u2"
  shows "bij_betw (\<lambda>g i. f i (g i)) (dependent_functions' u1 I A) (dependent_functions' u2 I B)"
proof (rule bij_betwI')
  fix x y
  assume x: "x \<in> dependent_functions' u1 I A"
  show "(\<lambda>i. f i (x i)) \<in> dependent_functions' u2 I B"
    apply (rule dependent_functions'.intros)
    apply (simp add: assms(2))
    by (meson x assms(1) bij_betwE dependent_functions'.cases)
  assume y: "y \<in> dependent_functions' u1 I A"
  from bij_f have inj_f: "inj_on (f i) (A i)" if "i:I" for i
    by (simp add: bij_betw_def that)
  have "x = y" if "(\<lambda>i. f i (x i)) = (\<lambda>i. f i (y i))"
    apply (rule ext)
    using that inj_f
    by (metis (full_types) dependent_functions'.cases inj_on_eq_iff x y)
  then show "((\<lambda>i. f i (x i)) = (\<lambda>i. f i (y i))) = (x = y)"
    by auto
next
  fix y
  assume y: "y \<in> dependent_functions' u2 I B"
  have "\<exists>x'. (y i = f i x' \<and> (i\<in>I \<longrightarrow> x' \<in> A i) \<and> (i\<notin>I \<longrightarrow> x' = u1))" for i
    apply (cases "i\<in>I")
    apply (metis bij_betw_def bij_f dependent_functions'.cases image_iff y)
    using dependent_functions'.simps f_undef y by fastforce 
  then obtain x where x: "(y i = f i (x i) \<and> (i\<in>I \<longrightarrow> x i \<in> A i) \<and> (i\<notin>I \<longrightarrow> x i = u1))" for i
    apply atomize_elim apply (rule choice) by simp
  then have "x\<in>dependent_functions' u1 I A" 
    apply (rule_tac dependent_functions'.intros) by auto
  moreover
  from x have "y = (\<lambda>i. f i (x i))"
    by auto
  ultimately show "\<exists>x\<in>dependent_functions' u1 I A. y = (\<lambda>i. f i (x i))"
    by auto
qed

(* lemma bij_dependent_functions_split:
  assumes "bij_betw (\<lambda>x i. (f1 i (x i), f2 i (x i))) (dependent_functions' u I A) (dependent_functions' (v1,v2) I (\<lambda>i. B i \<times> C i))"
  shows "bij_betw (\<lambda>x. (\<lambda>i. f1 i (x i), \<lambda>i. f2 i (x i))) (dependent_functions' u I A) (dependent_functions' v1 I B \<times> dependent_functions' v2 I C)" 
   *)

lemma dependent_functions_mono_domain:
  assumes "I \<subseteq> J"
  assumes "\<And>i. i \<in> J-I \<Longrightarrow> A i \<noteq> {}"
  shows "leq_card (dependent_functions I A) (dependent_functions J A)"
proof -
  define f where "f x i = (if i \<in> J-I then (SOME a. a : A i) else x i)" for x i
  have inj: "inj_on f (dependent_functions I A)"
  proof (rule inj_onI, rule ext)
    fix x y i
    assume xdep: "x \<in> dependent_functions I A" and ydep: "y \<in> dependent_functions I A" and feq: "f x = f y"
    show "x i = y i"
    proof (cases "i \<in> J-I")
      case True
      then have "i \<notin> I" by simp
      with xdep ydep have "x i = undefined" and "y i = undefined"
        by (simp add: dependent_functions'.simps)+
      then show "x i = y i" by simp
    next
      case False
      then have "f x i = x i" and "f y i = y i"
        unfolding f_def by auto
      with feq show "x i = y i" by simp
    qed
  qed 
  have range: "f ` dependent_functions I A \<subseteq> dependent_functions J A"
  proof (rule subsetI, drule imageE, rename_tac y x)
    fix x y assume y: "y = f x" and xdep: "x \<in> dependent_functions I A"
    show "y \<in> dependent_functions J A"
    proof (unfold y, rule dependent_functions'.intros; rename_tac i)
      fix i assume "i \<notin> J"
      with xdep show "f x i = undefined"
        unfolding f_def apply auto
        by (meson assms(1) contra_subsetD dependent_functions'.cases)
    next
      fix i assume "i \<in> J"
      with xdep show "f x i \<in> A i"
        unfolding f_def apply auto
        apply (simp add: assms(2) some_in_eq)
        by (simp add: dependent_functions'.simps)
    qed
  qed
  from inj range show ?thesis
    unfolding leq_card_def by auto
qed

lemma dependent_functions_mono:
  assumes "\<And>i. i\<in>I \<Longrightarrow> leq_card (A i) (B i)"
  shows "leq_card (dependent_functions I A) (dependent_functions I B)"
proof -
  obtain f where f: "inj_on (f i) (A i) \<and> f i ` A i \<subseteq> B i" if "i\<in>I" for i
    unfolding leq_card_def apply atomize_elim unfolding Ball_def[symmetric]
    apply (rule bchoice)
    using assms[unfolded leq_card_def] by simp
  define F where "F g = (\<lambda>i. if i\<in>I then f i (g i) else undefined)" for g
  have "F g \<in> dependent_functions I B" if "g \<in> dependent_functions I A" for g
    unfolding F_def apply (rule dependent_functions'.intros) apply auto
    using that apply cases using f by blast
  then have "F ` dependent_functions I A \<subseteq> dependent_functions I B"
    by auto
  moreover
  have "F g1 = F g2 \<Longrightarrow> g1 = g2"
    if "g1 \<in> dependent_functions I A" and "g2 \<in> dependent_functions I A" for g1 g2
    using that(1) apply cases using that(2) apply cases 
    unfolding F_def apply (rule ext)
    by (metis (no_types, lifting) f inj_on_contraD)
  then have "inj_on F (dependent_functions I A)"
    by (rule inj_onI)
  ultimately
  show ?thesis
    unfolding leq_card_def by auto
qed

definition "dependent_functions_split I f = ((\<lambda>i. if i\<in>I then fst (f i) else undefined),
                                             (\<lambda>i. if i\<in>I then snd (f i) else undefined))"

lemma bij_betw_dependent_functions_split:
  assumes "\<And>i. i\<in>I \<Longrightarrow> AB i = A i \<times> B i"
  shows "bij_betw (dependent_functions_split I) (dependent_functions' u I AB)
     (dependent_functions I A \<times> dependent_functions I B)"
proof (rule bij_betwI')
  fix x y :: "'a \<Rightarrow> 'b \<times> 'c"
  assume x: "x \<in> dependent_functions' u I AB"
  then have x_undef: "i \<notin> I \<Longrightarrow> x i = u" for i
    by cases
  assume y: "y \<in> dependent_functions' u I AB"
  then have y_undef: "i \<notin> I \<Longrightarrow> y i = u" for i
    by cases
  show "(dependent_functions_split I x = dependent_functions_split I y) = (x = y)"
    unfolding o_def dependent_functions_split_def 
    apply auto
    by (metis prod_eq_iff x_undef y_undef ext)
  have "(\<lambda>i. if i \<in> I then fst (x i) else undefined) \<in> dependent_functions I A"
    using x apply cases apply (subst dependent_functions'.simps)
    using assms by force
  moreover
  have "(\<lambda>i. if i \<in> I then snd (x i) else undefined) \<in> dependent_functions I B"
    using x apply cases apply (subst dependent_functions'.simps)
    using assms by force
  ultimately
  show "dependent_functions_split I x \<in> dependent_functions I A \<times> dependent_functions I B"
    unfolding dependent_functions_split_def
    by simp
next
  fix g
  assume "g \<in> dependent_functions I A \<times> dependent_functions I B"
  then obtain g1 g2 where g: "g = (g1,g2)" and g1: "g1 \<in> dependent_functions I A" and g2: "g2 \<in> dependent_functions I B"
    by auto
  obtain f1 where f1: "g1 i = (if i \<in> I then f1 i else undefined)" for i
    by (metis dependent_functions'.cases g1)
  obtain f2 where f2: "g2 i = (if i \<in> I then f2 i else undefined)" for i
    by (metis dependent_functions'.cases g2)
  define f where "f i = (if i:I then (f1 i, f2 i) else u)" for i
  have fAB: "f \<in> dependent_functions' u I AB"
    apply (rule dependent_functions'.intros) unfolding f_def using assms apply auto
    apply (metis dependent_functions'.cases f1 g1)
    by (metis dependent_functions'.cases f2 g2)
  show "\<exists>f\<in>dependent_functions' u I AB. g = dependent_functions_split I f"
    unfolding g dependent_functions_split_def apply (rule bexI[of _ f])
    using f1 f2 apply (fastforce simp: f_def)
    using fAB by assumption
qed

lemma dependent_functions_split:
  assumes disjoint: "I\<inter>J={}"
  shows "bij_betw (\<lambda>f. (restrict f I, restrict f J))
      (dependent_functions (I\<union>J) A)
      (dependent_functions I A \<times> dependent_functions J A)"
proof (rule bij_betwI', auto)
  fix x y assume x: "x \<in> dependent_functions (I \<union> J) A"
    and y: "y \<in> dependent_functions (I \<union> J) A"
    and eqI: "restrict x I = restrict y I"
    and eqJ: "restrict x J = restrict y J"
  show "x = y"
  proof (rule ext)
    fix i
    consider (I) "i : I" | (J) "i : J" | (none) "i \<notin> I\<union>J" by auto
    then show "x i = y i"
    proof cases
      case I
      then show ?thesis
        using eqI unfolding restrict_def by metis
    next
      case J
      then show ?thesis
        using eqJ unfolding restrict_def by metis
    next
      case none
      show ?thesis
        using x apply cases using y apply cases
        using none by metis
    qed
  qed
next
  fix x assume "x \<in> dependent_functions (I \<union> J) A"
  then show "restrict x I \<in> dependent_functions I A"
    by (rule dependent_functions_restrict, simp)
next
  fix x assume "x \<in> dependent_functions (I \<union> J) A"
  then show "restrict x J \<in> dependent_functions J A"
    by (rule dependent_functions_restrict, simp)
next
  fix a b assume a: "a \<in> dependent_functions I A" and b: "b \<in> dependent_functions J A"
  define x where "x i = (if i\<in>I then a i else if i\<in>J then b i else undefined)" for i
  have "x\<in>dependent_functions (I \<union> J) A"
    using a apply cases using b apply cases
    apply (rule dependent_functions'.intros)
    unfolding x_def by auto
  moreover have "a = restrict x I"
    apply (rule ext, rename_tac i)
    unfolding restrict_def x_def
    using a apply cases
    by simp
  moreover have "b = restrict x J"
    apply (rule ext, rename_tac i)
    unfolding restrict_def x_def
    using b apply cases
    using disjoint by auto
  ultimately show "\<exists>x\<in>dependent_functions (I \<union> J) A.
              a = restrict x I \<and> b = restrict x J"
    by auto
qed

lemma bij_betw_map_prod[intro]:
  assumes "bij_betw f1 A1 B1"
  assumes "bij_betw f2 A2 B2"
  shows "bij_betw (map_prod f1 f2) (A1 \<times> A2) (B1 \<times> B2)"
proof (rule bij_betw_imageI)
  show "inj_on (map_prod f1 f2) (A1 \<times> A2)"
    apply (rule map_prod_inj_on)
    using assms bij_betw_def by auto
  show "map_prod f1 f2 ` (A1 \<times> A2) = B1 \<times> B2"
    apply (rule map_prod_surj_on)
    using assms by (simp_all add: bij_betw_def)
qed

record 'a lvalue_factorization =
  lvf_domain :: "'a set"
  lvf_index_set :: "'a index set"
  lvf_sets :: "'a index \<Rightarrow> 'a factor set"
  lvf_isomorphism :: "'a \<Rightarrow> ('a index \<Rightarrow> 'a factor)"

inductive valid_lvalue_factorization :: "'a lvalue_factorization \<Rightarrow> bool" where
  "\<lbrakk> domain \<noteq> {};
     \<And>i. i\<notin>I \<Longrightarrow> sets i = undefined;
     \<And>x. x\<notin>domain \<Longrightarrow> isom x = undefined;
     leq_card I domain;
     bij_betw isom domain (dependent_functions I sets)
   \<rbrakk> \<Longrightarrow> valid_lvalue_factorization \<lparr> lvf_domain=domain, lvf_index_set=I, lvf_sets=sets, lvf_isomorphism=isom \<rparr>"

lemma lvalue_factorization_sets_nonempty:
  assumes valid: "valid_lvalue_factorization F"
  assumes i: "i \<in> lvf_index_set F"
  shows "lvf_sets F i \<noteq> {}"
  using valid 
proof cases
  case (1 domain I sets isom)
  from i have i: "i:I" unfolding 1 by simp
  from \<open>domain \<noteq> {}\<close> and \<open>bij_betw isom domain (dependent_functions I sets)\<close>
  have "dependent_functions I sets \<noteq> {}"
    using bij_betw_empty2 by fastforce
  then obtain f where "f \<in> dependent_functions I sets" by auto
  then have "sets i \<noteq> {}"
    apply cases using i by auto
  then show ?thesis
    unfolding 1 by auto
qed

record ('a,'b) lvalue_basic = 
  lv_factorization :: "'a lvalue_factorization"
  lv_factors :: "'a index set"
  lv_representation :: "('a index \<Rightarrow> 'a factor) \<Rightarrow> 'b"

inductive valid_lvalue_basic :: "('a,'b) lvalue_basic \<Rightarrow> bool" where
  "\<lbrakk> valid_lvalue_factorization factorization;
     factors \<subseteq> lvf_index_set factorization;
     inj_on repr (dependent_functions factors (lvf_sets factorization));
     \<And>x. x \<notin> (dependent_functions factors (lvf_sets factorization)) \<Longrightarrow> repr x = undefined
  \<rbrakk> \<Longrightarrow> valid_lvalue_basic \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr>"

definition "lvalue_basic_domain lv = lvf_domain (lv_factorization lv)"
definition "lvalue_basic_range lv = (lv_representation lv) ` (dependent_functions (lv_factors lv) (lvf_sets (lv_factorization lv)))"

lemma lvalue_basic_range_leq_domain:
  assumes "valid_lvalue_basic lv"
  shows "leq_card (lvalue_basic_range lv) (lvalue_basic_domain lv)"
(* TODO same for lvalue *)
  using assms
proof (cases lv)
  case (1 factorization factors repr)
  note valid = 1
  from \<open>valid_lvalue_factorization factorization\<close>
  show ?thesis
  proof cases
    case (1 domain I sets isom)
    note factor = this
    note leq_card_trans[rotated,trans]
    have "lvalue_basic_domain lv = domain"
      unfolding factor valid lvalue_basic_domain_def by simp
    also from \<open>bij_betw isom domain (dependent_functions I sets)\<close>
    have "leq_card (dependent_functions I sets) domain"
      using leq_cardI_bij' by blast
    also have "leq_card (dependent_functions factors sets) (dependent_functions I sets)"
      apply (rule dependent_functions_mono_domain)
      using factor(1) valid(3) apply auto[1]
      using factor(1) lvalue_factorization_sets_nonempty valid(2) by fastforce
    also have "leq_card (repr ` dependent_functions factors sets) (dependent_functions factors sets)"
      using factor(1) inj_on_imp_bij_betw leq_cardI_bij' valid(4) by fastforce
    also have "repr ` dependent_functions factors sets = lvalue_basic_range lv"
      unfolding factor valid lvalue_basic_range_def by simp
    finally show ?thesis by assumption
  qed
qed

inductive lvalue_basic_compatible :: "('a,'b) lvalue_basic \<Rightarrow> ('a,'c) lvalue_basic \<Rightarrow> bool" where
  "\<lbrakk> valid_lvalue_basic lv1; valid_lvalue_basic lv2;
     lv_factorization lv1 = lv_factorization lv2;
     lv_factors lv1 \<inter> lv_factors lv2 = {}
  \<rbrakk> \<Longrightarrow> lvalue_basic_compatible lv1 lv2"

lemma lvalue_basic_compatible_sym:
  assumes "lvalue_basic_compatible lvb1 lvb2"
  shows "lvalue_basic_compatible lvb2 lvb1"
  using assms apply cases apply (rule lvalue_basic_compatible.intros) by auto

fun lvalue_basic_map :: "('b\<Rightarrow>'c) \<Rightarrow> ('a,'b) lvalue_basic \<Rightarrow> ('a,'c) lvalue_basic" where
  "lvalue_basic_map f \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr>
    =  \<lparr> lv_factorization=factorization, lv_factors=factors, 
         lv_representation=restrict (f o repr) (dependent_functions factors (lvf_sets factorization)) \<rparr>"

lemma lvalue_basic_map_o[simp]:
  "lvalue_basic_map f (lvalue_basic_map g lvb) = lvalue_basic_map (f o g) lvb"
  apply (cases lvb) by (auto simp: restrict_def o_def)

lemma lvalue_basic_map_cong:
  assumes "\<And>x. x\<in>lvalue_basic_range lvb \<Longrightarrow> f x = g x"
  shows "lvalue_basic_map f lvb = lvalue_basic_map g lvb"
  using assms 
  apply (cases lvb)
  unfolding lvalue_basic_range_def by (auto simp: o_def restrict_def)

lemma lvalue_basic_map_id:
  assumes "valid_lvalue_basic lvb"
  shows "lvalue_basic_map id lvb = lvb"
  using assms apply (cases, hypsubst_thin)
  by (auto simp: restrict_def)

lemma valid_lvalue_basic_map:
  assumes "valid_lvalue_basic lvb"
  assumes "inj_on f (lvalue_basic_range lvb)"
  shows "valid_lvalue_basic (lvalue_basic_map f lvb)"
  using assms(1)
proof cases
  case (1 factorization factors repr)
  then have inj_repr: "inj_on repr (dependent_functions factors (lvf_sets factorization))" by simp
  have inj: "inj_on (\<lambda>x. if x \<in> dependent_functions factors (lvf_sets factorization) 
                    then f (repr x) else undefined)
     (dependent_functions factors (lvf_sets factorization))"
    apply (rule inj_onI, simp)
    apply (rule inj_repr[THEN inj_onD])
      apply (rule assms(2)[THEN inj_onD])
    unfolding 1 lvalue_basic_range_def
    by auto
  show ?thesis
    unfolding 1 apply simp
    apply (rule valid_lvalue_basic.intros) 
    using 1 inj by (auto simp: restrict_def[abs_def] o_def)
qed
(* TODO same for lvalue *)

lemma lvalue_basic_range_map[simp]: "lvalue_basic_range (lvalue_basic_map f lvb) = f ` lvalue_basic_range lvb"
  apply (cases lvb) by (auto simp: lvalue_basic_range_def image_image restrict_def o_def)
(* TODO same for lvalue *)
lemma lvalue_basic_domain_map[simp]: "lvalue_basic_domain (lvalue_basic_map f lvb) = lvalue_basic_domain lvb"
  apply (cases lvb) by (simp add: lvalue_basic_domain_def o_def)
(* TODO same for lvalue *)


fun lvalue_basic_fun where
  "lvalue_basic_fun \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr> x
  = repr (restrict (lvf_isomorphism factorization x) factors)"

fun lvalue_basic_corange_raw where
  "lvalue_basic_corange_raw \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr>
  = (dependent_functions (lvf_index_set factorization - factors) (lvf_sets factorization))"

definition lvalue_basic_cofun_squash :: "('a, 'b) lvalue_basic \<Rightarrow> ('a LValue.index \<Rightarrow> 'a factor) \<Rightarrow> 'a"  where
  "lvalue_basic_cofun_squash lv = (SOME f. inj_on f (lvalue_basic_corange_raw lv))"

lemma lvalue_basic_cofun_squash:
  assumes "valid_lvalue_basic lvb"
  shows "inj_on (lvalue_basic_cofun_squash lvb) (lvalue_basic_corange_raw lvb)"
  using assms
proof cases
  case (1 factorization factors repr)
  note lvb = 1
  from \<open>valid_lvalue_factorization factorization\<close>
  have "leq_card (lvalue_basic_corange_raw lvb) (UNIV::'a set)"
  proof cases
    case (1 domain I sets isom)
    have "lvalue_basic_corange_raw lvb = dependent_functions (I - factors) sets"
      unfolding lvb 1 by simp
    also have "leq_card \<dots> (dependent_functions I sets)"
      apply (rule leq_cardI_surj[where f="%f. restrict f (I-factors)"])
      apply (rule equalityD2)
      apply (rule dependent_functions_restrict_surj)
      apply auto[1]
      using "1"(1) lvalue_factorization_sets_nonempty lvb(2) by fastforce
    also have "leq_card \<dots> domain"
      using \<open>bij_betw isom domain (dependent_functions I sets)\<close>
      using leq_cardI_bij' by auto
    also have "leq_card \<dots> (UNIV::'a set)"
      by simp
    finally show ?thesis.
  qed
  then have "\<exists>f::_\<Rightarrow>'a. inj_on f (lvalue_basic_corange_raw lvb)"
    unfolding leq_card_def by auto
  then show ?thesis
    unfolding lvalue_basic_cofun_squash_def
    by (rule someI_ex[where P="%f. inj_on f (lvalue_basic_corange_raw lvb)"])
qed

fun lvalue_basic_corange where
  "lvalue_basic_corange lv = lvalue_basic_cofun_squash lv ` lvalue_basic_corange_raw lv"

fun lvalue_basic_cofun_raw where
  "lvalue_basic_cofun_raw \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr> x
    = restrict (lvf_isomorphism factorization x) (lvf_index_set factorization - factors)"

definition "lvalue_basic_cofun lv x = (lvalue_basic_cofun_squash lv (lvalue_basic_cofun_raw lv x))"

lemma lvalue_basic_fun_raw_bij:
  assumes "valid_lvalue_basic lvb"
  shows "bij_betw (\<lambda>x. (lvalue_basic_fun lvb x, lvalue_basic_cofun_raw lvb x)) 
                  (lvalue_basic_domain lvb) (lvalue_basic_range lvb \<times> lvalue_basic_corange_raw lvb)"
  using assms
proof cases
  case (1 factorization factors repr)
  note lvb = 1
  from \<open>valid_lvalue_factorization factorization\<close> 
  show ?thesis
  proof cases
    case (1 domain I sets isom)
    note factorization = 1
    note bij_betw_trans[trans]
    from 1 have "bij_betw isom domain (dependent_functions I sets)" by simp
    also have "bij_betw (\<lambda>f. (restrict f factors, restrict f (I-factors)))
      (dependent_functions I sets)
      (dependent_functions factors sets \<times> dependent_functions (I-factors) sets)"
    proof -
      have uni: "I = factors \<union> (I-factors)"
        using factorization(1) lvb(3) by auto
      show ?thesis
        apply (subst uni, rule dependent_functions_split)
        by simp
    qed
    also 
    have "bij_betw (map_prod repr id)
        (dependent_functions factors sets \<times> dependent_functions (I-factors) sets)
        (lvalue_basic_range lvb \<times> lvalue_basic_corange_raw lvb)"
    proof -
      have inj: "inj_on (map_prod repr id) (dependent_functions factors sets \<times> dependent_functions (I - factors) sets)"
        apply (rule map_prod_inj_on)
        using factorization(1) lvb(4) by auto
      show ?thesis
        unfolding lvb factorization 
        apply  (simp add: lvalue_basic_domain_def lvalue_basic_range_def o_def)
        using inj apply (rule bij_betw_imageI)
        by (simp add: map_prod_surj_on)
    qed
    finally show ?thesis
      unfolding lvb factorization 
      by (simp add: lvalue_basic_domain_def lvalue_basic_range_def o_def)
  qed
qed

lemma lvalue_basic_fun_bij:
  assumes "valid_lvalue_basic lvb"
  shows "bij_betw (\<lambda>x. (lvalue_basic_fun lvb x, lvalue_basic_cofun lvb x)) 
                  (lvalue_basic_domain lvb) (lvalue_basic_range lvb \<times> lvalue_basic_corange lvb)"
(* TODO same for lvalue *)
proof -
  note bij_betw_trans[trans]
  note lvalue_basic_fun_raw_bij[OF assms]
  also have "bij_betw (apsnd (lvalue_basic_cofun_squash lvb))
                      (lvalue_basic_range lvb \<times> lvalue_basic_corange_raw lvb)
                      (lvalue_basic_range lvb \<times> lvalue_basic_corange lvb)"
    unfolding lvalue_basic_cofun_squash apsnd_def
    apply (rule bij_betw_map_prod)
    by (auto simp: assms inj_on_imp_bij_betw lvalue_basic_cofun_squash)
  finally show ?thesis
    unfolding lvalue_basic_cofun_def o_def by simp
qed

fun lvalue_basic_compose :: "('a,'b) lvalue_basic \<Rightarrow> ('a,'c) lvalue_basic \<Rightarrow> ('a,'b*'c) lvalue_basic" where
  "lvalue_basic_compose \<lparr> lv_factorization=factorization1, lv_factors=factors1, lv_representation=repr1 \<rparr>
                        \<lparr> lv_factorization=factorization2, lv_factors=factors2, lv_representation=repr2 \<rparr> 
    =  \<lparr> lv_factorization=factorization1, lv_factors=factors1 \<union> factors2, 
         lv_representation=restrict (\<lambda>x. (repr1 (restrict x factors1), 
                                          repr2 (restrict x factors2)))
                                      (dependent_functions (factors1\<union>factors2) (lvf_sets factorization1)) \<rparr>"

lemma lvalue_basic_compose_fun:
  assumes compat: "lvalue_basic_compatible lv1 lv2"
  assumes x: "x : lvalue_basic_domain lv1"
  shows "lvalue_basic_fun (lvalue_basic_compose lv1 lv2) x = (lvalue_basic_fun lv1 x, lvalue_basic_fun lv2 x)"
  using assms
(* TODO same for lvalue *)
proof cases
  from compat have same_fact: "lv_factorization lv1 = lv_factorization lv2" by cases   
  obtain factorization factors1 repr1 where
    lv1: "lv1 = \<lparr> lv_factorization=factorization, lv_factors=factors1, lv_representation=repr1 \<rparr>"
    apply atomize_elim apply (cases lv1) by simp
  with same_fact obtain factors2 repr2 where
    lv2: "lv2 = \<lparr> lv_factorization=factorization, lv_factors=factors2, lv_representation=repr2 \<rparr>"
    apply atomize_elim apply (cases lv1) apply auto
    by (metis (full_types) lvalue_basic.surjective old.unit.exhaust)

  from compat have factors_disj: "factors1 \<inter> factors2 = {}" apply cases unfolding lv1 lv2 by simp

  from compat have valid1: "valid_lvalue_basic lv1" apply cases by simp
  then have "valid_lvalue_factorization factorization" unfolding lv1 apply cases by simp
  then obtain domain I sets isom where
    factorization: "factorization = \<lparr>lvf_domain = domain, lvf_index_set = I, lvf_sets = sets, lvf_isomorphism = isom\<rparr>"
    and "domain \<noteq> {}"
    and "\<And>i. i \<notin> I \<Longrightarrow> sets i = undefined"
    and "\<And>x. x \<notin> domain \<Longrightarrow> isom x = undefined"
    and bij: "bij_betw isom domain (dependent_functions I sets)"
    apply cases by auto

  from valid1 have factors1: "factors1 \<subseteq> I" unfolding lv1 apply cases by (auto simp: factorization)
  from compat have valid2: "valid_lvalue_basic lv2" apply cases by simp
  from valid2 have factors2: "factors2 \<subseteq> I" unfolding lv2 apply cases by (auto simp: factorization)

  from x have x: "x \<in> domain"
    unfolding lv1 lvalue_basic_domain_def factorization by simp

  have restrict: "restrict (isom x) (factors1 \<union> factors2)
    \<in> dependent_functions (factors1 \<union> factors2) sets"
    apply (rule dependent_functions_restrict[where D=I])
    using bij x bij_betwE factorization apply auto[1]
    using factors1 factors2 by simp

  have "fst (lvalue_basic_fun (lvalue_basic_compose lv1 lv2) x) = lvalue_basic_fun lv1 x"
    unfolding lv1 lv2 using factors_disj by (auto intro: restrict simp: factorization restrict_def Int_commute)
  moreover have "snd (lvalue_basic_fun (lvalue_basic_compose lv1 lv2) x) = lvalue_basic_fun lv2 x"
    unfolding lv1 lv2 using factors_disj by (auto intro: restrict simp: factorization restrict_def inf_sup_distrib2)
  ultimately show ?thesis
    by (metis prod.collapse)
qed


lemma lvalue_basic_compose_valid:
  assumes "lvalue_basic_compatible lv1 lv2"
  shows "valid_lvalue_basic (lvalue_basic_compose lv1 lv2)"
(* TODO same for lvalue *)
proof -
  from assms have same_fact: "lv_factorization lv1 = lv_factorization lv2" by cases   
  obtain factorization factors1 repr1 where
    lv1: "lv1 = \<lparr> lv_factorization=factorization, lv_factors=factors1, lv_representation=repr1 \<rparr>"
    apply atomize_elim apply (cases lv1) by simp
  with same_fact obtain factors2 repr2 where
    lv2: "lv2 = \<lparr> lv_factorization=factorization, lv_factors=factors2, lv_representation=repr2 \<rparr>"
    apply atomize_elim apply (cases lv1) apply auto
    by (metis (full_types) lvalue_basic.surjective old.unit.exhaust)

  from assms have valid1: "valid_lvalue_basic lv1" by cases
  then have valid_fact: "valid_lvalue_factorization factorization"
    apply cases unfolding lv1 by simp
  from valid1 have inj_repr1: "inj_on repr1 (dependent_functions factors1 (lvf_sets factorization))"
    apply cases unfolding lv1 by simp

  from assms have valid2: "valid_lvalue_basic lv2" by cases
  from valid2 have inj_repr2: "inj_on repr2 (dependent_functions factors2 (lvf_sets factorization))"
    apply cases unfolding lv2 by simp

  have fact_union: "factors1 \<union> factors2 \<subseteq> lvf_index_set factorization"
    by (metis Un_subset_iff assms lv1 lv2 lvalue_basic.select_convs(1) lvalue_basic.select_convs(2) lvalue_basic_compatible.cases valid_lvalue_basic.cases)
  
  have inj: "inj_on
     (restrict (\<lambda>x. (repr1 (restrict x factors1), repr2 (restrict x factors2)))
       (dependent_functions (factors1 \<union> factors2) (lvf_sets factorization)))
     (dependent_functions (factors1 \<union> factors2) (lvf_sets factorization))"
    apply (subst inj_on_restrict)
(* TODO apply rule that removes the restrict. Like inj_on (restrict f I) I = inj_on f I. *)
  proof (rule inj_onI, rule ext)
    fix x y i
    assume x: "x \<in> dependent_functions (factors1 \<union> factors2) (lvf_sets factorization)"
    then have x_factors1: "restrict x factors1 : dependent_functions factors1 (lvf_sets factorization)"
          and x_factors2: "restrict x factors2 : dependent_functions factors2 (lvf_sets factorization)"
      using dependent_functions_restrict by auto
    assume y: "y \<in> dependent_functions (factors1 \<union> factors2) (lvf_sets factorization)"
    then have y_factors1: "restrict y factors1 : dependent_functions factors1 (lvf_sets factorization)"
          and y_factors2: "restrict y factors2 : dependent_functions factors2 (lvf_sets factorization)"
      using dependent_functions_restrict by auto
    assume eq: "(repr1 (restrict x factors1), repr2 (restrict x factors2)) =
            (repr1 (restrict y factors1), repr2 (restrict y factors2))"
    then have "repr1 (restrict x factors1) = repr1 (restrict y factors1)"
      by simp
    from inj_repr1 this x_factors1 y_factors1
    have eq1: "restrict x factors1 = restrict y factors1"
      by (rule inj_onD[where f=repr1])
    from eq have "repr2 (restrict x factors2) = repr2 (restrict y factors2)"
      by simp
    from inj_repr2 this x_factors2 y_factors2
    have eq2: "restrict x factors2 = restrict y factors2"
      by (rule inj_onD[where f=repr2])

    consider (factors1) "i \<in> factors1" | (factors2) "i \<in> factors2" | (outside) "i \<notin> factors1 \<union> factors2"
      by auto
    then show "x i = y i"
    proof cases
      case factors1
      with eq1[THEN fun_cong, of i]
      show ?thesis 
        unfolding restrict_def by simp
    next
      case factors2
      with eq2[THEN fun_cong, of i]
      show ?thesis 
        unfolding restrict_def by simp
    next
      case outside
      with x have xi: "x i = undefined"
        apply cases by simp
      from y outside have yi: "y i = undefined"
        apply cases by simp
      from xi yi show ?thesis
        by simp
    qed
  qed

  have outside: "f \<notin> dependent_functions (factors1 \<union> factors2) (lvf_sets factorization) \<Longrightarrow>
         restrict (\<lambda>x. (repr1 (restrict x factors1), repr2 (restrict x factors2)))
          (dependent_functions (factors1 \<union> factors2) (lvf_sets factorization)) f =
         undefined" for f
    unfolding restrict_def by simp

  show ?thesis
    unfolding lv1 lv2 apply simp
    using valid_fact fact_union inj outside by (rule valid_lvalue_basic.intros)
qed


lemma lvalue_basic_domain_compose:
  assumes compat: "lvalue_basic_compatible lvb1 lvb2"
  shows "lvalue_basic_domain (lvalue_basic_compose lvb1 lvb2) = lvalue_basic_domain lvb1"
    and "lvalue_basic_domain (lvalue_basic_compose lvb1 lvb2) = lvalue_basic_domain lvb2"
   apply (cases lvb1, cases lvb2, hypsubst_thin, simp add: lvalue_basic_domain_def)
  apply (insert compat)
  by (cases lvb1, cases lvb2, hypsubst_thin, simp add: lvalue_basic_domain_def lvalue_basic_compatible.simps)
(* TODO same for lvalue *)

lemma lvalue_basic_range_compose:
  assumes compat: "lvalue_basic_compatible lvb1 lvb2"
  shows "lvalue_basic_range (lvalue_basic_compose lvb1 lvb2)
           = lvalue_basic_range lvb1 \<times> lvalue_basic_range lvb2"
(* TODO same for lvalue *)
proof -
  from assms have same_fact: "lv_factorization lvb1 = lv_factorization lvb2" by cases   
  obtain factorization factors1 repr1 where
    lv1: "lvb1 = \<lparr> lv_factorization=factorization, lv_factors=factors1, lv_representation=repr1 \<rparr>"
    apply atomize_elim apply (cases lvb1) by simp
  with same_fact obtain factors2 repr2 where
    lv2: "lvb2 = \<lparr> lv_factorization=factorization, lv_factors=factors2, lv_representation=repr2 \<rparr>"
    apply atomize_elim apply (cases lvb1) apply auto
    by (metis (full_types) lvalue_basic.surjective old.unit.exhaust)

  from assms have factors_disj: "factors1 \<inter> factors2 = {}" apply cases unfolding lv1 lv2 by simp

  have "(\<lambda>x. (restrict x factors1, restrict x factors2)) `
        dependent_functions (factors1 \<union> factors2) (lvf_sets factorization) =
            dependent_functions factors1 (lvf_sets factorization) \<times>
            dependent_functions factors2 (lvf_sets factorization)"
    using dependent_functions_split[OF factors_disj, where A="lvf_sets factorization"]
    by (simp add: bij_betw_def)
  also have "(map_prod repr1 repr2) ` \<dots> = lvalue_basic_range lvb1 \<times> lvalue_basic_range lvb2"
    apply (rule map_prod_surj_on)
    unfolding lvalue_basic_range_def lv1 lv2 by simp_all
  finally show ?thesis
    unfolding lvalue_basic_range_def lv1 lv2 
    unfolding map_prod_def image_comp o_def by (simp add: restrict_image)
qed

definition lvalue_basic_squash :: "('a,'b) lvalue_basic \<Rightarrow> ('a,'a) lvalue_basic * ('a\<Rightarrow>'b)" where
  "lvalue_basic_squash lv = 
    (let f::'b\<Rightarrow>'a = SOME f. inj_on f (lvalue_basic_range lv);
         lv' = lvalue_basic_map f lv;
         f' = inv_into (lvalue_basic_range lv) f
     in (lv',f'))"

lemma lvalue_basic_squash_valid:
  assumes "valid_lvalue_basic lvb"
  shows "valid_lvalue_basic (fst (lvalue_basic_squash lvb))"
  sorry

lemma lvalue_basic_squash_bij:
  assumes "valid_lvalue_basic lvb"
  shows "bij_betw (snd (lvalue_basic_squash lvb))
            (lvalue_basic_range (fst (lvalue_basic_squash lvb)))
            (lvalue_basic_range lvb)"
proof -
  define f :: "'b\<Rightarrow>'a" and lvb' and f' where "f = (SOME f. inj_on f (lvalue_basic_range lvb))"
    and "lvb' = lvalue_basic_map f lvb"
    and "f' = inv_into (lvalue_basic_range lvb) f"
  then have squash: "lvalue_basic_squash lvb = (lvb',f')"
    unfolding lvalue_basic_squash_def unfolding Let_def by simp
  have "inj_on f (lvalue_basic_range lvb)"
    unfolding f_def apply (rule someI_ex[where P="%f. inj_on f (lvalue_basic_range lvb)"])
    using lvalue_basic_range_leq_domain[OF assms]
    unfolding leq_card_def by auto
  then have "bij_betw f (lvalue_basic_range lvb) (lvalue_basic_range lvb')"
    unfolding lvb'_def
    by (simp add: inj_on_imp_bij_betw)
  then have "bij_betw f' (lvalue_basic_range lvb') (lvalue_basic_range lvb)"
    unfolding f'_def
    by (rule bij_betw_inv_into)
  then show ?thesis
    unfolding squash by simp
qed

lemma lvalue_basic_squash_map:
  assumes "valid_lvalue_basic lvb"
  shows "lvalue_basic_map (snd (lvalue_basic_squash lvb)) (fst (lvalue_basic_squash lvb)) = lvb"
proof -
  define f :: "'b\<Rightarrow>'a" and lvb' and f' where "f = (SOME f. inj_on f (lvalue_basic_range lvb))"
    and "lvb' = lvalue_basic_map f lvb"
    and "f' = inv_into (lvalue_basic_range lvb) f"
  then have squash: "lvalue_basic_squash lvb = (lvb',f')"
    unfolding lvalue_basic_squash_def unfolding Let_def by simp
  have "inj_on f (lvalue_basic_range lvb)"
    unfolding f_def apply (rule someI_ex[where P="%f. inj_on f (lvalue_basic_range lvb)"])
    using lvalue_basic_range_leq_domain[OF assms]
    unfolding leq_card_def by auto
  then have bij_f: "bij_betw f (lvalue_basic_range lvb) (lvalue_basic_range lvb')"
    unfolding lvb'_def
    by (simp add: inj_on_imp_bij_betw)

  have "f' (f x) = x" if "x \<in> lvalue_basic_range lvb" for x
    unfolding f'_def
    using bij_f that by (rule bij_betw_inv_into_left)
  then have "lvalue_basic_map (f' \<circ> f) lvb = lvb"
    apply (subst (2) lvalue_basic_map_id[OF assms, symmetric])
    apply (rule lvalue_basic_map_cong)
    by auto
  then show ?thesis
    unfolding squash lvb'_def by simp
qed

lemma lvalue_basic_squash_domain[simp]:
  "lvalue_basic_domain (fst (lvalue_basic_squash lvb)) = lvalue_basic_domain lvb"
  apply (cases lvb) unfolding lvalue_basic_squash_def
  by (simp add: Let_def lvalue_basic_domain_def)

datatype ('a,'b) lvalue = 
  LValueBasic "('a,'b) lvalue_basic"
  (* LValueChained lv lvb = lv o lvb *)
  | LValueChained "('a,'b) lvalue" "('a,'a) lvalue_basic"

fun lvalue_domain where
  "lvalue_domain (LValueBasic lvb) = lvalue_basic_domain lvb"
| "lvalue_domain (LValueChained lv lvb) = lvalue_basic_domain lvb"


fun lvalue_range where
  "lvalue_range (LValueBasic lvb) = lvalue_basic_range lvb"
| "lvalue_range (LValueChained lv lvb) = lvalue_range lv"

fun lvalue_map where
  "lvalue_map f (LValueBasic lvb) = LValueBasic (lvalue_basic_map f lvb)"
| "lvalue_map f (LValueChained lv lvb) = LValueChained (lvalue_map f lv) lvb"

inductive valid_lvalue where
  "valid_lvalue_basic lvb \<Longrightarrow> valid_lvalue (LValueBasic lvb)"
| "\<lbrakk> valid_lvalue lv; valid_lvalue_basic lvb; lvalue_domain lv = lvalue_basic_range lvb \<rbrakk>
       \<Longrightarrow> valid_lvalue (LValueChained lv lvb)"

fun lvalue_squash where
  "lvalue_squash (LValueBasic lvb) = (let (lvb',f) = lvalue_basic_squash lvb in (LValueBasic lvb', f))"
| "lvalue_squash (LValueChained lv lvb) = (let (lv',f) = lvalue_squash lv in (LValueChained lv' lvb, f))"

lemma lvalue_squash_bij:
  assumes "valid_lvalue lv"
  shows "bij_betw (snd (lvalue_squash lv)) (lvalue_range (fst (lvalue_squash lv))) (lvalue_range lv)"
proof (insert assms, induction lv)
  case (LValueBasic x)
  then show ?case
    apply cases
    apply (simp add: case_prod_beta)
    by (simp add: lvalue_basic_squash_bij)
next
  case (LValueChained lv x2)
  from LValueChained.prems have valid: "valid_lvalue lv" by cases
  show ?case
    apply (simp add: case_prod_beta)
    apply (rule LValueChained.IH)
    by (fact valid)
qed

lemma lvalue_squash_map:
  assumes "valid_lvalue lv"
  shows "lvalue_map (snd (lvalue_squash lv)) (fst (lvalue_squash lv)) = lv"
proof (insert assms, induction lv)
  case (LValueBasic lvb)
  then have valid: "valid_lvalue_basic lvb"
    by cases
  show ?case
    apply (simp add: case_prod_beta)
    apply (rule lvalue_basic_squash_map)
    by (fact valid)
next
  case (LValueChained lv x2)
  from LValueChained.prems have valid: "valid_lvalue lv" by cases
  show ?case
    apply (simp add: case_prod_beta)
    apply (rule LValueChained.IH)
    by (fact valid)
qed

fun factorization_domain_map :: "('a\<Rightarrow>'b) \<Rightarrow> 'b lvalue_factorization \<Rightarrow> 'a lvalue_factorization" where
  "factorization_domain_map f \<lparr> lvf_domain=domain, lvf_index_set=I, lvf_sets=sets, lvf_isomorphism=isom \<rparr>
    = (* \<lparr> lvf_domain=domain', lvf_index_set=I', lvf_sets=sets', lvf_isomorphism=isom' \<rparr> *) undefined"

(* lvalue_basic_domain_map f lv = lv o f *)
fun lvalue_basic_domain_map :: "('a\<Rightarrow>'b) \<Rightarrow> ('a set) \<Rightarrow> ('b,'c) lvalue_basic \<Rightarrow> ('a,'c) lvalue_basic" where
"lvalue_basic_domain_map f D \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr>
  = (* \<lparr> lv_factorization=factorization_domain_map f D factorization, lv_factors=factors, lv_representation=repr \<rparr> *)undefined" (* TODO *)

lemma lvalue_basic_domain_map_domain[simp]:
  shows "lvalue_basic_domain (lvalue_basic_domain_map f D lvb) = D"
  sorry

fun lvalue_chain_basic :: "('b,'c) lvalue_basic \<Rightarrow> ('a,'b) lvalue \<Rightarrow> ('a,'c) lvalue" where
  "lvalue_chain_basic lvb1 (LValueBasic lvb2) = (let (lvb2',f) = lvalue_basic_squash lvb2 in
    LValueChained (LValueBasic (lvalue_basic_domain_map f (lvalue_basic_range lvb2') lvb1)) lvb2')"
| "lvalue_chain_basic lvb1 (LValueChained lv2 lvb2) = LValueChained (lvalue_chain_basic lvb1 lv2) lvb2"

fun lvalue_chain where
  "lvalue_chain (LValueBasic lvb1) lv2 = lvalue_chain_basic lvb1 lv2"
| "lvalue_chain (LValueChained lv1 lvb1) lv2 = lvalue_chain lv1 (lvalue_chain_basic lvb1 lv2)"

lemma lvalue_chain_basic_domain[simp]: "lvalue_domain (lvalue_chain_basic lvb lv) = lvalue_domain lv"
  by (induction lv; simp add: case_prod_beta)

lemma lvalue_chain_domain[simp]: "lvalue_domain (lvalue_chain lv1 lv2) = lvalue_domain lv2"
  by (induction lv1 arbitrary: lv2; simp)

fun lvalue_fun :: "('a, 'b) lvalue \<Rightarrow> 'a \<Rightarrow> 'b" where
  "lvalue_fun (LValueBasic lvb) x = lvalue_basic_fun lvb x"
| "lvalue_fun (LValueChained lv lvb) x = lvalue_fun lv (lvalue_basic_fun lvb x)"

fun lvalue_cofun :: "('a, 'b) lvalue \<Rightarrow> 'a \<Rightarrow> 'a"
  and "lvalue_corange" :: "('a, 'b) lvalue \<Rightarrow> 'a set"
where
  "lvalue_cofun (LValueBasic lvb) x = lvalue_basic_cofun lvb x"
| "lvalue_cofun (LValueChained lv lvb) x = 
    (let y = lvalue_basic_fun lvb x;
         yco = lvalue_basic_cofun lvb x;
         zco = lvalue_cofun lv y;
         f = SOME f. inj_on f (lvalue_basic_corange lvb \<times> lvalue_corange lv)
     in f (yco,zco))"
| "lvalue_corange (LValueBasic lvb) = lvalue_basic_corange lvb"
| "lvalue_corange (LValueChained lv lvb) = 
    (let f = SOME f. inj_on f (lvalue_basic_corange lvb \<times> lvalue_corange lv)
    in f ` (lvalue_basic_corange lvb \<times> lvalue_corange lv))"

section \<open>Composition of lvalues\<close>

inductive lvalue_compatible :: "('a,'b) lvalue \<Rightarrow> ('a,'c) lvalue \<Rightarrow> bool" where
  lvalue_compatible_same: "\<lbrakk> lvalue_compatible lv1 lv2; valid_lvalue (LValueChained lv1 lvb);
 valid_lvalue (LValueChained lv2 lvb) \<rbrakk> \<Longrightarrow> lvalue_compatible (LValueChained lv1 lvb) (LValueChained lv2 lvb)" 
| lvalue_compatible_cc: "\<lbrakk> lvalue_basic_compatible lvb1 lvb2; valid_lvalue (LValueChained lv1 lvb1); valid_lvalue (LValueChained lv2 lvb2) \<rbrakk>
 \<Longrightarrow> lvalue_compatible (LValueChained lv1 lvb1) (LValueChained lv2 lvb2)"
| lvalue_compatible_bb: "\<lbrakk> lvalue_basic_compatible lvb1 lvb2; valid_lvalue (LValueBasic lvb1); valid_lvalue (LValueBasic lvb2) \<rbrakk> \<Longrightarrow> lvalue_compatible (LValueBasic lvb1) (LValueBasic lvb2)"
| lvalue_compatible_cb: "\<lbrakk> lvalue_basic_compatible lvb1 lvb2; valid_lvalue (LValueChained lv1 lvb1); valid_lvalue (LValueBasic lvb2) \<rbrakk> \<Longrightarrow> lvalue_compatible (LValueChained lv1 lvb1) (LValueBasic lvb2)"
| lvalue_compatible_bc: "\<lbrakk> lvalue_basic_compatible lvb1 lvb2; valid_lvalue (LValueBasic lvb1); valid_lvalue (LValueChained lv2 lvb2)\<rbrakk> \<Longrightarrow> lvalue_compatible (LValueBasic lvb1) (LValueChained lv2 lvb2)"

lemma lvalue_compatible_valid:
  assumes "lvalue_compatible lv1 lv2"
  shows "valid_lvalue lv1" and "valid_lvalue lv2"
  using assms apply cases apply auto 
  using assms apply cases by auto

term lvalue_chain_basic

definition lvalue_product :: "('a,'b) lvalue \<Rightarrow> ('c,'d) lvalue \<Rightarrow> ('a*'c,'b*'d) lvalue" where
  "lvalue_product = undefined" (* TODO *)

definition "make_lvalue_factorization D I sets isom =
    \<lparr> lvf_domain=D, lvf_index_set=I,
    lvf_sets=restrict sets I,
    lvf_isomorphism=restrict (\<lambda>a. restrict (isom a) I) D \<rparr>"

lemma valid_make_lvalue_factorization:
  assumes nonempty: "D \<noteq> {}"
  assumes surj: "\<And>y. y \<in> dependent_functions I sets \<Longrightarrow> \<exists>x\<in>D. \<forall>i\<in>I. y i = isom x i" 
  assumes sets: "\<And>x i. x \<in> D \<Longrightarrow> i:I \<Longrightarrow> isom x i \<in> sets i"
  assumes inj: "\<And>x y. x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> (\<And>i. i\<in>I \<Longrightarrow> isom x i = isom y i) \<Longrightarrow> x = y"
  assumes card: "leq_card I D"
  shows "valid_lvalue_factorization (make_lvalue_factorization D I sets isom)"
  unfolding make_lvalue_factorization_def
proof (rule valid_lvalue_factorization.intros)
  have dep: "dependent_functions I (restrict sets I) = dependent_functions I sets"
    apply auto
     apply (erule dependent_functions'.cases; rule dependent_functions'.intros; simp)
    by (erule dependent_functions'.cases; rule dependent_functions'.intros; simp)
  have surj': "\<exists>x\<in>D. y = restrict (isom x) I" if "y \<in> dependent_functions I sets" for y
    apply (rule bex_reg[OF _ surj[OF that]])
    using that apply (rule dependent_functions'.cases)
    apply auto apply (rule ext, rename_tac i) apply (case_tac "i:I")
    by auto
  have sets': "x \<in> D \<Longrightarrow> restrict (isom x) I \<in> dependent_functions I sets" for x
    apply (rule dependent_functions'.intros)
     apply auto
    by (rule sets)
  have inj': "x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> restrict (isom x) I = restrict (isom y) I \<Longrightarrow> x = y" for x y
    apply (rule inj, auto simp: restrict_def[abs_def])
    by meson
  show "bij_betw (restrict (\<lambda>a. restrict (isom a) I) D) D (dependent_functions I (restrict sets I))"
    apply (rule bij_betwI')
    by (auto simp: inj' sets' surj' dep)
qed (auto simp: assms)

definition "factorization_id D = make_lvalue_factorization D {undefined}
                                   (\<lambda>i. Abs_factor ` D) (\<lambda>a i. Abs_factor a)"

lemma factorization_id_index_set[simp]: "lvf_index_set (factorization_id D) = {undefined}"
  unfolding factorization_id_def make_lvalue_factorization_def by simp

lemma factorization_id_sets[simp]: "lvf_sets (factorization_id D) = restrict (\<lambda>i. Abs_factor ` D) {undefined}"
  unfolding factorization_id_def make_lvalue_factorization_def by simp


definition "make_lvalue_basic factorization factors repr
  = \<lparr> lv_factorization=factorization, lv_factors=factors,
      lv_representation=restrict repr (dependent_functions factors (lvf_sets factorization)) \<rparr>"

lemma valid_make_lvalue_basic:
  assumes factorization: "valid_lvalue_factorization factorization"
  assumes factors: "factors \<subseteq> lvf_index_set factorization"
  assumes repr: "inj_on repr (dependent_functions factors (lvf_sets factorization))"
  shows "valid_lvalue_basic (make_lvalue_basic factorization factors repr)"
proof -
  show ?thesis
  unfolding make_lvalue_basic_def
  using factorization factors apply (rule valid_lvalue_basic.intros)
  unfolding inj_on_restrict using repr apply assumption
  unfolding restrict_def by simp
qed

definition lvalue_basic_id :: "'a set \<Rightarrow> ('a,'a) lvalue_basic" where
  "lvalue_basic_id D = make_lvalue_basic (factorization_id D) {undefined} (\<lambda>f. Rep_factor (f undefined))"

lemma valid_factorization_id: 
  assumes "D\<noteq>{}"
  shows "valid_lvalue_factorization (factorization_id D)"
  unfolding factorization_id_def
proof (rule valid_make_lvalue_factorization)
  show "y \<in> dependent_functions {undefined} (\<lambda>i. Abs_factor ` D) \<Longrightarrow> 
          \<exists>x\<in>D. \<forall>i\<in>{undefined}. y i = Abs_factor x" for y :: "'a LValue.index \<Rightarrow> 'a factor"
    apply (rule bexI[of _ "Rep_factor (y undefined)"])
     apply (auto simp: Rep_factor_inverse)
    apply (erule dependent_functions'.cases)
    apply auto
    by (metis Abs_factor_inverse UNIV_I image_iff)
  show "x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> (\<And>i. i \<in> {undefined} \<Longrightarrow> Abs_factor x = Abs_factor y) \<Longrightarrow> x = y" for x y
    apply (subst (asm) Abs_factor_inject) by auto
  show "leq_card {undefined} D"
    unfolding leq_card_def
    apply (rule exI[of _ "\<lambda>_. SOME d. d\<in>D"])
    using assms by (simp add: some_in_eq)
qed (auto simp: assms)

lemma valid_lvalue_basic_id: 
  assumes "D\<noteq>{}"
  shows "valid_lvalue_basic (lvalue_basic_id D)"
proof -
  have inj: "inj_on (\<lambda>f. Rep_factor (f undefined)) (dependent_functions {undefined} (lvf_sets (factorization_id D)))"
    apply (rule inj_onI)
    apply (subst (asm) Rep_factor_inject)
    apply (simp, rule ext, rename_tac i, case_tac "i=undefined")
    unfolding dependent_functions'.simps by auto 

  show ?thesis
    unfolding lvalue_basic_id_def
    apply (rule valid_make_lvalue_basic)
    using assms apply (rule valid_factorization_id)
     apply simp
    using inj by simp
qed

definition "lvalue_id D = LValueBasic (lvalue_basic_id D)"

lemma valid_lvalue_id: 
  assumes "D \<noteq> {}"
  shows "valid_lvalue (lvalue_id D)"
  unfolding lvalue_id_def
  apply (rule valid_lvalue.intros)
  using assms by (rule valid_lvalue_basic_id)

function lvalue_compose :: "('a,'b) lvalue \<Rightarrow> ('a,'c) lvalue \<Rightarrow> ('a,'b*'c) lvalue" where
  lvalue_compose_same: "lvalue_compatible lv1 lv2 \<Longrightarrow> 
      lvalue_compose (LValueChained lv1 lvb) (LValueChained lv2 lvb) = 
      LValueChained (lvalue_compose lv1 lv2) lvb"
| lvalue_compose_cc: "\<not> lvalue_compatible lv1 lv2 \<or> lvb1\<noteq>lvb2 \<Longrightarrow>
      lvalue_compose (LValueChained lv1 lvb1) (LValueChained lv2 lvb2) =
      lvalue_chain (lvalue_product lv1 lv2) (LValueBasic (lvalue_basic_compose lvb1 lvb2))"
| lvalue_compose_bb: "lvalue_compose (LValueBasic lvb1) (LValueBasic lvb2) = LValueBasic (lvalue_basic_compose lvb1 lvb2)"
| lvalue_compose_cb: "lvalue_compose (LValueChained lv1 lvb1) (LValueBasic lvb2) =
      lvalue_chain (lvalue_product lv1 (lvalue_id (lvalue_basic_range lvb2)))
                   (LValueBasic (lvalue_basic_compose lvb1 lvb2))"
| lvalue_compose_bc: "lvalue_compose (LValueBasic lvb1) (LValueChained lv2 lvb2) =
      lvalue_chain (lvalue_product (lvalue_id (lvalue_basic_range lvb1)) lv2)
                   (LValueBasic (lvalue_basic_compose lvb1 lvb2))"
                 apply auto 
  by (atomize_elim, case_tac a; case_tac b, auto)
termination by lexicographic_order

lemma lvalue_compose_domain:
  assumes "lvalue_compatible lv1 lv2"
  shows "lvalue_domain (lvalue_compose lv1 lv2) = lvalue_domain lv1"
proof (insert assms, induction lv1 lv2 rule: lvalue_compose.induct)
  case (1 lv1 lv2 lvb)
  then show ?case
    by (subst lvalue_compose.simps, auto)
next
  case (2 lv1 lv2 lvb1 lvb2)
  then have c: "lvalue_basic_compatible lvb1 lvb2"
    using lvalue_compatible.cases by auto
  show ?case 
    apply (subst lvalue_compose.simps, fact 2)
    apply simp
    using c by (rule lvalue_basic_domain_compose)
next
  case (3 lvb1 lvb2)
  then have c: "lvalue_basic_compatible lvb1 lvb2"
    using lvalue_compatible.cases by auto
  show ?case
    apply (subst lvalue_compose.simps, simp)
    using c by (rule lvalue_basic_domain_compose)
next
  case (4 lv1 lvb1 lvb2)
  then have c: "lvalue_basic_compatible lvb1 lvb2"
    using lvalue_compatible.cases by auto
  show ?case
    apply (subst lvalue_compose.simps, simp)
    using c by (rule lvalue_basic_domain_compose)
next
  case (5 lvb1 lv2 lvb2)
  then have c: "lvalue_basic_compatible lvb1 lvb2"
    using lvalue_compatible.cases by auto
  show ?case
    apply (subst lvalue_compose.simps, simp)
    using c by (rule lvalue_basic_domain_compose)
qed

lemma lvalue_basic_domain_map_valid: 
  assumes "valid_lvalue_basic lvb"
  assumes "bij_betw f D (lvalue_basic_domain lvb)"
  shows "valid_lvalue_basic (lvalue_basic_domain_map f D lvb)"
  sorry

lemma lvalue_chain_basic_valid: 
  assumes valid_lvb: "valid_lvalue_basic lvb"
  assumes "valid_lvalue lv"
  assumes "lvalue_basic_domain lvb = lvalue_range lv"
  shows "valid_lvalue (lvalue_chain_basic lvb lv)"
proof (insert assms, induction lv arbitrary: lvb)
  case (LValueBasic lvb2)
  then have valid_lvb2: "valid_lvalue_basic lvb2"
    using valid_lvalue.simps by auto
  show ?case 
    apply (simp add: case_prod_beta)
    apply (rule valid_lvalue.intros)+
       apply (rule lvalue_basic_domain_map_valid)
    using LValueBasic apply simp
    using LValueBasic.prems(2) LValueBasic.prems(3) lvalue_basic_squash_bij valid_lvalue.cases apply auto[1]
    using valid_lvb2 apply (rule lvalue_basic_squash_valid)  
    by simp
  next
  case (LValueChained lv x2)
  then show ?case sorry
qed


lemma lvalue_chain_valid: 
  shows "valid_lvalue (lvalue_chain lv1 lv2)"
  apply (induction lv1) apply simp  
  find_theorems valid_lvalue lvalue_chain_basic
lemma lvalue_compose_valid: 
  shows "lvalue_compatible lv1 lv2 \<Longrightarrow> valid_lvalue (lvalue_compose lv1 lv2)"
proof (induction lv1 lv2 rule: lvalue_compose.induct)
  case (1 lv1 lv2 lvb)
  from "1.prems" have valid_lv1lvb: "valid_lvalue (LValueChained lv1 lvb)"
    by (rule lvalue_compatible_valid)
  then have valid_lvb: "valid_lvalue_basic lvb"
    by cases
  from valid_lv1lvb have dom1: "lvalue_domain lv1 = lvalue_basic_range lvb"
    by cases
  then have domain: "lvalue_domain (lvalue_compose lv1 lv2) = lvalue_basic_range lvb"
    by (subst lvalue_compose_domain[OF "1.hyps"])
  show ?case
    apply (subst lvalue_compose_same[OF "1.hyps"])
    using "1.IH"[OF "1.hyps"] valid_lvb domain by (rule valid_lvalue.intros)
next
  case (2 lv1 lv2 lvb1 lvb2)
  show ?case
    apply (subst lvalue_compose_cc[OF "2.hyps"])
    by x
next
  case (3 lvb1 lvb2)
  show ?case
    apply (subst lvalue_compose_bb)
    apply (rule valid_lvalue.intros)
    apply (rule lvalue_basic_compose_valid)
    using 3 by cases
next
  case (4 lv1 lvb1 lvb2)
  show ?case
    apply (subst lvalue_compose_cb)
    by x 
next
  case (5 lvb1 lv2 lvb2)
  show ?case 
    apply (subst lvalue_compose_bc)
    by x
qed

lemma lvalue_compatible_sym:
  assumes "lvalue_compatible lv1 lv2"
  shows "lvalue_compatible lv2 lv1"
  using assms proof induction
  case (lvalue_compatible_same lv1 lv2 lvb)
  then show ?case
    by (rule_tac lvalue_compatible.lvalue_compatible_same, simp)
next
  case (lvalue_compatible_cc lvb1 lvb2 lv1 lv2)
  then show ?case
    apply (rule_tac lvalue_compatible.intros)
    by (rule lvalue_basic_compatible_sym)
next
case (lvalue_compatible_bb lvb1 lvb2)
  then show ?case
    apply (rule_tac lvalue_compatible.intros)
    by (rule lvalue_basic_compatible_sym)
next
  case (lvalue_compatible_cb lvb1 lvb2 lv1)
  then show ?case
    apply (rule_tac lvalue_compatible.intros)
    by (rule lvalue_basic_compatible_sym)
next
case (lvalue_compatible_bc lvb1 lvb2 lv2)
  then show ?case 
    apply (rule_tac lvalue_compatible.intros)
    by (rule lvalue_basic_compatible_sym)
qed

definition "left_composition_map f x = (case x of (x,r) \<Rightarrow> case f r of (y,s) \<Rightarrow> ((x,y),s))"
definition "left_composition_map_back f' xy = (case xy of ((x,y),s) \<Rightarrow> (x, f' (y,s)))"

inductive left_composition_f :: "('a,'b) lvalue \<Rightarrow> ('a,'c) lvalue \<Rightarrow> _" where
  "bij_betw f (lvalue_corange x) (lvalue_range y \<times> lvalue_corange (lvalue_compose x y))
    \<Longrightarrow> (\<And>z. left_composition_map f (lvalue_fun x z, lvalue_cofun x z) 
                = (lvalue_fun (lvalue_compose x y) z, lvalue_cofun (lvalue_compose x y) z))
    \<Longrightarrow> (f' = inv_into (lvalue_corange x) f)
    \<Longrightarrow> left_composition_f x y f f'"

lemma left_composition_map_back:
  assumes left_composition_f: "left_composition_f x y f f'"
  defines "xy == lvalue_compose x y"
  defines "Rx == (\<lambda>i. (lvalue_fun x i, lvalue_cofun x i))"
  defines "Rxy == (\<lambda>i. (lvalue_fun xy i, lvalue_cofun xy i))"
  assumes z: "z \<in> lvalue_domain x"
  shows "Rx z = left_composition_map_back f' (Rxy z)"
  sorry

lemma left_composition_f_inv_inj: 
  fixes x :: "('a,'b) lvalue" and y :: "('a,'c) lvalue"
  assumes left_composition_f: "left_composition_f x y f f'"
  defines "xy == lvalue_compose x y"
  defines "Rx == (\<lambda>i. (lvalue_fun x i, lvalue_cofun x i))"
  defines "Rxy == (\<lambda>i. (lvalue_fun xy i, lvalue_cofun xy i))"
  assumes z1_dom: "z1 \<in> lvalue_domain x"
  assumes z2_dom: "z2 \<in> lvalue_domain x"
  assumes Rxy_z1: "Rxy z1 = ((x1, y1), r1)"
  assumes Rxy_z2: "Rxy z2 = ((x2, y2), r2)"
  shows "f' (y1, r1) = f' (y2, r2) \<longleftrightarrow> (y1,r1) = (y2,r2)"
  sorry

lemma composed_lvalue_relationship_left:
  fixes x :: "('a,'b) lvalue" and y :: "('a,'c) lvalue"
  assumes compat: "lvalue_compatible x y"
  shows "\<exists>f f'. left_composition_f x y f f'"
  sorry

section Matrices

typedef 'a matrix = "UNIV::('a\<Rightarrow>'a\<Rightarrow>complex) set" by simp
setup_lifting type_definition_matrix

lift_definition tensor :: "'a::finite matrix \<Rightarrow> 'b::finite matrix \<Rightarrow> ('a*'b) matrix" is
  "%A B. \<lambda>(r1,r2) (c1,c2). A r1 c1 * B r2 c2" .

instantiation matrix :: (type) ab_group_add begin
lift_definition plus_matrix :: "'a matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" is "%A B i j. A i j + B i j".
lift_definition minus_matrix :: "'a matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" is "%A B i j. A i j - B i j".
lift_definition uminus_matrix :: "'a matrix \<Rightarrow> 'a matrix" is "%A i j. - A i j".
lift_definition zero_matrix :: "'a matrix" is "\<lambda>i j. 0".
instance sorry
end

instantiation matrix :: (type) "{times,one}" begin
lift_definition times_matrix :: "'a matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" is "%A B i k. (\<Sum>j\<in>UNIV. A i j * B j k)".
lift_definition one_matrix :: "'a matrix" is "\<lambda>i j. if i=j then 1 else 0".
instance apply intro_classes.
end

instantiation matrix :: (finite) ring_1 begin
instance proof intro_classes
  fix a b c :: "'a matrix"
  show "(a * b) * c = a * (b * c)"
    apply transfer
    apply (subst sum_distrib_right)
    apply (subst sum_distrib_left)
    apply (subst sum.swap)
    apply (subst mult.assoc)
    by simp
  show "1 * a = a"
    apply (transfer, rule ext, rule ext, rename_tac i k)
    apply (subst sum.mono_neutral_right)
    by auto
  show "a * 1 = a"
    apply (transfer, rule ext, rule ext, rename_tac i k)
    apply (subst sum.mono_neutral_right)
    by auto
  show "(a + b) * c = a * c + b * c"
    apply transfer
    unfolding ring_distribs sum.distrib by simp
  show "a * (b + c) = a * b + a * c"
    apply transfer
    unfolding ring_distribs sum.distrib by simp
  show "(0::'a matrix) \<noteq> 1"
    apply transfer by (meson zero_neq_one) 
qed
end

axiomatization
  fst_lvalue :: "('a*'b, 'a) lvalue" and
  snd_lvalue :: "('a*'b, 'b) lvalue" where
  valid_fst_lvalue: "valid_lvalue fst_lvalue" and
  valid_snd_lvalue: "valid_lvalue snd_lvalue" and
  compatible_fst_snd: "lvalue_compatible fst_lvalue snd_lvalue"

lemma compatible_snd_fst: "lvalue_compatible snd_lvalue fst_lvalue"
  using compatible_fst_snd by (rule lvalue_compatible_sym)

abbreviation "delta x y == (if x=y then 1 else 0)"

lift_definition matrix_on :: "'b::finite matrix \<Rightarrow> ('a,'b) lvalue \<Rightarrow> 'a matrix" is
  "\<lambda>B lv (r::'a) (c::'a). B (lvalue_fun lv r) (lvalue_fun lv c)
  * delta (lvalue_cofun lv r) (lvalue_cofun lv c)" .

lemma matrix_on_lift_left:
  assumes compat: "lvalue_compatible x y"
  assumes domain[simp]: "lvalue_domain x = UNIV"
  defines "xy == lvalue_compose x y"
  shows "matrix_on A x = matrix_on (tensor A 1) xy"
proof (transfer fixing: x y xy, rule ext, rule ext)
  fix A :: "'b \<Rightarrow> 'b \<Rightarrow> complex" and r c
  define Rx where "Rx = (\<lambda>i. (lvalue_fun x i, lvalue_cofun x i))"
  define Rxy where "Rxy = (\<lambda>i. (lvalue_fun xy i, lvalue_cofun xy i))"
  from composed_lvalue_relationship_left[OF compat]
  obtain f f' where f: "left_composition_f x y f f'"
    by auto
  have valid_xy: "valid_lvalue xy"
    unfolding xy_def using compat by (rule lvalue_compose_valid)
  note f'_inj = left_composition_f_inv_inj[OF f, folded xy_def Rxy_def, simp]
  have map1: "lvalue_fun x z = fst (left_composition_map_back f' (Rxy z))" if "z \<in> lvalue_domain x" for z
    unfolding Rx_def Rxy_def xy_def
    apply (subst left_composition_map_back[OF f that, symmetric])
    by simp
  have map2: "lvalue_cofun x z = snd (left_composition_map_back f' (Rxy z))" if "z \<in> lvalue_domain x" for z
    unfolding Rx_def Rxy_def xy_def
    apply (subst left_composition_map_back[OF f that, symmetric])
    by simp
  define xr xc xyr xyc xyr' xyc' where "xr = lvalue_fun x r" and "xc = lvalue_fun x c"
                      and  "xyr = lvalue_fun xy r" and "xyc = lvalue_fun xy c"
                      and  "xyr' = lvalue_cofun xy r" and "xyc' = lvalue_cofun xy c"
  note defs = this
  show "A xr xc * delta (lvalue_cofun x r) (lvalue_cofun x c) =
       (case lvalue_fun xy r of (r1, r2) \<Rightarrow> \<lambda>(c1, c2). A r1 c1 * delta r2 c2) (lvalue_fun xy c) *
       delta (lvalue_cofun xy r) (lvalue_cofun xy c)"
    unfolding defs
    apply (subst map1 map2, simp)+
    unfolding Rxy_def
    unfolding defs[symmetric]
    unfolding left_composition_map_back_def
    apply (auto simp: case_prod_beta)
      apply (metis (no_types, lifting) Pair_inject f'_inj domain iso_tuple_UNIV_I prod.collapse xyc'_def xyc_def xyr'_def xyr_def)
    apply (metis (no_types, hide_lams) UNIV_I domain f'_inj prod.exhaust_sel prod.inject xyc'_def xyc_def xyr'_def xyr_def)
    by (metis UNIV_I domain f'_inj prod.exhaust_sel snd_conv xyc'_def xyc_def xyr'_def xyr_def)
qed

lemma matrix_on_lift_right:
  assumes (* "valid_lvaluex x" and "valid_lvaluex y" and *) compat: "compatible_lvaluex x y"
  assumes domain[simp]: "lvaluex_domain y = UNIV"
  defines "xy == compose_lvaluex x y"
  shows "matrix_on A y = matrix_on (tensor 1 A) xy"
proof (transfer fixing: x y xy, rule ext, rule ext)
  fix A :: "'c \<Rightarrow> 'c \<Rightarrow> complex" and r c
  define Ry where "Ry = lvaluex_representation y"
  define Rxy where "Rxy = lvaluex_representation xy"
  from composed_lvalue_relationship_right[OF compat]
  obtain f f' where f: "right_composition_f x y f f'"
    by auto
  have valid_xy: "valid_lvaluex xy"
    unfolding xy_def using compat by (rule valid_compose_lvaluex)
  note right_composition_f_inv_inj[OF f, folded xy_def Rxy_def, simp]
  have map: "Ry z = right_composition_map_back f' (Rxy z)" if "z \<in> lvaluex_domain y" for z
    unfolding Ry_def Rxy_def xy_def
    using f that by (rule right_composition_map_back)
  show "A (fst (Ry r)) (fst (Ry c)) * delta (snd (Ry r)) (snd (Ry c)) =
       (case fst (Rxy r) of (r1, r2) \<Rightarrow> \<lambda>(c1, c2). delta r1 c1 * A r2 c2)
        (fst (Rxy c)) * delta (snd (Rxy r)) (snd (Rxy c))"
    apply (subst map, simp)+
    apply (cases "Rxy r", cases "Rxy c") 
    unfolding right_composition_map_back_def
    by auto
qed

lemma tensor_distrib: "(tensor A B) * (tensor C D) = tensor (A * C) (B * D)"
proof (transfer, rule ext, rule ext)
  fix A C :: "'a\<Rightarrow>'a\<Rightarrow>complex" and B D :: "'b\<Rightarrow>'b\<Rightarrow>complex" and i k :: "'a*'b"
  obtain i1 i2 k1 k2 where i: "i=(i1,i2)" and k: "k=(k1,k2)" by force
  have "(\<Sum>j\<in>UNIV.
          (case i of (r1, r2) \<Rightarrow> \<lambda>(c1, c2). A r1 c1 * B r2 c2) j *
          (case j of (r1, r2) \<Rightarrow> \<lambda>(c1, c2). C r1 c1 * D r2 c2) k)
        =
          (\<Sum>(j1,j2)\<in>UNIV. (A i1 j1 * B i2 j2) * (C j1 k1 * D j2 k2))" (is "?lhs = _")
    unfolding i k by (auto simp: case_prod_beta)
  also have "\<dots> = (\<Sum>j1\<in>UNIV. \<Sum>j2\<in>UNIV. (A i1 j1 * C j1 k1) * (B i2 j2 * D j2 k2))"
    unfolding UNIV_Times_UNIV[symmetric] sum.cartesian_product[symmetric]
    by (meson semiring_normalization_rules(13) sum.cong)
  also have "\<dots> = (\<Sum>j1\<in>UNIV. A i1 j1 * C j1 k1) * (\<Sum>j2\<in>UNIV. B i2 j2 * D j2 k2)"
    by (simp add: sum_product)
  also have "... = (case i of (r1, r2) \<Rightarrow> \<lambda>(c1, c2). (\<Sum>j\<in>UNIV. A r1 j * C j c1) * (\<Sum>j\<in>UNIV. B r2 j * D j c2)) k"  (is "_ = ?rhs")
    unfolding i k by simp
  finally
  show "?lhs = ?rhs" by assumption
qed

lemma matrix_on_times: 
  fixes x :: "('a::finite, 'b::finite) lvalue"
  assumes valid_x: "valid_lvaluex x"
  assumes domain[simp]: "lvaluex_domain x = UNIV"
  assumes range[simp]: "lvaluex_range x = UNIV"
  shows "matrix_on A x * matrix_on B x = matrix_on (A*B) x"
proof (transfer fixing: x, rule ext, rule ext)
  fix A B :: "'b \<Rightarrow> 'b \<Rightarrow> complex" and i k
  define Rx rg corg where "Rx = lvaluex_representation x"
    and "rg = lvaluex_range x" and "corg = lvaluex_representation_range x"
  obtain i1 i2 where i: "Rx i = (i1, i2)" by force
  obtain k1 k2 where k: "Rx k = (k1, k2)" by force
  have Rx_bij: "bij_betw Rx UNIV (UNIV \<times> corg)"
    unfolding Rx_def domain[symmetric] range[symmetric] corg_def
    using valid_x by (rule bij_lvaluex_representation)
  have "(\<Sum>j\<in>UNIV \<times> corg. A i1 (fst j) * delta k2 (snd j) * (B (fst j) k1 * delta (snd j) k2)) =
        (\<Sum>j1\<in>UNIV. \<Sum>j2\<in>corg. A i1 j1 * delta k2 j2 * (B j1 k1 * delta j2 k2))"
    apply (subst sum.cartesian_product) by (auto simp: case_prod_beta)
  also have "\<dots> = (\<Sum>j1\<in>UNIV. \<Sum>j2\<in>corg. (A i1 j1 * B j1 k1) * (delta k2 j2 * delta j2 k2))"
    by (meson semiring_normalization_rules(13) sum.cong)
  also have "\<dots> = (\<Sum>j1\<in>UNIV. A i1 j1 * B j1 k1) * (\<Sum>j2\<in>corg. delta k2 j2 * delta j2 k2)"
    by (simp add: sum_product)
  also have "(\<Sum>j2\<in>corg. delta k2 j2 * delta j2 k2 :: complex) = (\<Sum>j2\<in>{k2}. delta k2 j2 * delta j2 k2)"
    apply (rule sum.mono_neutral_cong_right)
       apply simp
    using Rx_bij k
      apply (metis SigmaD2 bij_betw_def rangeI singletonD subset_eq)
    by auto
  also have "(\<Sum>j1\<in>UNIV. A i1 j1 * B j1 k1) * (\<Sum>j2\<in>{k2}. delta k2 j2 * delta j2 k2) = (\<Sum>j1\<in>UNIV. A i1 j1 * B j1 k1)"
    by simp
  also note eq = calculation
  show "(\<Sum>j\<in>UNIV.
          A (fst (Rx i)) (fst (Rx j)) * delta (snd (Rx i)) (snd (Rx j)) *
          (B (fst (Rx j)) (fst (Rx k)) * delta (snd (Rx j)) (snd (Rx k)))) =
       (\<Sum>j\<in>UNIV. A (fst (Rx i)) j * B j (fst (Rx k))) * delta (snd (Rx i)) (snd (Rx k))"
    apply (subst sum.reindex_bij_betw[OF Rx_bij]) unfolding i k using eq apply auto
    by (smt mult_not_zero sum.neutral)
qed
  

lemma
  fixes x :: "('a::finite, 'b::finite) lvaluex" and y :: "('a::finite, 'c::finite) lvaluex" 
  assumes (* "valid_lvaluex x" and "valid_lvaluex y" and *) "compatible_lvaluex x y"
  assumes domain: "lvaluex_domain x = UNIV"
  assumes range_x: "lvaluex_range x = UNIV"
  assumes range_y: "lvaluex_range y = UNIV"
  defines "xy == compose_lvaluex x y"
  shows "matrix_on A x * matrix_on B y = matrix_on (tensor A B) xy"
  apply (subst matrix_on_lift_left[where A=A and y=y])
  using assms(1-2) apply simp_all[2]
  apply (subst matrix_on_lift_right[where A=B and x=x])
  using assms(1) apply simp_all[3]
  using assms(1,2) domain_compose_lvaluex apply fastforce
  apply (subst matrix_on_times)
   apply (simp add: assms(1) assms(2) assms(3) valid_compose_lvaluex)
  apply (simp add: domain domain_compose_lvaluex(1))
   apply (subst range_compose_lvaluex)
    apply simp
  apply (simp add: range_x range_y)
  unfolding xy_def[symmetric]
  by (simp add: tensor_distrib)


(* ================================= *)


lemma compatible_compose_lvalue_raw0':
  (* assumes "valid_lvalue_raw0 lv1" *)
  (* assumes "valid_lvalue_raw0 lv2" *)
  (* assumes "valid_lvalue_raw0 lv3" *)
  assumes compat: "compatible_lvalue_raw0 lv1 lv2"
  assumes "compatible_lvalue_raw0 lv1 lv3"
  assumes "compatible_lvalue_raw0 lv2 lv3"
  shows "compatible_lvalue_raw0 (lvaluex_lvalue (compose_lvalue_raw0' lv1 lv2)) lv3"


function lvalue_raw_representation0 :: "'a lvalue_raw0 \<Rightarrow> 'a \<Rightarrow> 'a\<times>'a" where
  "lvalue_raw_representation0 (LValueUnit0 D r) x = (r,x)"
| "lvalue_raw_representation0 (LValueAll0 D repr) x = (repr x,undefined)"
| "lvalue_raw_representation0 (LValue0 F lvs rg repr) x =
    (let factors = isomorphism F x;
         factors_repr = \<lambda>i::'a index. 
              if i\<in>index_set F then lvalue_raw_representation0 (lvs i) (factors i)
                               else (undefined,undefined);
         factors_result = fst o factors_repr;
         leftover = snd o factors_repr;
         leftover_f = SOME f. inj_on f (dependent_functions (index_set F) (\<lambda>i. lvalue_raw_representation_range0 (lvs i)))
    in
    (repr factors_result, leftover_f leftover))"

definition lvaluex_representation :: "('a,'b) lvaluex \<Rightarrow> 'a \<Rightarrow> 'b\<times>'a" where
  "lvaluex_representation lv x = apfst (lvaluex_fun lv) (lvalue_raw_representation0 (lvaluex_lvalue lv) x)"

definition lvaluex_representation_range :: "('a,'b) lvaluex \<Rightarrow> 'a set" where
  "lvaluex_representation_range lv = lvalue_raw_representation_range0 (lvaluex_lvalue lv)"

definition "lvalue_update0 f lv x = inv (lvalue_raw_representation0 lv)
                                        (apfst f (lvalue_raw_representation0 lv x))"
fun lvaluex_update where
  "lvaluex_update f (LValueX lv g) = lvalue_update0 (inv g o f o g) lv"

definition "right_composition_map f y = (case y of (y,r) \<Rightarrow> case f r of (x,s) \<Rightarrow> ((x,y),s))"
definition "right_composition_map_back f' xy = (case xy of ((x,y),s) \<Rightarrow> (y, f' (x,s)))"


inductive right_composition_f :: "('a,'b) lvaluex \<Rightarrow> ('a,'c) lvaluex \<Rightarrow> _" where
" (* valid_lvaluex x \<Longrightarrow> valid_lvaluex y \<Longrightarrow> *) compatible_lvaluex x y
  \<Longrightarrow> bij_betw f (lvaluex_representation_range y) (lvaluex_range x \<times> lvaluex_representation_range (compose_lvaluex x y))
  \<Longrightarrow> (\<And>z. right_composition_map f (lvaluex_representation y z) = (lvaluex_representation (compose_lvaluex x y) z))
  \<Longrightarrow> (f' = inv_into (lvaluex_representation_range y) f)
  \<Longrightarrow> right_composition_f x y f f'"



lemma right_composition_f_inv_inj:
  fixes x :: "('a,'b) lvaluex" and y :: "('a,'c) lvaluex"
  assumes right_composition_f: "right_composition_f x y f f'"
  defines "xy == compose_lvaluex x y"
  defines "Ry == lvaluex_representation y"
  defines "Rxy == lvaluex_representation xy"
  assumes z1_dom: "z1 \<in> lvaluex_domain y"
  assumes z2_dom: "z2 \<in> lvaluex_domain y"
  assumes Rxy_z1: "Rxy z1 = ((x1, y1), r1)"
  assumes Rxy_z2: "Rxy z2 = ((x2, y2), r2)"
  shows "f' (x1, r1) = f' (x2, r2) \<longleftrightarrow> (x1,r1) = (x2,r2)"


  
lemma right_composition_map_back:
  assumes right_composition_f: "right_composition_f x y f f'"
  defines "xy == compose_lvaluex x y"
  defines "Ry == lvaluex_representation y"
  defines "Rxy == lvaluex_representation xy"
  assumes z: "z \<in> lvaluex_domain y"
  shows "Ry z = right_composition_map_back f' (Rxy z)"

lemma left_composition_fI:
  fixes f
  assumes compat: "compatible_lvaluex x y"
  defines "f' == inv_into (lvaluex_representation_range x) f"
  assumes bij: "bij_betw f (lvaluex_representation_range x)
     (lvaluex_range y \<times> lvaluex_representation_range (compose_lvaluex x y))"
  assumes map: "\<And>z. left_composition_map f (lvaluex_representation x z) 
                          = lvaluex_representation (compose_lvaluex x y) z"
  shows "left_composition_f x y f f'"

lemma composed_lvalue_relationship_left0:
  fixes x y :: "('a,_) lvalue"
  assumes compat: "lvalue_compatible x y"
  shows "\<exists>f. 
    bij_betw f (lvalue_raw_representation_range0 x) 
               (lvalue_range0 y \<times> lvaluex_representation_range (compose_lvalue_raw0' x y))
  \<and> (\<forall>z. left_composition_map f (lvalue_raw_representation0 x z) 
              = (lvaluex_representation (compose_lvalue_raw0' x y) z))"


lemma composed_lvalue_relationship_right:
  fixes x :: "('a,'b) lvaluex" and y :: "('a,'c) lvaluex"
  (* assumes "valid_lvaluex x" *)
  (* assumes "valid_lvaluex y" *)
  assumes "compatible_lvaluex x y"
  defines "xy == compose_lvaluex x y"
  obtains f f' where "right_composition_f x y f f'"
  sorry


end
