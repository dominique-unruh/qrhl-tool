theory LValue
  imports Main "HOL-Library.Rewrite" (* "HOL-Cardinals.Cardinals" *)
    (* "Jordan_Normal_Form.Matrix_Impl" *) Complex_Main
    (* "HOL-Library.Indicator_Function" *)
"HOL-Library.FuncSet"
begin

section \<open>Misc missing\<close>


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

lemma extensionalI:
  assumes "\<And>x. x\<notin>D \<Longrightarrow> f x = undefined"
  shows "f : extensional D"
  unfolding extensional_def using assms by simp

(* TODO remove *)
typedef 'a index = "UNIV::'a set" ..
typedef 'a factor = "UNIV::'a set" ..
typedef 'a target = "UNIV::'a set" ..

(* lemma "inj_on f *)

(*
inductive_set dependent_functions' :: "'b \<Rightarrow> 'a set \<Rightarrow> ('a\<Rightarrow>'b set) \<Rightarrow> ('a\<Rightarrow>'b) set"
  for undef :: 'b and domain :: "'a set" and range :: "'a \<Rightarrow> 'b set" where
  "\<lbrakk> \<And>a. a\<notin>domain \<Longrightarrow> f a = undef;
     \<And>a. a\<in>domain \<Longrightarrow> f a \<in> range a \<rbrakk>
   \<Longrightarrow> f \<in> dependent_functions' undef domain range"
*)

section \<open>leq_card\<close>

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


(* lemma bij_dependent_functions_split:
  assumes "bij_betw (\<lambda>x i. (f1 i (x i), f2 i (x i))) (dependent_functions' u I A) (dependent_functions' (v1,v2) I (\<lambda>i. B i \<times> C i))"
  shows "bij_betw (\<lambda>x. (\<lambda>i. f1 i (x i), \<lambda>i. f2 i (x i))) (dependent_functions' u I A) (dependent_functions' v1 I B \<times> dependent_functions' v2 I C)" 
   *)


section \<open>Dependent Functions -- REMOVE!\<close>

(* TODO remove *)
abbreviation "dependent_functions == PiE" 

(* (* TODO remove *)
lemma "restrict f S x = (if x\<in>S then f x else undefined)"
  unfolding restrict_def by simp
 *)

(* TODO remove *)
lemma restrict_simp[simp]:
  "x : D \<Longrightarrow> restrict f D x = f x"
  unfolding restrict_apply by simp

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

(* TODO remove *)
lemma dependent_functions_restrict:
  assumes "f \<in> dependent_functions D R"
  assumes D': "D' \<subseteq> D"
  shows "restrict f D' \<in> dependent_functions D' R"
  using D' assms(1) by auto

lemma dependent_functions_restrict_twice[simp]:
  "restrict (restrict f D) D'
      = restrict f (D\<inter>D')"
  unfolding restrict_def by auto

lemma dependent_functions_restrict_surj:
  assumes D: "D \<subseteq> D'"
  assumes A: "\<And>i. i\<in>D' \<Longrightarrow> A i \<noteq> {}"
  shows "(\<lambda>f. restrict f D) ` dependent_functions D' A = dependent_functions D A"
proof auto
  fix f x assume f: "f \<in> dependent_functions D' A" and "x:D"
  then show "f x \<in> A x"
    using f apply cases apply simp
    using D by blast
next
  fix f assume f: "f \<in> dependent_functions D A"
  define f' where "f' i = (if i\<in>D then f i else if i\<in>D' then (SOME x. x:A i) else undefined)" for i
  have "f = restrict f' D"
    unfolding restrict_def f'_def
    apply (rule ext) using f apply cases by auto
  moreover have "f' \<in> dependent_functions D' A"
    unfolding f'_def
    find_theorems intro PiE
    apply (rule PiE_I) 
    using D apply auto
    using f apply auto[1]
    by (simp add: A some_in_eq)
  ultimately show "f \<in> (\<lambda>f. restrict f D) ` dependent_functions D' A"
    by (rule image_eqI[where x=f'])
qed

    

lemma dependent_functions_nonempty:
  assumes "\<And>i. i\<in>I \<Longrightarrow> A i \<noteq> {}"
  shows "dependent_functions I A \<noteq> {}"
  by (simp add: PiE_eq_empty_iff assms)

lemma bij_betw_dependent_functions: 
  assumes bij_f: "\<And>i. i \<in> I \<Longrightarrow> bij_betw (f i) (A i) (B i)"
  assumes f_undef: "\<And>i x. i \<notin> I \<Longrightarrow> f i x = undefined"
  shows "bij_betw (\<lambda>g i. f i (g i)) (dependent_functions I A) (dependent_functions I B)"
proof (rule bij_betwI')
  fix x y
  assume x: "x \<in> dependent_functions I A"
  show "(\<lambda>i. f i (x i)) \<in> dependent_functions I B"
    using bij_betwE bij_f f_undef x by fastforce
  assume y: "y \<in> dependent_functions I A"
  from bij_f have inj_f: "inj_on (f i) (A i)" if "i:I" for i
    by (simp add: bij_betw_def that)
  have "x = y" if "(\<lambda>i. f i (x i)) = (\<lambda>i. f i (y i))"
    apply (rule ext)
    using that inj_f
    by (metis (full_types) PiE_E inj_on_eq_iff x y)
  then show "((\<lambda>i. f i (x i)) = (\<lambda>i. f i (y i))) = (x = y)"
    by auto
next
  fix y
  assume y: "y \<in> dependent_functions I B"
  have "\<exists>x'. (y i = f i x' \<and> (i\<in>I \<longrightarrow> x' \<in> A i) \<and> (i\<notin>I \<longrightarrow> x' = undefined))" for i
    apply (cases "i\<in>I")
    apply (metis PiE_iff bij_betw_def bij_f image_iff y)
    using f_undef y by auto
  then obtain x where x: "(y i = f i (x i) \<and> (i\<in>I \<longrightarrow> x i \<in> A i) \<and> (i\<notin>I \<longrightarrow> x i = undefined))" for i
    apply atomize_elim apply (rule choice) by simp
  then have "x\<in>dependent_functions I A"
    by blast
  moreover
  from x have "y = (\<lambda>i. f i (x i))"
    by auto
  ultimately show "\<exists>x\<in>dependent_functions I A. y = (\<lambda>i. f i (x i))"
    by auto
qed

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
        apply blast
        using \<open>i \<notin> I\<close> ydep by auto
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
      by (smt Collect_mem_eq Collect_mem_eq Collect_mono_iff DiffD2 Diff_empty Diff_iff Diff_subset PiE_I PiE_iff \<open>f \<equiv> \<lambda>x i. if i \<in> J - I then SOME a. a \<in> A i else x i\<close> assms(1) assms(2) empty_Collect_eq extensional_arb mem_Collect_eq mem_Collect_eq minus_set_def some_eq_ex some_in_eq subset_iff xdep y)
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
    unfolding F_def
      
    using f that by fastforce
  then have "F ` dependent_functions I A \<subseteq> dependent_functions I B"
    by auto
  moreover
  have "F g1 = F g2 \<Longrightarrow> g1 = g2"
    if "g1 \<in> dependent_functions I A" and "g2 \<in> dependent_functions I A" for g1 g2
    sorry
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
  shows "bij_betw (dependent_functions_split I) (dependent_functions I AB)
     (dependent_functions I A \<times> dependent_functions I B)"
proof (rule bij_betwI')
  fix x y :: "'a \<Rightarrow> 'b \<times> 'c"
  assume x: "x \<in> dependent_functions I AB"
  then have x_undef: "i \<notin> I \<Longrightarrow> x i = undefined" for i
    by blast
  assume y: "y \<in> dependent_functions I AB"
  then have y_undef: "i \<notin> I \<Longrightarrow> y i = undefined" for i
    by blast
  show "(dependent_functions_split I x = dependent_functions_split I y) = (x = y)"
    unfolding o_def dependent_functions_split_def 
    apply auto
    by (metis prod_eq_iff x_undef y_undef ext)
  have "(\<lambda>i. if i \<in> I then fst (x i) else undefined) \<in> dependent_functions I A"
    using x apply cases
    apply simp
    using PiE_mem assms by fastforce
  moreover
  have "(\<lambda>i. if i \<in> I then snd (x i) else undefined) \<in> dependent_functions I B"
    using x apply cases     
     apply blast
    using PiE_mem assms by fastforce
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

    by (metis PiE_restrict g1 restrict_simp_outside)
  obtain f2 where f2: "g2 i = (if i \<in> I then f2 i else undefined)" for i

    using g2 by force
  define f where "f i = (if i:I then (f1 i, f2 i) else undefined)" for i
  have fAB: "f \<in> dependent_functions I AB"
    by (smt PiE_I PiE_mem SigmaI \<open>f \<equiv> \<lambda>i. if i \<in> I then (f1 i, f2 i) else undefined\<close> assms f1 f2 g1 g2)
  show "\<exists>f\<in>dependent_functions I AB. g = dependent_functions_split I f"
    unfolding g dependent_functions_split_def apply (rule bexI[of _ f])
    using f1 f2 apply (fastforce simp: f_def)
    using fAB by assumption
qed

lemma dependent_functions_split:
  assumes disjoint: "disjnt I J"
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
      then show ?thesis
        using x y by fastforce
    qed
  qed
next
  fix a b assume a: "a \<in> dependent_functions I A" and b: "b \<in> dependent_functions J A"
  define x where "x i = (if i\<in>I then a i else if i\<in>J then b i else undefined)" for i
  have "x\<in>dependent_functions (I \<union> J) A"
    using a b 
    using PiE_mem x_def by auto
  moreover have "a = restrict x I"
    using a sorry
  moreover have "b = restrict x J"
    apply (rule ext, rename_tac i)
    unfolding restrict_def x_def
    using b apply cases
    using disjoint unfolding disjnt_def by auto
  ultimately show "\<exists>x\<in>dependent_functions (I \<union> J) A.
              a = restrict x I \<and> b = restrict x J"
    by auto
qed

section \<open>Factorization\<close>

record ('a,'b,'c) lvalue_factorization =
  lvf_domain :: "'a set"
  lvf_index_set :: "'b set"
  lvf_sets :: "'b \<Rightarrow> 'c set"
  lvf_isomorphism :: "'a \<Rightarrow> ('b \<Rightarrow> 'c)"

locale lvalue_factorization =
  fixes F :: "('a,'b,'c) lvalue_factorization"
begin
abbreviation "domain == lvf_domain F"
abbreviation "I == lvf_index_set F"
abbreviation "sets == lvf_sets F"
abbreviation "isom == lvf_isomorphism F"
end

(* 'a=domain, 'b=index set, 'c=factor set *)
locale valid_lvalue_factorization = lvalue_factorization +
(*   fixes domain :: "'a set"
    and I :: "'b set"
    and sets :: "'b \<Rightarrow> 'c set"
    and isom :: "'a \<Rightarrow> ('b \<Rightarrow> 'c)" *)
  assumes domain_nonempty[simp]: "domain \<noteq> {}"
     and sets_ext: "sets \<in> extensional I"
     and isom_ext: "isom \<in> extensional domain"
     and I_leq_domain: "leq_card I domain"
     and bij_betw_isom: "bij_betw isom domain (dependent_functions I sets)"

(* inductive valid_lvalue_factorization :: "('a,'b,'c) lvalue_factorization \<Rightarrow> bool" where
  "\<lbrakk> domain \<noteq> {};
     sets \<in> extensional I;
     isom \<in> extensional domain;
     leq_card I domain;
     bij_betw isom domain (dependent_functions I sets)
   \<rbrakk> \<Longrightarrow> valid_lvalue_factorization \<lparr> lvf_domain=domain, lvf_index_set=I, lvf_sets=sets, lvf_isomorphism=isom \<rparr>" *)

lemma (in valid_lvalue_factorization) sets_nonempty:
  (* assumes valid: "valid_lvalue_factorization F" *)
  assumes i: "i \<in> I"
  shows "sets i \<noteq> {}"
proof -
  (* case (1 domain sets I isom) *)
  (* thm 1 *)
  from bij_betw_isom
  have "Pi\<^sub>E I sets \<noteq> {}"
    using bij_betw_empty2 by fastforce
  then obtain f where "f \<in> dependent_functions I sets" by auto
  then have "sets i \<noteq> {}"
    apply cases using i by auto
  then show ?thesis
    by auto
qed


lemma (in valid_lvalue_factorization) I_sets_leq_domain[simp]: "leq_card (dependent_functions I sets) domain"
  using bij_betw_isom leq_cardI_bij' by blast

locale squash_factorization = valid_lvalue_factorization begin
definition "I_map = (SOME f::'b\<Rightarrow>'a. inj_on f I)"
definition "I' = I_map ` I"
definition "inv_I_map = inv_into I I_map"
definition "sets_map (i::'b) = (SOME f::'c\<Rightarrow>'a. inj_on f (sets i))"
definition "inv_sets_map i = inv_into (sets i) (sets_map i)"
definition "sets' = (\<lambda>i\<in>I'. sets_map (inv_I_map i) ` sets (inv_I_map i))"
definition "isom' = (\<lambda>a\<in>domain. \<lambda>i\<in>I'. sets_map (inv_I_map i) (isom a (inv_I_map i)))"
definition "F' = \<lparr>lvf_domain = domain, lvf_index_set = I', 
                       lvf_sets = sets',
                       lvf_isomorphism = isom'\<rparr>"
end

lemma (in squash_factorization) I_map_I'[simp]: "i\<in>I \<Longrightarrow> I_map i \<in> I'" for i
    unfolding I'_def by simp

lemma (in squash_factorization) inj_I_map: "inj_on I_map I"
    unfolding I_map_def apply (rule someI_ex[where P="\<lambda>f. inj_on f I"])
    by (meson I_leq_domain leq_card_def)

lemma (in squash_factorization) inv_I_map[simp]: "inv_I_map (I_map i) = i" if "i\<in>I" for i
    unfolding inv_I_map_def using that
    using inj_I_map by auto

lemma (in squash_factorization) inj_sets_map: "inj_on (sets_map i) (sets i)" if "i\<in>I" for i
proof -
  have "leq_card (sets i) (dependent_functions I sets)"
  proof -
    obtain S where S: "S \<in> dependent_functions I sets"
      apply atomize_elim
      using bij_betwE bij_betw_isom domain_nonempty by blast
    show ?thesis
      apply (rule leq_cardI[where f="\<lambda>x. S(i:=x)"])
       apply (simp add: fun_upd_eqD inj_onI)
      using S by (auto simp: that)
  qed
  also have "leq_card (dependent_functions I sets) (UNIV::'a set)"
    by (meson I_sets_leq_domain leq_card_def top_greatest)
  finally have "\<exists>f::'c\<Rightarrow>'a. inj_on f (sets i)"
    unfolding leq_card_def by auto
  then show ?thesis
    unfolding sets_map_def by (rule someI_ex[where P="\<lambda>f. inj_on f _"]) 
qed

definition (in lvalue_factorization) "inv_isom = inv_into domain isom"


lemma (in squash_factorization) inv_sets_map[simp]: "inv_sets_map i (sets_map i x) = x" if "i\<in>I" and "x\<in>sets i" for i x
  by (simp add: that inj_sets_map inv_sets_map_def)

lemma (in valid_lvalue_factorization) isom_sets[simp]: "isom a i \<in> sets i" if "i\<in>I" and "a\<in>domain" for i a
  by (meson that PiE_iff bij_betwE bij_betw_isom)

lemma (in valid_lvalue_factorization) isom_I_sets[simp]: "isom a \<in> Pi\<^sub>E I sets" if "a\<in>domain" for a
  using bij_betwE bij_betw_isom that by blast

lemma (in valid_lvalue_factorization) [simp]: "isom a \<in> extensional I" if "a\<in>domain" for a
  using that
  using PiE_iff isom_I_sets by blast

lemma (in valid_lvalue_factorization) restrict_isom[simp]: "restrict (isom a) I = isom a" if "a\<in>domain" for a
  by (meson PiE_restrict isom_I_sets that)

lemma (in valid_lvalue_factorization) inv_isom_isom[simp]: "inv_isom (isom a) = a" if "a\<in>domain" for a
  using bij_betw_inv_into_left bij_betw_isom inv_isom_def that by fastforce

lemma (in valid_lvalue_factorization) isom_inv_isom[simp]: "isom (inv_isom f) = f" if "f \<in> Pi\<^sub>E I sets" for f
  using bij_betw_inv_into_right bij_betw_isom inv_isom_def that by fastforce

lemma (in squash_factorization) inv_sets_map_sets: "inv_sets_map i f \<in> sets i" if "i \<in> I" and "f\<in>sets' (I_map i)" for i f
  unfolding inv_sets_map_def 
  apply (rule inv_into_into)
  using that unfolding sets'_def
  by simp

sublocale squash_factorization \<subseteq> squash: lvalue_factorization F'.

sublocale squash_factorization \<subseteq> squash: valid_lvalue_factorization F'
proof (unfold_locales)
  show "squash.domain \<noteq> {}"
    by (simp add: F'_def)
  show "squash.sets \<in> extensional squash.I"
    by (simp add: F'_def sets'_def)
  show "squash.isom \<in> extensional squash.domain"
    by (simp add: F'_def isom'_def)
  show "leq_card squash.I squash.domain"
    by (metis F'_def I'_def I_leq_domain I_map_def bij_betw_def leq_cardI_bij' leq_card_def leq_card_trans lvalue_factorization.select_convs(1) lvalue_factorization.select_convs(2) someI_ex)
  note restrict_cong[cong]  
  show "bij_betw squash.isom squash.domain (dependent_functions squash.I squash.sets)"
  proof -
    have "(isom' x = isom' y) = (x = y)" if [simp]:"x\<in>domain" and [simp]:"y\<in>domain" for x y
    proof (rule)
      assume "isom' x = isom' y"
      then have "(\<lambda>i\<in>I'. sets_map (inv_I_map i) (isom x (inv_I_map i))) =
                  (\<lambda>i\<in>I'. sets_map (inv_I_map i) (isom y (inv_I_map i)))"
        using that unfolding isom'_def by simp
      then have "(sets_map (inv_I_map i) (isom x (inv_I_map i))) =
                  (sets_map (inv_I_map i) (isom y (inv_I_map i)))" if "i\<in>I'" for i
        using that
        by (metis (mono_tags, lifting) restrict_simp)
      then have "(sets_map i (isom x i)) =
                  (sets_map i (isom y i))" if "i\<in>I" for i
        using that I_map_I' by fastforce
      then have "((isom x i)) =
                  ((isom y i))" if "i\<in>I" for i
        apply (rule inj_onD[OF inj_sets_map, OF that])
        using that by auto
      then have "isom x = isom y"
        apply (rule_tac extensionalityI[where A=I])
        by auto
      then show "x=y"
        using inv_isom_isom that by fastforce
    qed simp
    moreover have "isom' x \<in> dependent_functions I' sets'" if [simp]:"x\<in>domain" for x
    proof (rule PiE_I)
      fix i assume i[simp]:"i \<in> I'"
      show "isom' x i \<in> sets' i"
        unfolding isom'_def sets'_def
        apply simp using isom_sets i that
        by (metis I'_def imageI inv_I_map_def inv_into_into)
    next
      fix i assume [simp]:"i \<notin> I'"
      show "isom' x i = undefined"
        unfolding isom'_def by simp
    qed
    moreover have "\<exists>x\<in>domain. y = isom' x" if y:"y \<in> dependent_functions I' sets'" for y
    proof -
      have "(\<lambda>i\<in>I. inv_sets_map i (y (I_map i))) \<in> dependent_functions I sets"
        using inv_sets_map_sets y by fastforce
      with bij_betw_isom obtain x where isom_x:"isom x = (\<lambda>i\<in>I. inv_sets_map i (y (I_map i)))" and [simp]:"x:domain"
        apply atomize_elim unfolding bij_betw_def
        by (metis (mono_tags, lifting) imageE)
      then have "inv_sets_map i (y (I_map i)) = (isom x i)" if "i:I" for i
        using that by simp
      then have "y (I_map i) = (sets_map i (isom x i))" if "i:I" for i
        by (smt I_map_I' PiE_iff y f_inv_into_f inv_I_map inv_sets_map_def restrict_simp sets'_def that)
      then have "y i = (sets_map (inv_I_map i) (isom x (inv_I_map i)))" if "i:I'" for i
        by (metis I'_def f_inv_into_f inv_I_map_def inv_into_into that)
      then have "y = (\<lambda>i\<in>I'. sets_map (inv_I_map i) (isom x (inv_I_map i)))"
        using that by fastforce
      then show ?thesis
        unfolding isom'_def
        by auto
    qed
    ultimately have "bij_betw isom' domain (dependent_functions I' sets')"
      by (rule bij_betwI', simp_all)
    then show ?thesis
      by (simp add: F'_def)
  qed
qed


lemma (in squash_factorization) factorization_squash_index_sets_map: "\<And>i. i\<in>I \<Longrightarrow> bij_betw (sets_map i) (sets i) (sets' (I_map i))"
  by (simp add: bij_betw_def inj_sets_map sets'_def)

(* lemma 
  fixes F :: "('a,'b,'c) lvalue_factorization"
  assumes valid: "valid_lvalue_factorization F"
  assumes squash: "factorization_squash F = (F',I_map',sets_map')"
  (* shows factorization_squash_valid: "valid_lvalue_factorization F'" *)
    and factorization_squash_sets: "lvf_sets F' = (\<lambda>i\<in>lvf_index_set F'. sets_map' (inv_into (lvf_index_set F) I_map' i) ` lvf_sets F (inv_into (lvf_index_set F) I_map' i))"
    and factorization_squash_index_set: "lvf_index_set F' = I_map' ` lvf_index_set F"
    and factorization_squash_index_sets_map: "\<And>i. i\<in>lvf_index_set F \<Longrightarrow> bij_betw (sets_map' i) (lvf_sets F i) (lvf_sets F' (I_map' i))"
  using assms apply cases defer using assms apply cases defer using assms apply cases defer using assms
proof cases
 *)(*   case (1 domain sets I isom)
  define I_map I' inv_I_map sets_map inv_sets_map sets' isom' factorization' inv_isom where
    "I_map = (SOME f::'b\<Rightarrow>'a. inj_on f I)" and
    "I' = I_map ` I" and 
    "inv_I_map = inv_into I I_map" and 
    "sets_map = (\<lambda>i::'b. SOME f::'c\<Rightarrow>'a. inj_on f (sets i))" and
    "inv_sets_map = (\<lambda>i. inv_into (sets i) (sets_map i))" and 
    "sets' = (\<lambda>i\<in>I'. sets_map (inv_I_map i) ` sets (inv_I_map i))" and
    "isom' = (\<lambda>a\<in>domain. \<lambda>i\<in>I'. sets_map (inv_I_map i) (isom a (inv_I_map i)))" and
    "factorization' = \<lparr>lvf_domain = domain, lvf_index_set = I', 
                       lvf_sets = sets', 
                       lvf_isomorphism = isom'\<rparr>" and
    "inv_isom = inv_into domain isom"
  note defs = this
  have squashF:"factorization_squash F = (factorization',I_map,sets_map)"
    by (simp add: 1 defs[symmetric] Let_def)
  then have F': "F' = factorization'"
    using squash by auto
 *)




(*   have [simp]: "(\<lambda>i\<in>I. inv_sets_map i f) \<in> dependent_functions I sets" if "f \<in> sets' (I_map x)" for f
    (* unfolding inv_sets_map_def *)
    apply (rule PiE_I)
     apply (auto simp:)
    apply (rule inv_sets_map_sets)
    (* apply (rule dependent_functions_restrict[where D=I]) *)
    find_theorems intro PiE *)

(*   show "valid_lvalue_factorization F'"
    unfolding F' factorization'_def
  proof (rule valid_lvalue_factorization.intros)

  show "lvf_sets F' = (\<lambda>i\<in>lvf_index_set F'. sets_map' (inv_into (lvf_index_set F) I_map' i) ` lvf_sets F (inv_into (lvf_index_set F) I_map' i))"
    using "1"(1) factorization'_def inv_I_map_def sets'_def squash squashF by auto

  show "lvf_index_set F' = I_map' ` lvf_index_set F"
    using "1"(1) squashF factorization'_def I'_def squash by fastforce

  show "\<And>i. i \<in> lvf_index_set F \<Longrightarrow> bij_betw (sets_map' i) (lvf_sets F i) (lvf_sets F' (I_map' i))"
    by (metis (mono_tags, lifting) "1"(1) I_map_I' Pair_inject bij_betw_def factorization'_def inj_sets_map inv_I_map lvalue_factorization.select_convs(2) lvalue_factorization.select_convs(3) restrict_simp sets'_def squash squashF)
qed *)


lemma (in squash_factorization) sets_map_sets[simp]: "sets_map i ` sets i = sets' (I_map i)" if "i\<in>I" for i
  by (simp add: bij_betw_imp_surj_on factorization_squash_index_sets_map that)

definition (in lvalue_factorization) factorization_domain_map :: "('d\<Rightarrow>'a) \<Rightarrow> 'd set \<Rightarrow> ('d,'b,'c) lvalue_factorization" where
  "factorization_domain_map f D = \<lparr> lvf_domain=D, lvf_index_set=I, lvf_sets=sets, lvf_isomorphism=isom o f \<rparr>"

definition "factorization_id D = \<lparr> lvf_domain=D, lvf_index_set={undefined}, lvf_sets=\<lambda>i\<in>{undefined}. D, lvf_isomorphism=\<lambda>x\<in>D. (\<lambda>i\<in>{undefined}. x) \<rparr>"

lemma leq_card_singleton[simp]: assumes "D\<noteq>{}" shows "leq_card {x::'a} D"
proof -
  obtain y where y: "y\<in>D" using assms by auto
  define f where "f x = y" for x :: "'a"
  have "inj_on f {x}"
    by auto
  moreover have "f ` {x} \<subseteq> D"
    unfolding f_def using y by auto
  ultimately show ?thesis
    by (rule leq_cardI)
qed

lemma valid_factorization_id:
  assumes "D\<noteq>{}"
  shows  "valid_lvalue_factorization (factorization_id D)"
proof (unfold_locales, unfold factorization_id_def, auto simp: assms)
  show "bij_betw (\<lambda>x. \<lambda>i\<in>{undefined}. x) D (Pi\<^sub>E {undefined} (\<lambda>i\<in>{undefined}. D))"
  proof (rule bij_betwI', auto)
    fix x y 
    show "x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> (\<lambda>i\<in>{undefined}. x) = (\<lambda>i\<in>{undefined}. y) \<Longrightarrow> x = y"
      by (metis restrict_simp singletonI)
  next
    fix f :: "'c\<Rightarrow>'a"
    assume f: "f \<in> dependent_functions {undefined} (\<lambda>i\<in>{undefined}. D)"
    show "\<exists>x\<in>D. f = (\<lambda>i\<in>{undefined}. x)"
      apply (rule bexI[of _ "f undefined"])
      using f apply fastforce
      using PiE_mem f by fastforce
  qed
qed

section \<open>lvalue_basic\<close>

record ('a,'b,'c,'d) lvalue_basic =
  lv_factorization :: "('a,'b,'c) lvalue_factorization"
  lv_factors :: "'b set"
  lv_representation :: "('b \<Rightarrow> 'c) \<Rightarrow> 'd"

locale lvalue_basic = (* lvalue_factorization "lv_factorization lvb" + *)
  fixes lvb :: "('a,'b,'c,'d) lvalue_basic" begin
definition "F = lv_factorization lvb" 
sublocale lvalue_factorization F.
abbreviation "factors == lv_factors lvb"
abbreviation "repr == lv_representation lvb"
lemma lvb_def: "lvb = \<lparr> lv_factorization=F, lv_factors=factors, lv_representation=repr \<rparr>"
  unfolding F_def by auto
end

locale valid_lvalue_basic = lvalue_basic + valid_lvalue_factorization F +
(*   fixes factors :: "'b set"
    and repr :: "('b \<Rightarrow> 'c) \<Rightarrow> 'd" *)
  assumes factors_I: "factors \<subseteq> I"
    and inj_repr: "inj_on repr (dependent_functions factors sets)"
    and repr_ext: "repr \<in> extensional (dependent_functions factors sets)"

(* inductive valid_lvalue_basic :: "('a,'b,'c,'d) lvalue_basic \<Rightarrow> bool" where
  "\<lbrakk> valid_lvalue_factorization factorization;
     factors \<subseteq> lvf_index_set factorization;
     inj_on repr (dependent_functions factors (lvf_sets factorization));
     \<And>x. x \<notin> (dependent_functions factors (lvf_sets factorization)) \<Longrightarrow> repr x = undefined
  \<rbrakk> \<Longrightarrow> valid_lvalue_basic \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr>" *)

(* definition "lvalue_basic_domain lv = lvf_domain (lv_factorization lv)" *)
definition (in lvalue_basic) "lvrange = repr ` (dependent_functions factors sets)"

lemma (in valid_lvalue_basic) lvalue_basic_range_leq_domain: "leq_card lvrange domain"
proof -
  note leq_card_trans[rotated,trans]
  have "leq_card (dependent_functions I sets) domain"
    by simp
  also have "leq_card (dependent_functions factors sets) (dependent_functions I sets)"
    apply (rule dependent_functions_mono_domain)
    by (auto simp: sets_nonempty factors_I)
  also have "leq_card (repr ` dependent_functions factors sets) (dependent_functions factors sets)"
    using inj_on_imp_bij_betw inj_repr leq_cardI_bij' by blast
  also have "repr ` dependent_functions factors sets = lvrange"
    by (simp add: lvrange_def)
  finally show ?thesis by assumption
qed

locale lvalue_basic_compatible =
  a: valid_lvalue_basic lv1 + b: valid_lvalue_basic lv2 for lv1::"('a,'b,'c,'d) lvalue_basic" and  lv2::"('a,'b,'c,'e) lvalue_basic" +
assumes same_F: "a.F = b.F"
  and disj_factors: "disjnt a.factors b.factors"

lemma (in lvalue_basic_compatible) same_sets: "a.sets = b.sets"
  unfolding same_F by simp

(* TODO remove *)
lemmas lvalue_locale_defs = lvalue_basic.F_def 

(* inductive lvalue_basic_compatible :: "('a,'b,'c,'d) lvalue_basic \<Rightarrow> ('a,'b,'c,'e) lvalue_basic \<Rightarrow> bool" where
  "\<lbrakk> valid_lvalue_basic lv1; valid_lvalue_basic lv2;
     lv_factorization lv1 = lv_factorization lv2;
     lv_factors lv1 \<inter> lv_factors lv2 = {}
  \<rbrakk> \<Longrightarrow> lvalue_basic_compatible lv1 lv2" *)

lemma (in lvalue_basic_compatible) lvalue_basic_compatible_sym:
  (* assumes "lvalue_basic_compatible lvb1 lvb2" *)
  shows "lvalue_basic_compatible lv2 lv1"
  apply intro_locales
  apply unfold_locales
  apply (simp add: same_F)
  by (simp add: disjnt_sym disj_factors)

(* locale lvbmap = valid_lvalue_basic +
  fixes f :: "'d\<Rightarrow>'e"
  assumes "inj_on f lvrange" *)

definition (in lvalue_basic) "lvbmap f = \<lparr> lv_factorization=F, lv_factors=factors, 
         lv_representation=restrict (f o repr) (dependent_functions factors sets) \<rparr>"

(* sublocale lvbmap \<subseteq> mapped: valid_lvalue_basic "mapped"
  apply intro_locales
  apply (metis lvalue_basic.select_convs(1) lvalue_locale_defs valid_lvalue_factorization_axioms mapped_def)
  apply unfold_locales
  apply (metis factors_I lvalue_basic.select_convs(1) lvalue_basic.select_convs(2) lvalue_locale_defs mapped_def)
   apply (simp add: lvbmap_def lvalue_locale_defs , unfold lvalue_locale_defs[symmetric])
  defer
  apply (simp add: lvalue_locale_defs)
  sorry
 *)

(* definition (in lvalue_basic) "lvbmap f = \<lparr> lv_factorization=F, lv_factors=factors, lv_representation=restrict (f o repr) (dependent_functions factors sets) \<rparr>" *)

(* fun lvalue_basic_map :: "('d\<Rightarrow>'e) \<Rightarrow> ('a,'b,'c,'d) lvalue_basic \<Rightarrow> ('a,'b,'c,'e) lvalue_basic" where
  "lvalue_basic_map f \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr>
    =  \<lparr> lv_factorization=factorization, lv_factors=factors, 
         lv_representation=restrict (f o repr) (dependent_functions factors (lvf_sets factorization)) \<rparr>" *)


(* locale lvalue_basic_map_o = f: lvbmap + g: lvbmap f.mapped g + gf: lvbmap _ "g o f" for g *)

(* lemma (in lvalue_basic_map_o) lvalue_basic_map_o: "g.mapped = gf.mapped"
  unfolding g.mapped_def gf.mapped_def
  unfolding f.mapped_def lvalue_basic.F_def apply (simp add: o_def)
  by auto *)

lemma (in lvalue_basic) lvalue_basic_map_o[simp]:
  "lvalue_basic.lvbmap (lvbmap f) g = lvbmap (g o f)"
  unfolding lvbmap_def lvalue_basic.lvbmap_def
  apply (simp add: o_def lvalue_basic.F_def)
  by auto

lemma (in lvalue_basic) lvalue_basic_map_cong:
  assumes "\<And>x. x\<in>lvrange \<Longrightarrow> f x = g x"
  shows "lvbmap f = lvbmap g"
  using assms unfolding lvrange_def lvbmap_def 
  by (auto simp: o_def restrict_def)

lemma (in valid_lvalue_basic) lvalue_basic_map_id: "lvbmap id = lvb"
  apply (subst (2) lvb_def) 
  using repr_ext by (auto simp: lvbmap_def extensional_def restrict_def)

(* lemma (in lvalue_basic) "F = lv_factorization lvb" *)

lemma (in valid_lvalue_basic) valid_lvalue_basic_map:
  (* assumes "valid_lvalue_basic lvb" *)
  assumes "inj_on f lvrange"
  shows "valid_lvalue_basic (lvbmap f)"
  apply intro_locales
   apply (simp_all add: lvbmap_def lvalue_locale_defs, unfold lvalue_locale_defs[symmetric])
   apply (simp add: valid_lvalue_factorization_axioms)
  by (metis assms comp_inj_on factors_I inj_on_restrict inj_repr lvalue_basic.lvb_def lvalue_basic.select_convs(1) lvalue_basic.select_convs(2) lvalue_basic.select_convs(3) lvrange_def restrict_extensional valid_lvalue_basic_axioms_def)
(* TODO same for lvalue *)

lemma (in lvalue_basic) lvalue_basic_range_map[simp]: "lvalue_basic.lvrange (lvbmap f) = f ` lvrange"
  by (smt image_cong image_image lvalue_basic.lvbmap_def lvalue_basic.lvrange_def lvalue_basic.select_convs(2) lvalue_basic.select_convs(3) lvalue_basic.simps(1) lvalue_locale_defs(1) o_def restrict_simp)
(* TODO same for lvalue *)

definition (in lvalue_basic) "lvbdomain = domain"

lemma (in lvalue_basic) lvalue_basic_domain_map[simp]: "lvalue_basic.lvbdomain (lvbmap f) = domain"
  by (simp add: lvalue_basic.F_def lvalue_basic.lvbdomain_def lvbmap_def)
(* TODO same for lvalue *)

definition (in lvalue_basic)
  "lvalue_basic_fun x
  = repr (restrict (isom x) factors)"

(* fun lvalue_basic_fun where
  "lvalue_basic_fun \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr> x
  = repr (restrict (lvf_isomorphism factorization x) factors)"
 *)

definition  (in lvalue_basic) 
  "lvalue_basic_corange_raw = (dependent_functions (I - factors) sets)"

fun lvalue_basic_corange_raw where
  "lvalue_basic_corange_raw \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr>
  = (dependent_functions (lvf_index_set factorization - factors) (lvf_sets factorization))"

definition (in lvalue_basic) lvalue_basic_cofun_squash :: "('b \<Rightarrow> 'c) \<Rightarrow> 'a"  where
  "lvalue_basic_cofun_squash = (SOME f. inj_on f (lvalue_basic_corange_raw))"

lemma (in valid_lvalue_basic) lvalue_basic_cofun_squash:
  shows "inj_on (lvalue_basic_cofun_squash) (lvalue_basic_corange_raw)"
proof -
  have "leq_card (lvalue_basic_corange_raw) (UNIV::'a set)"
  proof -
    have "lvalue_basic_corange_raw = dependent_functions (I - factors) sets"
      by (metis lvalue_basic_corange_raw_def)
    also have "leq_card \<dots> (dependent_functions I sets)"
      apply (rule leq_cardI_surj[where f="%f. restrict f (I-factors)"])
      apply (rule equalityD2)
      apply (rule dependent_functions_restrict_surj)
      apply auto[1]
      by (simp add: sets_nonempty)
    also have "leq_card \<dots> domain"
      by simp
    also have "leq_card \<dots> (UNIV::'a set)"
      by simp
    finally show ?thesis.
  qed
  then have "\<exists>f::_\<Rightarrow>'a. inj_on f (lvalue_basic_corange_raw)"
    unfolding leq_card_def by auto
  then show ?thesis
    unfolding lvalue_basic_cofun_squash_def
    by (rule someI_ex[where P="%f. inj_on f (lvalue_basic_corange_raw )"])
qed

definition (in lvalue_basic) "lvalue_basic_corange = lvalue_basic_cofun_squash ` lvalue_basic_corange_raw"

definition (in lvalue_basic)
  "lvalue_basic_cofun_raw x = restrict (isom x) (I - factors)"

definition (in lvalue_basic) "lvalue_basic_cofun x = (lvalue_basic_cofun_squash (lvalue_basic_cofun_raw x))"

lemma (in valid_lvalue_basic) lvalue_basic_fun_raw_bij:
  shows "bij_betw (\<lambda>x. (lvalue_basic_fun x, lvalue_basic_cofun_raw x)) 
                  (domain) (lvrange \<times> lvalue_basic_corange_raw)"
proof -
  show ?thesis
  proof -
    note bij_betw_trans[trans]
    have "bij_betw isom domain (dependent_functions I sets)"
      by (simp add: bij_betw_isom)
    also have "bij_betw (\<lambda>f. (restrict f factors, restrict f (I-factors)))
      (dependent_functions I sets)
      (dependent_functions factors sets \<times> dependent_functions (I-factors) sets)"
    proof -
      have uni: "I = factors \<union> (I-factors)"
        using factors_I by auto
      show ?thesis
        apply (subst uni, rule dependent_functions_split)
        by (simp add: disjnt_def)
    qed
    also 
    have "bij_betw (map_prod repr id)
        (dependent_functions factors sets \<times> dependent_functions (I-factors) sets)
        (lvrange \<times> lvalue_basic_corange_raw)"
      by (simp add: bij_betw_map_prod inj_on_imp_bij_betw inj_repr lvalue_basic_corange_raw_def lvrange_def)

      finally show ?thesis
        by (smt bij_betw_cong comp_apply id_apply lvalue_basic_cofun_raw_def lvalue_basic_fun_def map_prod_simp)
  qed
qed

lemma (in valid_lvalue_basic) lvalue_basic_fun_bij:
  shows "bij_betw (\<lambda>x. (lvalue_basic_fun x, lvalue_basic_cofun x)) 
                  (domain) (lvrange \<times> lvalue_basic_corange )"
(* TODO same for lvalue *)
proof -
  note bij_betw_trans[trans]
  note lvalue_basic_fun_raw_bij
  also have "bij_betw (apsnd (lvalue_basic_cofun_squash ))
                      (lvrange \<times> lvalue_basic_corange_raw )
                      (lvrange \<times> lvalue_basic_corange )"
    unfolding lvalue_basic_cofun_squash apsnd_def
    apply (rule bij_betw_map_prod)
    apply simp
    by (simp add: bij_betw_imageI lvalue_basic_cofun_squash lvalue_basic_corange_def)
  finally show ?thesis
    unfolding lvalue_basic_cofun_def o_def by simp
qed

definition (in lvalue_basic_compatible)
  "lvalue_basic_compose 
    =  \<lparr> lv_factorization=a.F, lv_factors=a.factors \<union> b.factors, 
         lv_representation=restrict (\<lambda>x. (a.repr (restrict x a.factors), 
                                          b.repr (restrict x b.factors)))
                                      (dependent_functions (a.factors\<union>b.factors) a.sets) \<rparr>"


(* fun lvalue_basic_compose :: "('a,'b,'c,'d) lvalue_basic \<Rightarrow> ('a,'b,'c,'e) lvalue_basic \<Rightarrow> ('a,'b,'c,'d*'e) lvalue_basic" where
  "lvalue_basic_compose \<lparr> lv_factorization=factorization1, lv_factors=a.factors, lv_representation=repr1 \<rparr>
                        \<lparr> lv_factorization=factorization2, lv_factors=b.factors, lv_representation=repr2 \<rparr> 
    =  \<lparr> lv_factorization=factorization1, lv_factors=a.factors \<union> b.factors, 
         lv_representation=restrict (\<lambda>x. (repr1 (restrict x a.factors), 
                                          repr2 (restrict x b.factors)))
                                      (dependent_functions (a.factors\<union>b.factors) (lvf_sets factorization1)) \<rparr>"
 *)

lemma (in lvalue_basic_compatible) lvalue_basic_compose_fun:
  assumes x: "x : a.domain"
  shows "lvalue_basic.lvalue_basic_fun (lvalue_basic_compose) x = (a.lvalue_basic_fun x, b.lvalue_basic_fun x)"
(* TODO same for lvalue *)
proof -
  (* have same_fact: "lv_factorization lv1 = lv_factorization lv2" by cases    *)
  (* obtain factorization a.factors repr1 where *)
    (* lv1: "lv1 = \<lparr> lv_factorization=factorization, lv_factors=a.factors, lv_representation=repr1 \<rparr>" *)
    (* apply atomize_elim apply (cases lv1) by simp *)
  (* with same_fact obtain b.factors repr2 where *)
    (* lv2: "lv2 = \<lparr> lv_factorization=factorization, lv_factors=b.factors, lv_representation=repr2 \<rparr>" *)
    (* apply atomize_elim apply (cases lv1) apply auto *)
    (* by (metis (full_types) lvalue_basic.surjective old.unit.exhaust) *)

  (* from compat have factors_disj: "a.factors \<inter> b.factors = {}" apply cases unfolding lv1 lv2 by simp *)
(*   have valid1: "valid_lvalue_basic lv1"
    by (simp add: a.valid_lvalue_basic_axioms) apply cases by simp
  then have "valid_lvalue_factorization factorization" unfolding lv1 apply cases by simp *)
  (* then obtain domain I sets isom where
    factorization: "factorization = \<lparr>lvf_domain = domain, lvf_index_set = I, lvf_sets = sets, lvf_isomorphism = isom\<rparr>"
    and "domain \<noteq> {}"
    and "sets \<in> extensional I"
    and "isom \<in> extensional domain"
    and bij: "bij_betw isom domain (dependent_functions I sets)"
    apply cases by auto *)

  (* define I where "I = a.I" *)

  have factors1: "a.factors \<subseteq> a.I"
    by (simp add: a.factors_I)
  (* have valid2: "valid_lvalue_basic lv2" apply cases by simp *)
  have factors2: "b.factors \<subseteq> a.I"
    by (simp add: b.factors_I same_F)
    
(*   from x have x: "x \<in> a.domain"
    unfolding lv1 lvalue_basic_domain_def factorization by simp *)

  have restrict: "restrict (a.isom x) (a.factors \<union> b.factors)
    \<in> dependent_functions (a.factors \<union> b.factors) a.sets"
    apply (rule dependent_functions_restrict[where D=a.I])
    using a.bij_betw_isom bij_betwE x apply blast
    by (simp add: factors1 factors2)
(*     using bij x bij_betwE factorization apply auto[1]
    apply blast
    apply blast
    by (simp add: a.factors b.factors)
 *)

  have "fst (lvalue_basic.lvalue_basic_fun (lvalue_basic_compose) x) = a.lvalue_basic_fun x"
    unfolding lvalue_basic_compose_def a.lvalue_basic_fun_def lvalue_basic.lvalue_basic_fun_def
    apply (simp add: lvalue_locale_defs)
    apply (simp add: lvalue_locale_defs[symmetric])
    by (metis Pi_split_domain inf_commute inf_sup_absorb restrict restrict_PiE)
  moreover have "snd (lvalue_basic.lvalue_basic_fun (lvalue_basic_compose) x) = b.lvalue_basic_fun x"
    unfolding lvalue_basic_compose_def b.lvalue_basic_fun_def lvalue_basic.lvalue_basic_fun_def
    apply (simp add: lvalue_locale_defs)
    apply (simp add: lvalue_locale_defs[symmetric])
    by (metis Pi_split_domain inf_sup_absorb inf_sup_aci(1) inf_sup_aci(5) restrict restrict_PiE same_F)
  ultimately show ?thesis
    by (metis prod.collapse)
qed

(* 
lemma (in lvalue_basic_compatible) lvalue_basic_compose_valid:
  (* assumes "lvalue_basic_compatible lv1 lv2" *)
  shows "valid_lvalue_basic (lvalue_basic_compose)" *)
sublocale lvalue_basic_compatible \<subseteq> valid_lvalue_basic lvalue_basic_compose
(* TODO same for lvalue *)
proof -
  (* from assms have same_fact: "lv_factorization lv1 = lv_factorization lv2" by cases    *)
  (* obtain factorization a.factors repr1 where *)
    (* lv1: "lv1 = \<lparr> lv_factorization=factorization, lv_factors=a.factors, lv_representation=repr1 \<rparr>" *)
    (* apply atomize_elim apply (cases lv1) by simp *)
  (* with same_fact obtain b.factors repr2 where *)
    (* lv2: "lv2 = \<lparr> lv_factorization=factorization, lv_factors=b.factors, lv_representation=repr2 \<rparr>" *)
    (* apply atomize_elim apply (cases lv1) apply auto *)
    (* by (metis (full_types) lvalue_basic.surjective old.unit.exhaust) *)

  (* from assms have valid1: "valid_lvalue_basic lv1" by cases *)
  (* then have valid_fact: "valid_lvalue_factorization factorization" *)
    (* apply cases unfolding lv1 by simp *)
(*   from valid1 have inj_repr1: "inj_on repr1 (dependent_functions a.factors (lvf_sets factorization))"
    apply cases unfolding lv1 by simp *)

(*   from assms have valid2: "valid_lvalue_basic lv2" by cases
  from valid2 have inj_repr2: "inj_on repr2 (dependent_functions b.factors (lvf_sets factorization))"
    apply cases unfolding lv2 by simp *)

  have fact_union: "a.factors \<union> b.factors \<subseteq> a.I"
    using a.factors_I b.factors_I same_F by auto
    (* by (metis Un_subset_iff assms lv1 lv2 lvalue_basic.select_convs(1) lvalue_basic.select_convs(2) lvalue_basic_compatible.cases valid_lvalue_basic.cases) *)
  
  have inj: "inj_on
     ( (\<lambda>x\<in>(dependent_functions (a.factors \<union> b.factors) (a.sets)). (a.repr (restrict x a.factors), b.repr (restrict x b.factors)))
       )
     (dependent_functions (a.factors \<union> b.factors) (a.sets))"
    apply (subst inj_on_restrict)
    thm inj_on_restrict
(* TODO apply rule that removes the restrict. Like inj_on (restrict f I) I = inj_on f I. *)
  proof (rule inj_onI, rule ext)
    fix x y i
    assume x: "x \<in> dependent_functions (a.factors \<union> b.factors) (a.sets)"
    then have x_factors1: "restrict x a.factors : dependent_functions a.factors a.sets"
          and x_factors2: "restrict x b.factors : dependent_functions b.factors a.sets"
      using dependent_functions_restrict by auto
    assume y: "y \<in> dependent_functions (a.factors \<union> b.factors) a.sets"
    then have y_factors1: "restrict y a.factors : dependent_functions a.factors a.sets"
          and y_factors2: "restrict y b.factors : dependent_functions b.factors a.sets"
      using dependent_functions_restrict by auto
    assume eq: "(a.repr (restrict x a.factors), b.repr (restrict x b.factors)) =
            (a.repr (restrict y a.factors), b.repr (restrict y b.factors))"
    then have "a.repr (restrict x a.factors) = a.repr (restrict y a.factors)"
      by simp
    from a.inj_repr this x_factors1 y_factors1
    have eq1: "restrict x a.factors = restrict y a.factors"
      by (rule inj_onD[where f=a.repr])
    from eq have "b.repr (restrict x b.factors) = b.repr (restrict y b.factors)"
      by simp
    from b.inj_repr this x_factors2 y_factors2
    have eq2: "restrict x b.factors = restrict y b.factors"
      unfolding same_sets
      by (rule inj_onD[where f=b.repr])

    consider (factors1) "i \<in> a.factors" | (factors2) "i \<in> b.factors" | (outside) "i \<notin> a.factors \<union> b.factors"
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
        by blast
      from y outside have yi: "y i = undefined"
        by blast
      from xi yi show ?thesis
        by simp
    qed
  qed

(*   have outside: "f \<notin> dependent_functions (a.factors \<union> b.factors) a.sets \<Longrightarrow>
          (\<lambda>x\<in>dependent_functions (a.factors \<union> b.factors) a.sets. 
            (a.repr (restrict x a.factors), b.repr (restrict x b.factors))) f =
         undefined" for f
    unfolding restrict_def by simp
 *)

  show "valid_lvalue_basic lvalue_basic_compose"
    apply intro_locales
     apply (metis (mono_tags, lifting) b.valid_lvalue_factorization_axioms lvalue_basic.F_def lvalue_basic.select_convs(1) lvalue_basic_compose_def same_F)
    apply unfold_locales
    unfolding lvalue_basic_compose_def
      apply (simp_all add: lvalue_locale_defs)
     apply (simp_all add: lvalue_locale_defs[symmetric])
    using a.factors_I b.factors_I same_F apply auto[1]
    using inj by auto
qed


lemma (in lvalue_basic_compatible) lvalue_basic_domain_compose:
  (* assumes compat: "lvalue_basic_compatible lvb1 lvb2" *)
  shows "domain = a.domain"
    and "domain = b.domain"
  using F_def lvalue_basic_compose_def apply auto[1]
  using F_def lvalue_basic_compose_def same_F by auto
(* TODO same for lvalue *)

lemma (in lvalue_basic_compatible) lvalue_basic_range_compose:
  (* assumes compat: "lvalue_basic_compatible lvb1 lvb2" *)
  shows "lvrange = a.lvrange \<times> b.lvrange"
(* TODO same for lvalue *)
proof -
  (* from assms have same_fact: "lv_factorization lvb1 = lv_factorization lvb2" by cases    *)
(*   obtain factorization a.factors repr1 where
    lv1: "lvb1 = \<lparr> lv_factorization=factorization, lv_factors=a.factors, lv_representation=repr1 \<rparr>"
    apply atomize_elim apply (cases lvb1) by simp
  with same_fact obtain b.factors repr2 where
    lv2: "lvb2 = \<lparr> lv_factorization=factorization, lv_factors=b.factors, lv_representation=repr2 \<rparr>"
    apply atomize_elim apply (cases lvb1) apply auto
    by (metis (full_types) lvalue_basic.surjective old.unit.exhaust)

  from assms have factors_disj: "a.factors \<inter> b.factors = {}" apply cases unfolding lv1 lv2 by simp *)

  have "(\<lambda>x. (restrict x a.factors, restrict x b.factors)) `
        dependent_functions (a.factors \<union> b.factors) a.sets =
            dependent_functions a.factors a.sets \<times>
            dependent_functions b.factors a.sets"
    using dependent_functions_split[OF disj_factors, where A="a.sets"]
    by (simp add: bij_betw_def)
  also have "(map_prod a.repr b.repr) ` \<dots> = a.lvrange \<times> b.lvrange"
    apply (rule map_prod_surj_on)
    unfolding a.lvrange_def b.lvrange_def same_sets by simp_all
  finally show ?thesis
    unfolding a.lvrange_def b.lvrange_def same_sets 
    unfolding map_prod_def image_comp o_def
    using lvalue_basic_compose_def lvb_def lvrange_def same_F by auto
qed


locale lvalue_basic_squash = valid_lvalue_basic + squash_factorization F
begin
definition "factors' = I_map ` factors"
definition "repr' = (\<lambda>f\<in>dependent_functions factors' sets'. repr (\<lambda>i\<in>factors. (inv_sets_map i (f (I_map i)))))"
definition "lv' =  \<lparr> lv_factorization=F', lv_factors=factors', 
                     lv_representation=repr' \<rparr>"
end

(* fun lvalue_basic_squash1 :: "('a,'b,'c,'d) lvalue_basic \<Rightarrow> ('a,'a,'a,'d) lvalue_basic" where
  "lvalue_basic_squash1 \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr> = 
    (let (factorization',I_map,sets_map) = factorization_squash factorization;
         inv_sets_map = \<lambda>i. inv_into (lvf_sets factorization i) (sets_map i);
         factors' = I_map ` factors;
         repr' = \<lambda>f\<in>dependent_functions factors' (lvf_sets factorization'). repr (\<lambda>i\<in>factors. (inv_sets_map i (f (I_map i))));
         lv' =  \<lparr> lv_factorization=factorization', lv_factors=I_map ` factors, 
                  lv_representation=repr' \<rparr>;
         f::'d\<Rightarrow>'a = SOME f. inj_on f (lvalue_basic_range lv')
     in lv')" *)

(* lemma 
  fixes A :: "'a set" and C :: "'c set"
  assumes "inj_on F (Pi\<^sub>E C D)"
  shows "inj_on (\<lambda>f. F (\<lambda>x\<in>C. f (g x))) (Pi\<^sub>E A B)"
proof (rule inj_onI, rename_tac f1 f2)
  fix f1 f2
  assume f1:"f1 \<in> dependent_functions A B"
    and f2:"f2 \<in> dependent_functions A B"
    and eq: "F (\<lambda>x\<in>C. f1 (g x)) = F (\<lambda>x\<in>C. f2 (g x))"
  have "(\<lambda>x\<in>C. f1 (g x)) \<in> PiE C D"
    apply
    find_theorems intro Pi\<^sub>E
    sorry
  moreover have "(\<lambda>x\<in>C. f2 (g x)) \<in> PiE C D"
    sorry
  ultimately have "(\<lambda>x\<in>C. f1 (g x)) = (\<lambda>x\<in>C. f2 (g x))"
    by (metis assms eq inj_onD)
  show "f1 = f2"
  qed *)

lemma (in valid_lvalue_basic) factors_then_I[simp]: "i\<in>factors \<Longrightarrow> i\<in>I" for i
  using factors_I by auto

sublocale lvalue_basic_squash \<subseteq> squash1: valid_lvalue_basic lv'
  apply (intro_locales) defer 
proof unfold_locales[1]
  show "valid_lvalue_factorization (lvalue_basic.F lv')"
    by (metis lv'_def lvalue_basic.select_convs(1) lvalue_locale_defs squash.valid_lvalue_factorization_axioms)
  
(*   have squash1: "lvalue_basic_squash1 lvb = \<lparr>lv_factorization = factorization', lv_factors = factors',
       lv_representation = repr'\<rparr>"
    by (simp add: squash 1 repr'_def inv_sets_map_def factors'_def)
 *)(*   have "valid_lvalue_factorization factorization'"
    using "1"(2) factorization_squash_valid squash by blast *)
(*   moreover have "factors' \<subseteq> lvf_index_set factorization'"
    apply (subst factorization_squash_index_set)
    unfolding factors'_def using valid_fact squash apply auto[2]
    by (simp add: "1"(3) image_mono) *)
  (* moreover *)
  have "inj_on repr' (Pi\<^sub>E factors' sets')"
  proof (rule inj_onI, goal_cases)
    case (1 x y)
    from 1 have "repr (\<lambda>i\<in>factors. inv_sets_map i (x (I_map i))) = repr (\<lambda>i\<in>factors. inv_sets_map i (y (I_map i)))"
      unfolding repr'_def factors'_def by simp
    moreover have "(\<lambda>i\<in>factors. inv_sets_map i (x (I_map i))) \<in> Pi\<^sub>E factors sets"
      apply (rule PiE_I, simp add: inv_sets_map_def)
       apply (rule inv_into_into, simp)
      using "1"(1) unfolding factors'_def apply force by auto
    moreover have "(\<lambda>i\<in>factors. inv_sets_map i (y (I_map i))) \<in> Pi\<^sub>E factors sets"
      apply (rule PiE_I, simp add: inv_sets_map_def)
       apply (rule inv_into_into, simp)
      using "1" unfolding factors'_def apply blast by auto
    ultimately have "(\<lambda>i\<in>factors. inv_sets_map i (x (I_map i))) = (\<lambda>i\<in>factors. inv_sets_map i (y (I_map i)))"
      by (rule inj_onD[OF inj_repr])
    then have "inv_sets_map i (x (I_map i)) = inv_sets_map i (y (I_map i))" if "i\<in>factors" for i
      by (metis (mono_tags, lifting) restrict_simp that)
    then have xy: "(x (I_map i)) = (y (I_map i))" if "i\<in>factors" for i
      using "1"(1) "1"(2) inv_sets_map_def inv_into_injective that by fastforce
    show ?case
      apply (rule extensionalityI)
      using 1 xy unfolding PiE_def factors'_def by auto
  qed
  then show "inj_on (lv_representation lv') (dependent_functions (lv_factors lv') (lvf_sets (lvalue_basic.F lv')))"
    by (metis F'_def lv'_def lvalue_basic.select_convs(1) lvalue_basic.select_convs(2) lvalue_basic.select_convs(3) lvalue_factorization.select_convs(3) lvalue_locale_defs)

  moreover have "repr' x = undefined" 
    if "x \<notin> dependent_functions factors' sets'" for x
    using that unfolding repr'_def by auto
  then show "lv_representation lv' \<in> extensional (dependent_functions (lv_factors lv') (lvf_sets (lvalue_basic.F lv')))"
    by (metis F'_def extensionalI lv'_def lvalue_basic.select_convs(1) lvalue_basic.select_convs(2) lvalue_basic.select_convs(3) lvalue_factorization.select_convs(3) lvalue_locale_defs)

  show "lv_factors lv' \<subseteq> lvf_index_set (lvalue_basic.F lv')"
    by (metis F'_def I'_def factors'_def factors_I image_mono lv'_def lvalue_basic.select_convs(1) lvalue_basic.select_convs(2) lvalue_factorization.select_convs(2) lvalue_locale_defs)
qed


definition (in lvalue_basic_squash) "(f::'d\<Rightarrow>'a) = (SOME f. inj_on f squash1.lvrange)"
definition (in lvalue_basic_squash) "f' = inv_into squash1.lvrange f"
(* TODO make lvbmap into a locale and then do some sublocale stuff *)
definition (in lvalue_basic_squash) "squashed = squash1.lvbmap f"

lemma (in lvalue_basic_squash) inj_f: "inj_on f squash1.lvrange"
proof -
  have "leq_card squash1.lvrange squash1.domain"
    by (simp add: squash1.lvalue_basic_range_leq_domain)
  also have "leq_card \<dots> (UNIV::'a set)"
    by simp
  finally have "\<exists>f::'d\<Rightarrow>'a. inj_on f squash1.lvrange"
    by (simp add: leq_card_def)
  then show "inj_on f squash1.lvrange"
    unfolding f_def by (rule someI_ex)
qed

(* definition lvalue_basic_squash2 :: "('a,'b,'c,'d) lvalue_basic \<Rightarrow> ('a,'b,'c,'a) lvalue_basic * ('a\<Rightarrow>'d)" where
  "lvalue_basic_squash2 lv = 
    (let f::'d\<Rightarrow>'a = SOME f. inj_on f (lvalue_basic_range lv);
         lv' = lvalue_basic_map f lv;
         f' = inv_into (lvalue_basic_range lv) f
     in (lv',f'))" *)

(* definition "lvalue_basic_squash = lvalue_basic_squash2 o lvalue_basic_squash1" *)

sublocale lvalue_basic_squash \<subseteq> squash2: valid_lvalue_basic squashed
  apply (intro_locales) defer apply unfold_locales[1]
proof -
  show "lv_factors squashed \<subseteq> lvf_index_set (lvalue_basic.F squashed)"
    by (simp add: inj_f squash1.valid_lvalue_basic_map squashed_def valid_lvalue_basic.factors_I)
  
  show "inj_on (lv_representation squashed) (dependent_functions (lv_factors squashed) (lvf_sets (lvalue_basic.F squashed)))"
    by (simp add: inj_f squash1.valid_lvalue_basic_map squashed_def valid_lvalue_basic.inj_repr)

  show "lv_representation squashed
    \<in> extensional (dependent_functions (lv_factors squashed) (lvf_sets (lvalue_basic.F squashed)))"
    by (simp add: inj_f squash1.valid_lvalue_basic_map squashed_def valid_lvalue_basic.repr_ext)

  show "valid_lvalue_factorization (lvalue_basic.F squashed)"
    by (simp add: inj_f squash1.valid_lvalue_basic_map squashed_def valid_lvalue_basic.axioms(1))
qed

(* lemma lvalue_basic_squash_valid:
  assumes "valid_lvalue_basic lvb"
  shows "valid_lvalue_basic (fst (lvalue_basic_squash lvb))"
  sorry *)

(* lemma PiE_permute1:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes "g ` A \<subseteq> A'"
  assumes "\<And>a. a:A \<Longrightarrow> h a ` B' (g a) \<subseteq> B a"
  (* assumes "\<And>x. x\<in>A \<Longrightarrow> g' (g x) = x" *)
  shows "(\<lambda>f. (\<lambda>a\<in>A. h a (f (g a)))) ` Pi\<^sub>E A' B' \<subseteq> Pi\<^sub>E A B"
proof auto
  show "f \<in> dependent_functions A' B' \<Longrightarrow> a \<in> A \<Longrightarrow> h a (f (g a)) \<in> B a" for f a
    using assms(1) assms(2) by fastforce
qed *)

(*
lemma PiE_permute:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes "g ` A \<subseteq> A'"
  assumes "\<And>a. a:A \<Longrightarrow> h a ` B' (g a) \<subseteq> B a"
  (* assumes "\<And>x. x\<in>A \<Longrightarrow> g' (g x) = x" *)
  defines "M == (\<lambda>f. (\<lambda>a\<in>A. h a (f (g a))))"
  shows "M ` Pi\<^sub>E A' B' = Pi\<^sub>E A B"
proof rule
  show "M ` dependent_functions A' B' \<subseteq> dependent_functions A B"
    unfolding M_def apply (rule PiE_permute1) using assms by auto
  define M' :: "('a\<Rightarrow>'b) \<Rightarrow> ('c\<Rightarrow>'d)" where "M' = (\<lambda>f. \<lambda>a\<in>A'. h' a (f (g' a)))"
  have "dependent_functions A B = M ` M' ` PiE A B"
    by x
  have "M' ` PiE A B \<subseteq> Pi\<^sub>E A B"
  show "dependent_functions A B \<subseteq> M ` dependent_functions A' B'"
    
  proof
    show "f \<in> dependent_functions A B \<Longrightarrow> f \<in> (\<lambda>f. \<lambda>a\<in>A. h a (f (g a))) ` dependent_functions A' B'" for f
      by x
  qed
qed

(* proof auto
  show "\<And>f xa. f \<in> dependent_functions (g ` A) (\<lambda>x. h x ` B (g1 x)) \<Longrightarrow> xa \<in> A \<Longrightarrow> h (g1 xa) (f (g xa)) \<in> B xa"
    by x
  show "\<And>x. x \<in> dependent_functions A B \<Longrightarrow> x \<in> (\<lambda>f. \<lambda>x\<in>A. h (f (g x))) ` dependent_functions (g ` A) (\<lambda>x. h ` B (g1 x))"
    by x
qed *)
  sorry
*)

lemma (in lvalue_basic_squash) lvalue_basic_squash1_range[simp]: "squash1.lvrange = lvrange"
proof -
  thm lv'_def repr'_def sets'_def
  have "(\<lambda>f. (\<lambda>i\<in>factors. inv_sets_map i (f (I_map i)))) ` dependent_functions factors' sets' = dependent_functions factors sets"
  proof (rule; rule subsetI)
    fix g assume g: "g \<in> (\<lambda>f. \<lambda>i\<in>factors. inv_sets_map i (f (I_map i))) ` dependent_functions factors' sets'"
    show "g \<in> dependent_functions factors sets"
      apply (rule PiE_I)
      using g by (auto simp: PiE_mem factors'_def inv_sets_map_sets)
  next
    fix g assume g: "g \<in> dependent_functions factors sets"
    define h where "h = (\<lambda>i\<in>factors'. sets_map (inv_I_map i) (g (inv_I_map i)))"
    have h_PiE: "h : dependent_functions factors' sets'"
    proof (rule PiE_I)
      fix i
      assume i: "i \<in> factors'"
      then have "inv_I_map i \<in> factors"
        unfolding factors'_def by auto
      with g have "g (inv_I_map i) \<in> sets (inv_I_map i)"
        by auto
      then have "sets_map (inv_I_map i) (g (inv_I_map i)) \<in> sets_map (inv_I_map i) ` sets (inv_I_map i)"
        by blast
      with i show "h i \<in> sets' i"
        unfolding sets'_def h_def factors'_def by auto
    next
      fix x
      show "x \<notin> factors' \<Longrightarrow> h x = undefined"
        by (simp add: h_def)
    qed 
    have h_g: "(\<lambda>i\<in>factors. inv_sets_map i (h (I_map i))) = g"
    proof (rule extensionalityI[where A=factors], simp)
      from g show "g \<in> extensional factors"
        by (simp add: PiE_iff)
      fix i assume i: "i : factors"
      then have "(\<lambda>i\<in>factors. inv_sets_map i (h (I_map i))) i = inv_sets_map i (h (I_map i))"
        by simp
      also with i have "\<dots> = inv_sets_map i (sets_map (inv_I_map (I_map i)) (g (inv_I_map (I_map i))))"
        by (simp add: factors'_def h_def)
      also with i have "\<dots> = inv_sets_map i (sets_map i (g i))"
        by auto
      also with g i have "\<dots> = (g i)"
        by (subst inv_sets_map, auto)
      finally show "(\<lambda>i\<in>factors. inv_sets_map i (h (I_map i))) i = g i".
    qed
    show "g \<in> (\<lambda>f. \<lambda>i\<in>factors. inv_sets_map i (f (I_map i))) ` dependent_functions factors' sets'"
      using h_PiE h_g by auto
  qed
  then have "repr' ` dependent_functions factors' sets' = repr ` (dependent_functions factors sets)"
    unfolding repr'_def apply simp
    by (metis image_image)
  then show ?thesis
    using F'_def F_def    
    by (simp add: squash1.lvrange_def lv'_def lvalue_basic.lvrange_def lvalue_basic.F_def)
qed

lemma (in lvalue_basic_squash) lvalue_basic_squash2_range[simp]: "squash2.lvrange = f ` lvrange" 
  unfolding squashed_def by simp

lemma (in lvalue_basic_squash) lvalue_basic_squash_bij[simp]:
  shows "bij_betw f lvrange squash2.lvrange"
  using inj_f inj_on_imp_bij_betw by auto

lemma (in lvalue_basic_squash) lvalue_basic_squash_bij':
  shows "bij_betw f' squash2.lvrange lvrange"
  using lvalue_basic_squash_bij f'_def by (simp add: bij_betw_inv_into)

lemma (in lvalue_basic_squash) lvalue_basic_squash2_map: "squash2.lvbmap f' = lv'"
proof -
  have "squash2.lvbmap f' = squash1.lvbmap id"
    unfolding squashed_def squash1.lvalue_basic_map_o
    apply (rule lvalue_basic.lvalue_basic_map_cong)
    using f'_def inj_f by auto
  also have "\<dots> = lv'"
    by (simp add: squash1.lvalue_basic_map_id) 
  finally show ?thesis.
qed

lemma (in lvalue_basic_squash) lvalue_basic_squash2_domain[simp]: "squash2.domain = domain"
proof -
  have "squash2.domain = squash1.domain"
    by (metis lvalue_basic.lvalue_basic_domain_map lvalue_basic_squash2_map squash1.lvbdomain_def)
  also have "\<dots> = domain"
    apply (simp add: lv'_def lvalue_basic.F_def squash_factorization.F'_def)
    using F'_def F_def by auto
  finally show ?thesis.
qed

fun lvalue_basic_domain_map :: "('a\<Rightarrow>'b) \<Rightarrow> ('a set) \<Rightarrow> ('b,'c) lvalue_basic \<Rightarrow> ('a,'c) lvalue_basic" where
"lvalue_basic_domain_map f D \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr>
  = (* \<lparr> lv_factorization=factorization_domain_map f D factorization, lv_factors=factors, lv_representation=repr \<rparr> *)undefined" (* TODO *)

lemma lvalue_basic_domain_map_domain[simp]:
  shows "lvalue_basic_domain (lvalue_basic_domain_map f D lvb) = D"
  sorry

definition lvalue_basic_id :: "'a set \<Rightarrow> ('a,'a) lvalue_basic" where
  "lvalue_basic_id D = make_lvalue_basic (factorization_id D) {undefined} (\<lambda>f. Rep_factor (f undefined))"



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


section \<open>lvalue\<close>

datatype ('a,'b) lvalue = 
  LValueBasic "('a,'a,'a,'b) lvalue_basic"
  (* LValueChained lv lvb = lv o lvb *)
  | LValueChained "('a,'b) lvalue" "('a,'a,'a,'a) lvalue_basic"

fun lvalue_domain where
  "lvalue_domain (LValueBasic lvb) = lvalue_basic.lvbdomain lvb"
| "lvalue_domain (LValueChained lv lvb) = lvalue_basic.lvbdomain lvb"


fun lvalue_range where
  "lvalue_range (LValueBasic lvb) = lvalue_basic.lvrange lvb"
| "lvalue_range (LValueChained lv lvb) = lvalue_range lv"

fun lvalue_map where
  "lvalue_map f (LValueBasic lvb) = LValueBasic (lvalue_basic.lvbmap lvb f)"
| "lvalue_map f (LValueChained lv lvb) = LValueChained (lvalue_map f lv) lvb"

inductive valid_lvalue where
  "valid_lvalue_basic lvb \<Longrightarrow> valid_lvalue (LValueBasic lvb)"
| "\<lbrakk> valid_lvalue lv; valid_lvalue_basic lvb; lvalue_domain lv = lvalue_basic_range lvb \<rbrakk>
       \<Longrightarrow> valid_lvalue (LValueChained lv lvb)"

fun lvalue_squash where
  "lvalue_squash (LValueBasic lvb) = (LValueBasic (lvalue_basic_squash.squashed lvb), lvalue_basic_squash.f' lvb)"
| "lvalue_squash (LValueChained lv lvb) = (let (lv',f) = lvalue_squash lv in (LValueChained lv' lvb, f))"

lemma lvalue_squash_bij:
  assumes "valid_lvalue lv"
  shows "bij_betw (snd (lvalue_squash lv)) (lvalue_range (fst (lvalue_squash lv))) (lvalue_range lv)"
proof (insert assms, induction lv)
  case (LValueBasic x)
  then show ?case
    apply cases
    apply (simp add: case_prod_beta)
    apply (subst lvalue_basic_squash.lvalue_basic_squash2_range)
    apply (simp add: lvalue_basic_squash_def squash_factorization_def valid_lvalue_basic_def)
    using lvalue_basic_squash.lvalue_basic_squash2_range lvalue_basic_squash.lvalue_basic_squash_bij' lvalue_basic_squash_def squash_factorization_def valid_lvalue_basic_def by fastforce
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

definition lvalue_product :: "('a,'b) lvalue \<Rightarrow> ('c,'d) lvalue \<Rightarrow> ('a*'c,'b*'d) lvalue" where
  "lvalue_product = undefined" (* TODO *)

(* TODO remove *)
definition "make_lvalue_factorization D I sets isom =
    \<lparr> lvf_domain=D, lvf_index_set=I,
    lvf_sets=restrict sets I,
    lvf_isomorphism=restrict (\<lambda>a. restrict (isom a) I) D \<rparr>"

(* TODO remove *)
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

(* TODO remove *)
definition "make_lvalue_basic factorization factors repr
  = \<lparr> lv_factorization=factorization, lv_factors=factors,
      lv_representation=restrict repr (dependent_functions factors (lvf_sets factorization)) \<rparr>"

(* TODO remove *)
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
