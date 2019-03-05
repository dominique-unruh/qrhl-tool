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

definition "dependent_functions_restrict f S x = (if x\<in>S then f x else undefined)"

lemma dependent_functions_restrict:
  assumes "f \<in> dependent_functions D R"
  assumes D': "D' \<subseteq> D"
  shows "dependent_functions_restrict f D' \<in> dependent_functions D' R"
  apply (rule dependent_functions'.intros)
  unfolding dependent_functions_restrict_def apply auto
  by (meson assms contra_subsetD dependent_functions'.cases)

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
     bij_betw isom domain (dependent_functions I sets)
   \<rbrakk> \<Longrightarrow> valid_lvalue_factorization \<lparr> lvf_domain=domain, lvf_index_set=I, lvf_sets=sets, lvf_isomorphism=isom \<rparr>"

lemma lvalue_factorization_sets_nonempty:
  assumes "valid_lvalue_factorization F"
  assumes "i\<in>I"
  shows "lvf_sets F i \<noteq> {}"
  sorry

record ('a,'b) lvalue_basic = 
  lv_factorization :: "'a lvalue_factorization"
  lv_factors :: "'a index set"
  lv_representation :: "('a index \<Rightarrow> 'a factor) \<Rightarrow> 'b"

inductive valid_lvalue_basic :: "('a,'b) lvalue_basic \<Rightarrow> bool" where
  "\<lbrakk> valid_lvalue_factorization factorization;
     factors \<subseteq> lvf_index_set factorization;
     inj_on repr (dependent_functions factors (lvf_sets factorization))
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

fun lvalue_basic_map :: "('b\<Rightarrow>'c) \<Rightarrow> ('a,'b) lvalue_basic \<Rightarrow> ('a,'c) lvalue_basic" where
  "lvalue_basic_map f \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr>
    =  \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=f o repr \<rparr>"


lemma valid_map_lvaluex:
  assumes "valid_lvalue_basic lvb"
  assumes "inj_on f (lvalue_basic_range lvb)"
  shows "valid_lvalue_basic (lvalue_basic_map f lvb)"
  by (smt assms(1) assms(2) image_eqI inj_on_def lvalue_basic.select_convs(3) lvalue_basic.simps(1) lvalue_basic.simps(2) lvalue_basic_map.simps lvalue_basic_range_def o_apply valid_lvalue_basic.simps)
(* TODO same for lvalue *)

lemma lvalue_basic_range_map[simp]: "lvalue_basic_range (lvalue_basic_map f lvb) = f ` lvalue_basic_range lvb"
  apply (cases lvb) by (simp add: lvalue_basic_range_def image_image o_def)
(* TODO same for lvalue *)
lemma lvalue_basic_domain_map[simp]: "lvalue_basic_domain (lvalue_basic_map f lvb) = lvalue_basic_domain lvb"
  apply (cases lvb) by (simp add: lvalue_basic_domain_def o_def)
(* TODO same for lvalue *)


fun lvalue_basic_fun where
  "lvalue_basic_fun \<lparr> lv_factorization=factorization, lv_factors=factors, lv_representation=repr \<rparr> x
  = repr (dependent_functions_restrict (lvf_isomorphism factorization x) factors)"

fun lvalue_basic_compose :: "('a,'b) lvalue_basic \<Rightarrow> ('a,'c) lvalue_basic \<Rightarrow> ('a,'b*'c) lvalue_basic" where
  "lvalue_basic_compose \<lparr> lv_factorization=factorization1, lv_factors=factors1, lv_representation=repr1 \<rparr>
                        \<lparr> lv_factorization=factorization2, lv_factors=factors2, lv_representation=repr2 \<rparr> 
    =  \<lparr> lv_factorization=factorization1, lv_factors=factors1 \<union> factors2, 
         lv_representation=(\<lambda>x. (repr1 (dependent_functions_restrict x factors1), 
                                 repr2 (dependent_functions_restrict x factors2))) \<rparr>"

lemma lvalue_basic_compose_fun:
  assumes "lvalue_basic_compatible lv1 lv2"
  shows "lvalue_basic_fun (lvalue_basic_compose lv1 lv2) x = (lvalue_basic_fun lv1 x, lvalue_basic_fun lv2 x)"
  sorry
(* TODO same for lvalue *)

lemma lvalue_basic_compose_valid:
  assumes "lvalue_basic_compatible lv1 lv2"
  shows "valid_lvalue_basic (lvalue_basic_compose lv1 lv2)"
  sorry
(* TODO same for lvalue *)

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
  shows "lvalue_basic_range (lvalue_basic_compose lvb1 lvb2) = lvalue_basic_range lvb1 \<times> lvalue_basic_range lvb2"
(* TODO same for lvalue *)
  sorry

definition lvalue_basic_squash :: "('a,'b) lvalue_basic \<Rightarrow> ('a,'a) lvalue_basic * ('a\<Rightarrow>'b)" where
  "lvalue_basic_squash lv = 
    (let f::'b\<Rightarrow>'a = SOME f. inj_on f (lvalue_basic_range lv);
         lv' = lvalue_basic_map f lv;
         f' = inv_into (lvalue_basic_range lv) f
     in (lv',f'))"

lemma lvalue_basic_squash_bij:
  "bij_betw (snd (lvalue_basic_squash lv)) (lvalue_basic_range (fst (lvalue_basic_squash lv))) (lvalue_basic_range lv)"
  sorry

lemma lvalue_basic_squash_map:
  "lvalue_basic_map (snd (lvalue_basic_squash lv)) (fst (lvalue_basic_squash lv)) = lv"
  sorry

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

definition lvalue_compose :: "('a,'b) lvalue \<Rightarrow> ('a,'c) lvalue \<Rightarrow> ('a,'b*'c) lvalue" where
  "lvalue_compose = undefined"

fun lvalue_squash where
  "lvalue_squash (LValueBasic lvb) = (let (lvb',f) = lvalue_basic_squash lvb in (LValueBasic lvb', f))"
| "lvalue_squash (LValueChained lv lvb) = (let (lv',f) = lvalue_squash lv in (LValueChained lv' lvb, f))"

lemma lvalue_squash_bij:
  "bij_betw (snd (lvalue_squash lv)) (lvalue_range (fst (lvalue_squash lv))) (lvalue_range lv)"
  sorry

lemma lvalue_squash_map:
  "lvalue_map (snd (lvalue_squash lv)) (fst (lvalue_squash lv)) = lv"
  sorry

definition lvalue_basic_domain_map :: "('a\<Rightarrow>'b) \<Rightarrow> ('b,'c) lvalue_basic \<Rightarrow> ('a,'c) lvalue_basic" where
"lvalue_basic_domain_map = undefined" (* TODO *)

fun lvalue_chain_basic :: "('b,'c) lvalue_basic \<Rightarrow> ('a,'b) lvalue \<Rightarrow> ('a,'c) lvalue" where
  "lvalue_chain_basic lvb1 (LValueBasic lvb2) = (let (lvb2',f) = lvalue_basic_squash lvb2 in
    LValueChained (LValueBasic (lvalue_basic_domain_map f lvb1)) lvb2')"
| "lvalue_chain_basic lvb1 (LValueChained lv2 lvb2) = LValueChained (lvalue_chain_basic lvb1 lv2) lvb2"

fun lvalue_chain where
  "lvalue_chain (LValueBasic lvb1) lv2 = lvalue_chain_basic lvb1 lv2"
| "lvalue_chain (LValueChained lv1 lvb1) lv2 = lvalue_chain lv1 (lvalue_chain_basic lvb1 lv2)"


(* ================================= *)


lemma conj_to_conjunctionI: "A \<and> B \<Longrightarrow> (A &&& B)"
  by presburger

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


lemma bij_lvalue_raw_representation0:
  assumes "valid_lvalue_raw0 lv"
  shows "bij_betw (lvalue_raw_representation0 lv) (lvalue_domain0 lv) (lvalue_range0 lv \<times> lvalue_raw_representation_range0 lv)"

lemma bij_lvaluex_representation:
  assumes "valid_lvaluex lv"
  shows "bij_betw (lvaluex_representation lv) (lvaluex_domain lv) 
                  (lvaluex_range lv \<times> lvaluex_representation_range lv)"

definition "left_composition_map f x = (case x of (x,r) \<Rightarrow> case f r of (y,s) \<Rightarrow> ((x,y),s))"
definition "left_composition_map_back f' xy = (case xy of ((x,y),s) \<Rightarrow> (x, f' (y,s)))"

definition "right_composition_map f y = (case y of (y,r) \<Rightarrow> case f r of (x,s) \<Rightarrow> ((x,y),s))"
definition "right_composition_map_back f' xy = (case xy of ((x,y),s) \<Rightarrow> (y, f' (x,s)))"

inductive left_composition_f :: "('a,'b) lvaluex \<Rightarrow> ('a,'c) lvaluex \<Rightarrow> _" where
" valid_lvaluex x \<Longrightarrow> valid_lvaluex y \<Longrightarrow> compatible_lvaluex x y
  \<Longrightarrow> bij_betw f (lvaluex_representation_range x) (lvaluex_range y \<times> lvaluex_representation_range (compose_lvaluex x y))
  \<Longrightarrow> (\<And>z. left_composition_map f (lvaluex_representation x z) = (lvaluex_representation (compose_lvaluex x y) z))
  \<Longrightarrow> (f' = inv_into (lvaluex_representation_range x) f)
  \<Longrightarrow> left_composition_f x y f f'"


inductive right_composition_f :: "('a,'b) lvaluex \<Rightarrow> ('a,'c) lvaluex \<Rightarrow> _" where
" (* valid_lvaluex x \<Longrightarrow> valid_lvaluex y \<Longrightarrow> *) compatible_lvaluex x y
  \<Longrightarrow> bij_betw f (lvaluex_representation_range y) (lvaluex_range x \<times> lvaluex_representation_range (compose_lvaluex x y))
  \<Longrightarrow> (\<And>z. right_composition_map f (lvaluex_representation y z) = (lvaluex_representation (compose_lvaluex x y) z))
  \<Longrightarrow> (f' = inv_into (lvaluex_representation_range y) f)
  \<Longrightarrow> right_composition_f x y f f'"


lemma left_composition_f_inv_inj: 
  fixes x :: "('a,'b) lvaluex" and y :: "('a,'c) lvaluex"
  assumes left_composition_f: "left_composition_f x y f f'"
  defines "xy == compose_lvaluex x y"
  defines "Rx == lvaluex_representation x"
  defines "Rxy == lvaluex_representation xy"
  assumes z1_dom: "z1 \<in> lvaluex_domain x"
  assumes z2_dom: "z2 \<in> lvaluex_domain x"
  assumes Rxy_z1: "Rxy z1 = ((x1, y1), r1)"
  assumes Rxy_z2: "Rxy z2 = ((x2, y2), r2)"
  shows "f' (y1, r1) = f' (y2, r2) \<longleftrightarrow> (y1,r1) = (y2,r2)"

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

lemma left_composition_map_back:
  assumes left_composition_f: "left_composition_f x y f f'"
  defines "xy == compose_lvaluex x y"
  defines "Rx == lvaluex_representation x"
  defines "Rxy == lvaluex_representation xy"
  assumes z: "z \<in> lvaluex_domain x"
  shows "Rx z = left_composition_map_back f' (Rxy z)"

  
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
  fixes x y :: "'a lvalue_raw0"
  assumes compat: "compatible_lvalue_raw0 x y"
  shows "\<exists>f. 
    bij_betw f (lvalue_raw_representation_range0 x) (lvalue_range0 y \<times> lvaluex_representation_range (compose_lvalue_raw0' x y))
  \<and> (\<forall>z. left_composition_map f (lvalue_raw_representation0 x z) 
              = (lvaluex_representation (compose_lvalue_raw0' x y) z))"

lemma composed_lvalue_relationship_left:
  fixes x :: "('a,'b) lvaluex" and y :: "('a,'c) lvaluex"
  (* assumes "valid_lvaluex x" *)
  (* assumes "valid_lvaluex y" *)
  assumes compat: "compatible_lvaluex x y"
  (* defines "xy == compose_lvaluex x y" *)
  obtains f f' where "left_composition_f x y f f'"

lemma composed_lvalue_relationship_right:
  fixes x :: "('a,'b) lvaluex" and y :: "('a,'c) lvaluex"
  (* assumes "valid_lvaluex x" *)
  (* assumes "valid_lvaluex y" *)
  assumes "compatible_lvaluex x y"
  defines "xy == compose_lvaluex x y"
  obtains f f' where "right_composition_f x y f f'"
  sorry

typedef 'a matrix = "UNIV::('a\<Rightarrow>'a\<Rightarrow>complex) set" by simp
setup_lifting type_definition_matrix

(* definition "matrix_tensor (A::'a::times mat) (B::'a mat) =
  mat (dim_row A*dim_row B) (dim_col A*dim_col B) 
  (\<lambda>(r,c). A $$ (r div dim_row B, c div dim_col B) *
           B $$ (r mod dim_row B, c mod dim_col B))" *)

(* lemma dim_row_matrix_tensor: "dim_row (matrix_tensor M N) = dim_row M * dim_row N" sorr
lemma dim_col_matrix_tensor: "dim_col (matrix_tensor M N) = dim_col M * dim_col N" sorr *)

lift_definition tensor :: "'a::finite matrix \<Rightarrow> 'b::finite matrix \<Rightarrow> ('a*'b) matrix" is
  "%A B. \<lambda>(r1,r2) (c1,c2). A r1 c1 * B r2 c2" .

(*
consts value1 :: 'a
definition "value2 = (SOME x. x\<noteq>value1)"

definition "fst_subset = (SOME M::('a*'b)set. \<exists>f. bij_betw f (UNIV::'a set) M)"
definition "snd_subset = (SOME M::('a*'b)set. \<exists>f. bij_betw f (UNIV::'b set) M)"
definition "fst_iso = (SOME f::'a\<Rightarrow>'a*'b. bij_betw f (UNIV::'a set) fst_subset)"
definition "snd_iso = (SOME f::'b\<Rightarrow>'a*'b. bij_betw f (UNIV::'b set) snd_subset)"

term fst_iso

 (* TODO only workd is both 'a,'b have \<ge>2 elements *)
definition pair_factorization :: "('a*'b) lvalue_factorization" where
  "pair_factorization = \<lparr> domain=UNIV, index_set={value1,value2}, 
                          sets=(%i. if i=value1 then fst_subset else if i=value2 then snd_subset else undefined), 
                          isomorphism=(%x i. if i=value1 then fst_iso (fst x) else if i=value2 then snd_iso (snd x) else undefined) \<rparr>"

lemma assumes "card (UNIV::'a set) \<ge> 2" and "card (UNIV::'b set) \<ge> 2" 
  shows "valid_lvalue_factorization (pair_factorization::('a*'b) lvalue_factorization)"
  unfolding pair_factorization_def apply (rule valid_lvalue_factorization.intros)
     apply auto
  sorr

definition fst_lvalue :: "('a*'b, 'a) lvaluex" where
  "fst_lvalue = LValueX (LValue0 pair_factorization 
      (\<lambda>i. if i=value1 then LValueAll0 fst_subset id else LValueUnit0 snd_subset undefined)
      fst_subset (\<lambda>x. fst_iso (fst (x value1)))) (inv fst_iso)" *)

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
instance apply intro_classes sorry
end

axiomatization
  fst_lvalue :: "('a*'b, 'a) lvaluex" and
  snd_lvalue :: "('a*'b, 'b) lvaluex" where
  valid_fst_lvalue: "valid_lvaluex fst_lvalue" and
  valid_snd_lvalue: "valid_lvaluex snd_lvalue" and
  compatible_fst_snd: "compatible_lvaluex fst_lvalue snd_lvalue" and
  compatible_snd_fst: "compatible_lvaluex snd_lvalue fst_lvalue"

abbreviation "delta x y == (if x=y then 1 else 0)"

lift_definition matrix_on :: "'b::finite matrix \<Rightarrow> ('a,'b) lvaluex \<Rightarrow> 'a matrix" is
  "\<lambda>B lv (r::'a) (c::'a). B (fst (lvaluex_representation lv r)) (fst (lvaluex_representation lv c))
  * delta (snd (lvaluex_representation lv r)) (snd (lvaluex_representation lv c))".

lemma matrix_on_lift_left:
  assumes (* "valid_lvaluex x" and "valid_lvaluex y" and *) compat: "compatible_lvaluex x y"
  assumes domain[simp]: "lvaluex_domain x = UNIV"
  defines "xy == compose_lvaluex x y"
  shows "matrix_on A x = matrix_on (tensor A 1) xy"
proof (transfer fixing: x y xy, rule ext, rule ext)
  fix A :: "'b \<Rightarrow> 'b \<Rightarrow> complex" and r c
  define Rx where "Rx = lvaluex_representation x"
  define Rxy where "Rxy = lvaluex_representation xy"
  from composed_lvalue_relationship_left[OF compat]
  obtain f f' where f: "left_composition_f x y f f'"
    by auto
  have valid_xy: "valid_lvaluex xy"
    unfolding xy_def using compat by (rule valid_compose_lvaluex)
  note left_composition_f_inv_inj[OF f, folded xy_def Rxy_def, simp]
  have map: "Rx z = left_composition_map_back f' (Rxy z)" if "z \<in> lvaluex_domain x" for z
    unfolding Rx_def Rxy_def xy_def
    using f that by (rule left_composition_map_back)
  show "A (fst (Rx r)) (fst (Rx c)) * delta (snd (Rx r)) (snd (Rx c)) =
       (case fst (Rxy r) of (r1, r2) \<Rightarrow> \<lambda>(c1, c2). A r1 c1 * delta r2 c2)
        (fst (Rxy c)) * delta (snd (Rxy r)) (snd (Rxy c))"
    apply (subst map, simp)+
    apply (cases "Rxy r", cases "Rxy c") 
    unfolding left_composition_map_back_def
    by auto
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
  fixes x :: "('a::finite, 'b::finite) lvaluex"
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

end
