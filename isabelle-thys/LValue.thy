theory LValue
  imports Main "HOL-Library.Rewrite" (* "HOL-Cardinals.Cardinals" *)
    (* "Jordan_Normal_Form.Matrix_Impl" *) Complex_Main
    (* "HOL-Library.Indicator_Function" *)
begin

(* no_syntax "\<^const>Group.m_inv" :: "('a, 'b) monoid_scheme => 'a => 'a" ("inv\<index> _" [81] 80) *)

typedef 'a index = "UNIV::'a set" ..
(* typedef 'a target = "UNIV::'a set" .. *)

inductive_set dependent_functions' :: "'b \<Rightarrow> 'a set \<Rightarrow> ('a\<Rightarrow>'b set) \<Rightarrow> ('a\<Rightarrow>'b) set"
  for undef :: 'b and domain :: "'a set" and range :: "'a \<Rightarrow> 'b set" where
  "\<lbrakk> \<And>a. a\<notin>domain \<Longrightarrow> f a = undef;
     \<And>a. a\<in>domain \<Longrightarrow> f a \<in> range a \<rbrakk>
   \<Longrightarrow> f \<in> dependent_functions' undef domain range"

abbreviation "dependent_functions == dependent_functions' undefined" 

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
  domain :: "'a set"
  index_set :: "'a index set"
  sets :: "'a index \<Rightarrow> 'a set"
  isomorphism :: "'a \<Rightarrow> ('a index \<Rightarrow> 'a)"

inductive valid_lvalue_factorization :: "'a lvalue_factorization \<Rightarrow> bool" where
  "\<lbrakk> domain F \<noteq> {};
     \<And>i. i\<notin>index_set F \<Longrightarrow> sets F i = undefined;
     \<And>x. x\<notin>domain F \<Longrightarrow> isomorphism F x = undefined;
     bij_betw (isomorphism F) (domain F) (dependent_functions (index_set F) (sets F))
   \<rbrakk> \<Longrightarrow> valid_lvalue_factorization F"

datatype 'a lvalue_raw0 = 
    LValueAll0 "'a set" "'a=>'a"
  | LValueUnit0 "'a set" "'a"
  | LValue0 "'a lvalue_factorization" 
           "'a index \<Rightarrow> 'a lvalue_raw0"
           "'a set" (* range *)
           "('a index \<Rightarrow> 'a) \<Rightarrow> 'a"

datatype ('a,'b) lvaluex = LValueX (lvaluex_lvalue:"'a lvalue_raw0") (lvaluex_fun:"'a\<Rightarrow>'b")

datatype ('a,'b) lvalue_raw =
    LValueAll "'a set" "'a=>'b"
  | LValueUnit "'a set" "'b"
  | LValue (lvalue_factorization:"'a lvalue_factorization")
           (lvalue_lvalues:"'a index \<Rightarrow> 'a lvalue_raw0")
           "'b set" (* range *)
           (lvalue_repr:"('a index \<Rightarrow> 'a) \<Rightarrow> 'b")

fun of_lvalue0 where
  "of_lvalue0 (LValueUnit0 D r) = LValueUnit D r"
| "of_lvalue0 (LValueAll0 D f) = LValueAll D f"
| "of_lvalue0 (LValue0 F lvs rg repr) = LValue F lvs rg repr"

fun to_lvalue0 where
  "to_lvalue0 (LValueUnit D r) = LValueUnit0 D r"
| "to_lvalue0 (LValueAll D f) = LValueAll0 D f"
| "to_lvalue0 (LValue F lvs rg repr) = LValue0 F lvs rg repr"

lemma of_lvalue0_to_lvalue0[simp]: "of_lvalue0 (to_lvalue0 x) = x"
  apply (cases x) by auto

lemma to_lvalue0_of_lvalue0[simp]: "to_lvalue0 (of_lvalue0 x) = x"
  apply (cases x) by auto

fun lvalue_range where
  "lvalue_range (LValueAll d repr) = repr ` d"
| "lvalue_range (LValueUnit d r) = {r}"
| "lvalue_range (LValue F lvalues rg repr) = rg"

fun lvalue_range0 where
  "lvalue_range0 (LValueAll0 d repr) = repr ` d"
| "lvalue_range0 (LValueUnit0 d r) = {r}"
| "lvalue_range0 (LValue0 F lvalues rg repr) = rg"

fun lvaluex_range where
  "lvaluex_range (LValueX lv f) = f ` lvalue_range0 lv"

(* definition [simp]: "lvalue_range0 lv0 = lvalue_range (of_lvalue0 lv0)" *)

fun lvalue_domain where
  "lvalue_domain (LValueAll d repr) = d"
| "lvalue_domain (LValueUnit d _) = d"
| "lvalue_domain (LValue F lvalues rg repr) = domain F"

fun lvalue_domain0 where
  "lvalue_domain0 (LValueAll0 d repr) = d"
| "lvalue_domain0 (LValueUnit0 d _) = d"
| "lvalue_domain0 (LValue0 F lvalues rg repr) = domain F"

fun lvaluex_domain where
  "lvaluex_domain (LValueX lv _) = lvalue_domain0 lv"

(* definition [simp]: "lvalue_domain0 lv0 = lvalue_domain (of_lvalue0 lv0)" *)

inductive valid_lvalue_raw0 :: "'a lvalue_raw0 \<Rightarrow> bool" where
  valid_lvalue_raw0_all: "D \<noteq> {} \<Longrightarrow> inj_on repr D \<Longrightarrow> valid_lvalue_raw0 (LValueAll0 D repr)"
| valid_lvalue_raw0_unit: "D \<noteq> {} \<Longrightarrow> valid_lvalue_raw0 (LValueUnit0 D _)"
| valid_lvalue_raw0_mix: "\<lbrakk> 
     valid_lvalue_factorization F;
     \<And>i. i\<in>index_set F \<Longrightarrow> valid_lvalue_raw0 (lvalues i);
     \<And>i. i\<in>index_set F \<Longrightarrow> lvalue_domain0 ( (lvalues i)) = sets F i;
     bij_betw repr (dependent_functions (index_set F) (\<lambda>i. lvalue_range0 (lvalues i))) rg
   \<rbrakk> \<Longrightarrow> valid_lvalue_raw0 (LValue0 F lvalues rg repr)"

inductive valid_lvaluex where
  "valid_lvalue_raw0 lv \<Longrightarrow> inj_on f (lvalue_range0 lv) \<Longrightarrow> valid_lvaluex (LValueX lv f)"

(* inductive valid_lvalue_raw :: "('a,'b) lvalue_raw \<Rightarrow> bool" where
  "inj_on repr D \<Longrightarrow> valid_lvalue_raw (LValueAll D repr)"
| "valid_lvalue_raw (LValueUnit _ _)"
| "\<lbrakk> 
     valid_lvalue_factorization F;
     \<And>i. i\<in>index_set F \<Longrightarrow> valid_lvalue_raw0 (lvalues i);
     \<And>i. i\<in>index_set F \<Longrightarrow> lvalue_domain (of_lvalue0 (lvalues i)) = sets F i;
     bij_betw repr (dependent_functions (index_set F) (\<lambda>i. lvalue_range (of_lvalue0 (lvalues i)))) rg
   \<rbrakk> \<Longrightarrow> valid_lvalue_raw (LValue F lvalues rg repr)" *)

(* lemma to_lvalue0_subst: "(\<And>x. P (to_lvalue0 x)) \<Longrightarrow> P y"
  by (metis lvalue_raw0.exhaust to_lvalue0.simps(1) to_lvalue0.simps(2) to_lvalue0.simps(3)) *)
  
(* lemma valid_lvalue_raw_of_lvalue0: "valid_lvalue_raw (of_lvalue0 lv0) = valid_lvalue_raw0 lv0" 
  sorr *)
(* proof -
  have "valid_lvalue_raw0 (to_lvalue0 lv)" if "valid_lvalue_raw lv" for lv
    using that apply induction 
      apply auto
      apply (subst valid_lvalue_raw0.simps) apply simp
     apply (subst valid_lvalue_raw0.simps) sorr
    (* apply (subst valid_lvalue_raw0.simps) sorr *)
  note this[of "of_lvalue0 lv0", simplified]
  moreover have "valid_lvalue_raw (of_lvalue0 lv0)" if "valid_lvalue_raw0 lv0"
    using that apply induction sorr
  ultimately show ?thesis 
    by blast
qed *)

(* typedef ('a,'b) lvalue = "UNIV :: (('a,'b) lvalue_raw) set" ..
setup_lifting type_definition_lvalue *)

(* lift_definition valid_lvalue :: "('a,'b) lvalue \<Rightarrow> bool" is
 "\<lambda>lvalue::('a,'b) lvalue_raw. valid_lvalue_raw lvalue \<and> lvalue_domain lvalue = (UNIV::'a set)
     \<and> lvalue_range lvalue = (UNIV::'b set)" . *)

inductive compatible_lvalue_raw0 :: "'a lvalue_raw0 \<Rightarrow> 'a lvalue_raw0 \<Rightarrow> bool" where
  compatible_lvalue_raw0_unitleft: "lvalue_domain0 lv2 = D \<Longrightarrow> compatible_lvalue_raw0 (LValueUnit0 D _) lv2"
| compatible_lvalue_raw0_unitright: "lvalue_domain0 lv1 = D \<Longrightarrow> compatible_lvalue_raw0 lv1 (LValueUnit0 D _)"
| compatible_lvalue_raw0_merge:
  "\<lbrakk> valid_lvalue_raw0 (LValue0 F lvs1 rg1 repr1);
     valid_lvalue_raw0 (LValue0 F lvs2 rg2 repr2);
     \<And>i. i\<in>index_set F \<Longrightarrow> compatible_lvalue_raw0 (lvs1 i) (lvs2 i)
   \<rbrakk> \<Longrightarrow> compatible_lvalue_raw0 (LValue0 F lvs1 rg1 repr1) (LValue0 F lvs2 rg2 repr2)"

(* inductive compatible_lvalue_raw :: "('a,'b) lvalue_raw \<Rightarrow> ('a,'c) lvalue_raw \<Rightarrow> bool" where
  "lvalue_domain lv2 = D \<Longrightarrow> compatible_lvalue_raw (LValueUnit D _) lv2"
| "lvalue_domain lv1 = D \<Longrightarrow> compatible_lvalue_raw lv1 (LValueUnit D _)"
| "\<lbrakk> valid_lvalue_raw (LValue F lvs1 rg1 repr1);
     valid_lvalue_raw (LValue F lvs2 rg2 repr2);
     \<And>i. i\<in>index_set F \<Longrightarrow> compatible_lvalue_raw0 (lvs1 i) (lvs2 i)
   \<rbrakk> \<Longrightarrow> compatible_lvalue_raw (LValue F lvs1 rg1 repr1) (LValue F lvs2 rg2 repr2)" *)

inductive compatible_lvaluex where
  "compatible_lvalue_raw0 lv1 lv2 \<Longrightarrow> compatible_lvaluex (LValueX lv1 _) (LValueX lv2 _)"

(* lemma compatible_lvalue_raw_of_lvalue0: "compatible_lvalue_raw (of_lvalue0 lv0) (of_lvalue0 lv0') = compatible_lvalue_raw0 lv0 lv0'" 
proof -
  have "compatible_lvalue_raw0 (to_lvalue0 lv) (to_lvalue0 lv')" if "compatible_lvalue_raw lv lv'" for lv lv' :: "('a,'a) lvalue_raw"
    using that apply induction 
      apply auto
      apply (subst compatible_lvalue_raw0.simps) apply simp
      sorr
    
  note this[of "of_lvalue0 lv0" "of_lvalue0 lv0'", simplified]
  moreover have "compatible_lvalue_raw (of_lvalue0 lv0) (of_lvalue0 lv0')" if "compatible_lvalue_raw0 lv0 lv0'"
    using that apply induction
      apply (auto simp: compatible_lvalue_raw.simps)[2]
    (* by (metis compatible_lvalue_raw.intros(3) of_lvalue0.simps(3) valid_lvalue_raw_of_lvalue0) *)
    sorr
  ultimately show ?thesis 
    by blast
qed *)

(* lift_definition compatible_lvalue :: "('a,'b) lvalue \<Rightarrow> ('a,'c) lvalue \<Rightarrow> bool" is 
  "compatible_lvalue_raw :: ('a,'b) lvalue_raw \<Rightarrow> ('a,'c) lvalue_raw \<Rightarrow> bool" . *)

(* fun map_lvalue :: "('b\<Rightarrow>'c) \<Rightarrow> ('a,'b) lvalue_raw \<Rightarrow> ('a,'c) lvalue_raw" where
  "map_lvalue f (LValueUnit D r) = LValueUnit D (f r)"
| "map_lvalue f (LValueAll D repr) = LValueAll D (f o repr)"
| "map_lvalue f (LValue F lvs rg repr) = LValue F lvs (f ` rg) (f o repr)" *)

fun map_lvaluex where
  "map_lvaluex g (LValueX lv f) = LValueX lv (g o f)"

definition "lvalue_raw0_to_lvaluex lv = LValueX lv id"

lemma lvaluex_range_map[simp]: "lvaluex_range (map_lvaluex g lv) = g ` lvaluex_range lv"
  by (cases lv, hypsubst_thin, auto)
lemma lvaluex_domain_map[simp]: "lvaluex_domain (map_lvaluex g lv) = lvaluex_domain lv"
  by (cases lv, hypsubst_thin, auto)

inductive_set lvalue_raw0_termination_relation where
  "((lvs1 i), (LValue0 F1 lvs1 rg1 repr1)) \<in> lvalue_raw0_termination_relation"
lemma wf_lvalue_raw0_termination_relation: "wf lvalue_raw0_termination_relation"
proof (rule wfUNIVI, rename_tac P l)
  fix P :: "'a lvalue_raw0 \<Rightarrow> bool" and l
  assume IH: "\<forall>x. (\<forall>y. (y, x) \<in> lvalue_raw0_termination_relation \<longrightarrow> P y) \<longrightarrow> P x"
  show "P l"
    apply (rule IH[rule_format], rename_tac l')
    (* apply (case_tac pred, hypsubst_thin, rename_tac l1' l2') *)
  proof (induction l)
    case LValueAll0
    then show ?case
      by (simp add: lvalue_raw0_termination_relation.simps)
  next
    case LValueUnit0
    then show ?case
      by (simp add: lvalue_raw0_termination_relation.simps)
  next
    case (LValue0 F lvs rg repr) then show ?case
      by (metis IH lvalue_raw0.inject(3) lvalue_raw0_termination_relation.simps rangeI)
  qed
qed

definition relation_prod where 
  "relation_prod R S = {((x,y),(x',y')). (x,x') \<in> R \<and> (y,y') \<in> S}"

lemma wf_relation_prod: "wf R \<Longrightarrow> wf (relation_prod R S)"
  unfolding wf_def relation_prod_def  
  apply (rule allI)
  apply (rule impI)
  apply (simp only: split_paired_All)
  apply (drule spec)
  apply (erule mp)
  by simp

(* function (sequential) compose_lvalue_raw0 :: "'a lvalue_raw0 \<Rightarrow> 'a lvalue_raw0 \<Rightarrow> ('a,'a\<times>'a) lvalue_raw" where
  "compose_lvalue_raw0 (LValueUnit0 _ r) lv2 = map_lvalue (\<lambda>x2. (r,x2)) (of_lvalue0 lv2)"
| "compose_lvalue_raw0 lv1 (LValueUnit0 _ r) = map_lvalue (\<lambda>x1. (x1,r)) (of_lvalue0 lv1)"
| "compose_lvalue_raw0 (LValueAll0 _ _) _ = undefined" (* cannot be compatible *)
| "compose_lvalue_raw0 _ (LValueAll0 _ _) = undefined" (* cannot be compatible *)
| "compose_lvalue_raw0 (LValue0 F1 lvs1 rg1 repr1) (LValue0 F2 lvs2 rg2 repr2) = 
    (let f = \<lambda>i. SOME f. inj_on f (lvalue_range0 (lvs1 i) \<times> lvalue_range0 (lvs2 i)) in
     let f' = \<lambda>all. let all1 = \<lambda>i. fst (inv (f i) (all i)); all2 = \<lambda>i. snd (inv (f i) (all i)) in (repr1 all1, repr2 all2) in
    LValue F1 (\<lambda>i. to_lvalue0 (map_lvalue (f i) (compose_lvalue_raw0 (lvs1 i) (lvs2 i)))) (rg1\<times>rg2) f')"
  by pat_completeness auto
termination 
  apply (relation "relation_prod lvalue_raw0_termination_relation UNIV")
   apply (rule wf_relation_prod)
   apply (fact wf_lvalue_raw0_termination_relation)
  by (auto simp: relation_prod_def lvalue_raw0_termination_relation.simps) *)

(* find_consts "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)"  *)
(* find_theorems "(fst o ?f, snd o ?f)" *)

function (sequential) compose_lvalue_raw0' :: "'a lvalue_raw0 \<Rightarrow> 'a lvalue_raw0 \<Rightarrow> ('a,'a\<times>'a) lvaluex" where
  "compose_lvalue_raw0' (LValueUnit0 _ r) lv2 = LValueX lv2 (\<lambda>x2. (r,x2))"
| "compose_lvalue_raw0' lv1 (LValueUnit0 _ r) = LValueX lv1 (\<lambda>x1. (x1,r))"
| "compose_lvalue_raw0' (LValueAll0 _ _) _ = undefined" (* cannot be compatible *)
| "compose_lvalue_raw0' _ (LValueAll0 _ _) = undefined" (* cannot be compatible *)
| "compose_lvalue_raw0' (LValue0 F1 lvs1 rg1 repr1) (LValue0 F2 lvs2 rg2 repr2) = 
    (let lvs' :: 'a index \<Rightarrow> ('a,'a\<times>'a) lvaluex = \<lambda>i. compose_lvalue_raw0' (lvs1 i) (lvs2 i);
           \<comment> \<open>\<open>lvs' i\<close> is the composition of \<open>lvs1 i\<close>, \<open>lvs2 i\<close>\<close>
         lvs'' :: 'a index \<Rightarrow> 'a lvalue_raw0 = \<lambda>i. lvaluex_lvalue (lvs' i);
         depfuns = (dependent_functions (index_set F1) (\<lambda>i. lvalue_range0 (lvs'' i)));
         f'' :: 'a index\<Rightarrow>'a\<Rightarrow>'a\<times>'a = \<lambda>i. if i\<in>index_set F1 then lvaluex_fun (lvs' i) else (\<lambda>_. undefined);
           \<comment> \<open>f'' o lvs'' = lvs', componentwise\<close>
         repr' :: ('a index\<Rightarrow>'a) \<Rightarrow> 'a = SOME repr'. inj_on repr' depfuns;
           \<comment> \<open>an arbitrary representation\<close>
         rg' :: 'a set = repr' ` depfuns;
         lvs0 :: 'a lvalue_raw0 = LValue0 F1 lvs'' rg' repr';
           \<comment> \<open>An lvalue that is already the composition, except that we don't have the right representation\<close>
         fun :: 'a\<Rightarrow>'a*'a = (map_prod repr1 repr2) o (dependent_functions_split (index_set F1)) 
                              o (\<lambda>g i. (f'' i) (g i)) o (inv_into depfuns repr')
           \<comment> \<open>getting the right value out of lvs0: first apply \<open>inv repr'\<close> to get the dependent function,
               then pointwise apply f'' to get the outputs of lvs',
               then split into two functions
               then apply repr1,repr2 to get the outputs of lvs1,lvs2\<close>
    in
    LValueX lvs0 fun)"
  by pat_completeness auto
termination 
  apply (relation "relation_prod lvalue_raw0_termination_relation UNIV")
   apply (rule wf_relation_prod)
   apply (fact wf_lvalue_raw0_termination_relation)
  by (auto simp: relation_prod_def lvalue_raw0_termination_relation.simps)

fun compose_lvaluex where
  "compose_lvaluex (LValueX lv1 f1) (LValueX lv2 f2) = map_lvaluex (map_prod f1 f2) (compose_lvalue_raw0' lv1 lv2)"

(* TODO: remove *)
(* fun compose_lvalue_raw :: "('a,'b) lvalue_raw \<Rightarrow> ('a,'c) lvalue_raw \<Rightarrow> ('a,'b\<times>'c) lvalue_raw" where
  "compose_lvalue_raw (LValueUnit _ r) lv2 = map_lvalue (\<lambda>x2. (r,x2)) (lv2)"
| "compose_lvalue_raw lv1 (LValueUnit _ r) = map_lvalue (\<lambda>x1. (x1,r)) (lv1)"
| "compose_lvalue_raw (LValueAll _ _) _ = undefined" (* cannot be compatible *)
| "compose_lvalue_raw _ (LValueAll _ _) = undefined" (* cannot be compatible *)
| "compose_lvalue_raw (LValue F1 lvs1 rg1 repr1) (LValue F2 lvs2 rg2 repr2) = 
    (let f = \<lambda>i. SOME f. inj_on f (lvalue_range0 (lvs1 i) \<times> lvalue_range0 (lvs2 i)) in
     let f' = \<lambda>all. let all1 = \<lambda>i. fst (inv (f i) (all i)); all2 = \<lambda>i. snd (inv (f i) (all i)) in (repr1 all1, repr2 all2) in
    LValue F1 (\<lambda>i. to_lvalue0 (map_lvalue (f i) (compose_lvalue_raw0 (lvs1 i) (lvs2 i)))) (rg1\<times>rg2) f')" *)

lemma lvaluex_domain_compose_lvalue_raw0':
  assumes valid1: "valid_lvalue_raw0 lv1"
  assumes valid2: "valid_lvalue_raw0 lv2"
  assumes compat: "compatible_lvalue_raw0 lv1 lv2"
  shows "lvaluex_domain (compose_lvalue_raw0' lv1 lv2) = lvalue_domain0 lv1" (is ?thesis1)
    and "lvaluex_domain (compose_lvalue_raw0' lv1 lv2) = lvalue_domain0 lv2" (is ?thesis2)
proof -
  show ?thesis1
    using compat proof cases
    case (compatible_lvalue_raw0_unitleft D uu)
    then show ?thesis by simp
  next
    case (compatible_lvalue_raw0_unitright D uv)
    then show ?thesis
      apply (cases lv1) by simp_all
  next
    case (compatible_lvalue_raw0_merge F lvs1 rg1 repr1 lvs2 rg2 repr2)
    show ?thesis
      unfolding compatible_lvalue_raw0_merge by (simp add: Let_def)
  qed
  show ?thesis2
    using compat proof cases
    case (compatible_lvalue_raw0_unitleft D uu)
    then show ?thesis by simp
  next
    case (compatible_lvalue_raw0_unitright D uv)
    then show ?thesis
      apply (cases lv1) by simp_all
  next
    case (compatible_lvalue_raw0_merge F lvs1 rg1 repr1 lvs2 rg2 repr2)
    show ?thesis
      unfolding compatible_lvalue_raw0_merge by (simp add: Let_def)
  qed
qed

lemma conj_to_conjunctionI: "A \<and> B \<Longrightarrow> (A &&& B)"
  by presburger

lemma lvalue_range0_leq_domain0:
  assumes "valid_lvalue_raw0 lv"
  shows "leq_card (lvalue_range0 lv) (lvalue_domain0 lv)"
  using assms proof induction
  case (valid_lvalue_raw0_all repr D)
  then show ?case
    using inj_on_the_inv_into the_inv_into_onto by (fastforce simp: leq_card_def)
next
  case (valid_lvalue_raw0_unit D uu)
  then show ?case 
    using inj_on_the_inv_into the_inv_into_onto by (fastforce simp: leq_card_def)
next
  case (valid_lvalue_raw0_mix F lvalues repr rg)
  from valid_lvalue_raw0_mix
  have "leq_card rg (dependent_functions (index_set F) (\<lambda>i. lvalue_range0 (lvalues i)))"
    unfolding leq_card_def
    by (metis bij_betw_imp_inj_on bij_betw_imp_surj_on bij_betw_the_inv_into equalityD1)
  also 
  have "leq_card \<dots> (dependent_functions (index_set F) (\<lambda>i. lvalue_domain0 (lvalues i)))"
    apply (rule dependent_functions_mono)
    by (rule valid_lvalue_raw0_mix.IH)
  also
  have "leq_card \<dots> (dependent_functions (index_set F) (sets F))"
    apply (rule dependent_functions_mono)
    using valid_lvalue_raw0_mix by auto
  also
  from \<open>valid_lvalue_factorization F\<close> 
  have "leq_card \<dots> (domain F)"
    apply cases unfolding leq_card_def
    by (metis bij_betw_imp_inj_on bij_betw_imp_surj_on bij_betw_the_inv_into equalityD1)
  finally
  have "leq_card rg (domain F)".
  then show ?case
    unfolding valid_lvalue_raw0_mix by simp
qed

lemma
  assumes "valid_lvalue_raw0 lv1"
  assumes "valid_lvalue_raw0 lv2"
  assumes compat: "compatible_lvalue_raw0 lv1 lv2"
  shows valid_compose_lvalue_raw0': "valid_lvaluex (compose_lvalue_raw0' lv1 lv2)" 
    and range_compose_lvalue_raw0': "lvaluex_range (compose_lvalue_raw0' lv1 lv2) = lvalue_range0 lv1 \<times> lvalue_range0 lv2"
  using compat assms(1-2) 
   (* apply induction
   apply (rule conj_to_conjunctionI)  find_theorems "?A \<and> ?B \<Longrightarrow> (?A &&& ?B)"
  apply (insert assms(1-2)) using compat *)
proof induction
  case (compatible_lvalue_raw0_unitleft lv2 D uu) case 1
  then show ?case
    by (auto intro!: inj_onI valid_lvaluex.intros)
next
  case (compatible_lvalue_raw0_unitleft lv2 D uu) case 2
  with compatible_lvalue_raw0_unitleft show ?case
    by auto
next
  case (compatible_lvalue_raw0_unitright lv1 D uv) case 1
  with compatible_lvalue_raw0_unitright show ?case
    apply (cases lv1)
    by (auto intro!: inj_onI valid_lvaluex.intros)
next
  case (compatible_lvalue_raw0_unitright lv1 D uv) case 2
  show ?case
    apply (cases lv1) by auto
(* next
  case (compatible_lvalue_raw0_merge F lvs1 rg1 repr1 lvs2 rg2 repr2) case 2
  with compatible_lvalue_raw0_merge show ?case
    *)
next
  case (compatible_lvalue_raw0_merge F lvs1 rg1 repr1 lvs2 rg2 repr2) 
  case 1 let ?case1 = ?case
  case 2 let ?case2 = ?case

  define lvs' lvs'' depfuns  f'' repr' rg' lvs0 "fun" composed depfuns' depfuns1 depfuns2 where
    "lvs' = (\<lambda>i. compose_lvalue_raw0' (lvs1 i) (lvs2 i))" and
    "lvs'' = (\<lambda>i. lvaluex_lvalue (lvs' i))" and
    "depfuns = (dependent_functions (index_set F) (\<lambda>i. lvalue_range0 (lvs'' i)))" and
    "f'' = (\<lambda>i. if i\<in>index_set F then lvaluex_fun (lvs' i) else (\<lambda>_. undefined))" and
    "repr' = (SOME repr'. inj_on repr' depfuns)" and
    "rg' = repr' ` depfuns" and
    "lvs0 = LValue0 F lvs'' rg' repr'" and
    "fun  = (map_prod repr1 repr2) o (dependent_functions_split (index_set F)) o (\<lambda>g i. (f'' i) (g i)) o (inv_into depfuns repr')" and
    "composed = LValueX lvs0 fun" and
    "depfuns' = (dependent_functions (index_set F) (\<lambda>i. lvaluex_range (lvs' i)))" and
    "depfuns1 = (dependent_functions (index_set F) (\<lambda>i. lvalue_range0 (lvs1 i)))" and
    "depfuns2 = (dependent_functions (index_set F) (\<lambda>i. lvalue_range0 (lvs2 i)))"
  note defs = this

  have composed: "composed = compose_lvalue_raw0' (LValue0 F lvs1 rg1 repr1) (LValue0 F lvs2 rg2 repr2)"
    unfolding defs by (simp add: Let_def)

  have valid_F: "valid_lvalue_factorization F"
    using 1(1) valid_lvalue_raw0.simps by fastforce

  from 1(1)
  have domain1: "lvalue_domain0 (lvs1 i) = sets F i" if "i \<in> index_set F" for i
    by (cases, simp add: that)
  from 1(1)
  have valid1: "valid_lvalue_raw0 (lvs1 i)" if "i \<in> index_set F" for i
    by (cases, simp add: that)
  from 1(2)
  have valid2: "valid_lvalue_raw0 (lvs2 i)" if "i \<in> index_set F" for i
    by (cases, simp add: that)
  have "valid_lvaluex (compose_lvalue_raw0' (lvs1 i) (lvs2 i))" if "i \<in> index_set F" for i
    apply (rule compatible_lvalue_raw0_merge.IH)
    using that valid1 valid2 by auto
  then have valid_lvs': "valid_lvaluex (lvs' i)" if "i \<in> index_set F" for i
    using that by (simp add: lvs'_def)
  then have valid_lvs'': "valid_lvalue_raw0 (lvs'' i)" if "i \<in> index_set F" for i
    using that lvs''_def by (metis lvaluex.sel(1) valid_lvaluex.simps)
  have "lvaluex_domain (lvs' i) = lvalue_domain0 (lvs1 i)" if "i \<in> index_set F" for i
    unfolding lvs'_def
    using valid1 valid2 apply (rule lvaluex_domain_compose_lvalue_raw0')
    apply (fact that)+
    using that by (rule compatible_lvalue_raw0_merge.hyps)
  with domain1
  have "lvaluex_domain (lvs' i) = sets F i" if "i \<in> index_set F" for i
    using that by simp
  then have domain_lvs'': "lvalue_domain0 (lvs'' i) = sets F i" if "i \<in> index_set F" for i
    unfolding lvs''_def
    using that by (metis lvaluex.exhaust_sel lvaluex_domain.simps) 

  have inj_repr': "inj_on repr' depfuns" (is "?P repr'")
    unfolding repr'_def
  proof (rule someI_ex[of ?P])
    have "leq_card depfuns (dependent_functions (index_set F) (\<lambda>i. lvalue_domain0 (lvs'' i)))"
      unfolding depfuns_def apply (rule dependent_functions_mono)
      apply (rule lvalue_range0_leq_domain0)
      by (rule valid_lvs'')
    also have "leq_card \<dots> (dependent_functions (index_set F) (sets F))"
      apply (rule dependent_functions_mono)
      apply (subst domain_lvs'')
      by auto
    also have "leq_card \<dots> (domain F)"
      using valid_F apply cases
      by (metis bij_betw_imp_inj_on bij_betw_imp_surj_on bij_betw_the_inv_into leq_card_def subset_eq)
    also have "leq_card \<dots> (UNIV::'a set)"
      unfolding leq_card_def 
      using inj_on_id2 by blast
    finally show "\<exists>f::_\<Rightarrow>'a. inj_on f depfuns"
      unfolding leq_card_def by auto 
  qed
  then have bij_repr': "bij_betw repr' depfuns rg'"
    unfolding rg'_def
    by (simp add: bij_betw_imageI)

  have valid_lvs0: "valid_lvalue_raw0 lvs0" 
    unfolding lvs0_def 
    using valid_F valid_lvs'' domain_lvs'' bij_repr' unfolding depfuns_def 
    by (rule valid_lvalue_raw0.intros)

  have bij_fun: "bij_betw fun (lvalue_range0 lvs0) (rg1 \<times> rg2)"
  proof -
(*     have inj_comp: "bij_betw f A B \<Longrightarrow> inj_on g B \<Longrightarrow> inj_on (g o f) A" for g::"'bb\<Rightarrow>'cc" and f::"'aa\<Rightarrow>'bb" and A B
      by (simp add: bij_betw_def comp_inj_on) *)
(*     have bij_comp: "bij_betw f A B \<Longrightarrow> bij_betw g B C \<Longrightarrow> bij_betw (g o f) A C" for g::"'bb\<Rightarrow>'cc" and f::"'aa\<Rightarrow>'bb" and A B C
      by (simp add: bij_betw_trans) *)

    have "bij_betw (inv_into depfuns repr') (lvalue_range0 lvs0) depfuns"
      apply (rule bij_betw_inv_into)
      using bij_repr' unfolding lvs0_def by simp 
    moreover
    have inj_f'': "inj_on (f'' i) (lvalue_range0 (lvs'' i))" if "i\<in>index_set F" for i
      using valid_lvs'[OF that] apply cases
      unfolding f''_def lvs''_def by (simp add: that)
    have bij_f'': "bij_betw (f'' i) (lvalue_range0 (lvs'' i)) (lvaluex_range (lvs' i))" if "i\<in>index_set F" for i
      apply (rewrite at "lvaluex_range _" DEADID.rel_mono_strong[where y="f'' i ` (lvalue_range0 (lvs'' i))"])
       using that apply (metis f''_def lvaluex.exhaust_sel lvaluex_range.simps lvs''_def)
      using inj_f'' that by (simp add: bij_betw_imageI)
    have "bij_betw (\<lambda>g i. f'' i (g i)) depfuns depfuns'"
      unfolding depfuns_def depfuns'_def 
      apply (rule bij_betw_dependent_functions)
       apply (rule bij_f'', assumption)
      unfolding f''_def by simp
    moreover
    have lvs'_range: "lvaluex_range (lvs' i) = lvalue_range0 (lvs1 i) \<times> lvalue_range0 (lvs2 i)" if "i \<in> index_set F" for i
      unfolding lvs'_def 
      using that valid1[OF that] valid2[OF that]
      by (rule compatible_lvalue_raw0_merge)
    have "bij_betw (dependent_functions_split (index_set F)) depfuns' (depfuns1 \<times> depfuns2)"
      unfolding depfuns'_def depfuns1_def depfuns2_def
      apply (rule bij_betw_dependent_functions_split)
      using lvs'_range by simp
    moreover
    have bij_repr1: "bij_betw repr1 depfuns1 rg1"
      and bij_repr2: "bij_betw repr2 depfuns2 rg2"
      unfolding depfuns1_def depfuns2_def
      using 1 valid_lvalue_raw0.simps by fastforce+
(*     then have inj_repr1: "inj_on repr1 (dependent_functions (index_set F) (\<lambda>i. lvalue_range0 (lvs1 i)))"
      and inj_repr2: "inj_on repr2 (dependent_functions (index_set F) (\<lambda>i. lvalue_range0 (lvs2 i)))"
      using bij_betw_imp_inj_on depfuns1_def depfuns2_def by auto *)
    then have "bij_betw (map_prod repr1 repr2) (depfuns1 \<times> depfuns2) (rg1 \<times> rg2)"
      by (rule bij_betw_map_prod)
    ultimately
    show ?thesis
      unfolding fun_def
      by (auto intro!: bij_betw_trans)
  qed
  then have inj_fun: "inj_on fun (lvalue_range0 lvs0)"
    using bij_betw_imp_inj_on by blast

  show ?case1
    unfolding composed[symmetric] composed_def
    using valid_lvs0 inj_fun by (rule valid_lvaluex.intros)

  from bij_fun
  have "lvaluex_range composed = rg1 \<times> rg2"
    by (simp add: bij_betw_imp_surj_on composed_def)
  then show ?case2
    by (simp only: composed lvalue_range0.simps)
qed

lemma valid_map_lvaluex:
  assumes "valid_lvaluex lv"
  assumes "inj_on g (lvaluex_range lv)"
  shows "valid_lvaluex (map_lvaluex g lv)"
  using assms apply cases by (auto simp: comp_inj_on_iff intro!: valid_lvaluex.intros)

lemma valid_compose_lvaluex:
  assumes valid_lv1: "valid_lvaluex lv1"
  assumes valid_lv2: "valid_lvaluex lv2"
  assumes compat: "compatible_lvaluex lv1 lv2"
  shows "valid_lvaluex (compose_lvaluex lv1 lv2)" 
  apply (cases lv1, cases lv2, simp)
  apply (rule valid_map_lvaluex)
   apply (metis compat compatible_lvaluex.simps lvaluex.sel(1) valid_compose_lvalue_raw0' valid_lv1 valid_lv2 valid_lvaluex.simps)
  by (metis compat compatible_lvaluex.simps lvaluex.inject map_prod_inj_on range_compose_lvalue_raw0' valid_lv1 valid_lv2 valid_lvaluex.simps)

lemma lvalue_induct:
  assumes all: "\<And>D repr. P (LValueAll0 D repr)"
  assumes unit: "\<And>D r. P (LValueUnit0 D r)"
  assumes mix: "\<And>F lvs rg repr. (\<And>i. P (lvs i)) \<Longrightarrow> P (LValue0 F lvs rg repr)"
  shows "P lv"
proof (induction rule: wf_induct_rule[OF wf_lvalue_raw0_termination_relation])
  case (1 lv)
  then show "P lv"
  proof (cases lv)
    case (LValueAll0 x11 x12)
    then show ?thesis
      apply simp by (rule all)
  next
    case (LValueUnit0 x21 x22)
    then show ?thesis
      apply simp by (rule unit)
  next
    case (LValue0 F lvs rg repr)
    then show ?thesis
      apply simp
      apply (rule mix)
      apply (rule 1)
      by (auto intro: lvalue_raw0_termination_relation.intros)
  qed
qed

lemma range_compose_lvaluex:
  assumes valid_x: "valid_lvaluex x"
  assumes valid_y: "valid_lvaluex y"
  assumes compat: "compatible_lvaluex x y"
  shows "lvaluex_range (compose_lvaluex x y) = lvaluex_range x \<times> lvaluex_range y"
proof -
  obtain xlv xf where x: "x = LValueX xlv xf"
    using lvaluex.exhaust_sel by blast
  obtain ylv yf where y: "y = LValueX ylv yf"
    using lvaluex.exhaust_sel by blast
  from valid_x have valid_xlv: "valid_lvalue_raw0 xlv" 
    unfolding x apply cases by simp
  from valid_y have valid_ylv: "valid_lvalue_raw0 ylv" 
    unfolding y apply cases by simp
  from compat have compat0: "compatible_lvalue_raw0 xlv ylv" 
    unfolding x y apply cases by simp

  show ?thesis
    by (simp add: x y map_prod_surj_on range_compose_lvalue_raw0'[OF valid_xlv valid_ylv compat0])
qed

lemma domain_compose_lvaluex:
  assumes valid_x: "valid_lvaluex x"
  assumes valid_y: "valid_lvaluex y"
  assumes compat: "compatible_lvaluex x y"
  shows "lvaluex_domain (compose_lvaluex x y) = lvaluex_domain x" (is ?thesis1)
    and "lvaluex_domain (compose_lvaluex x y) = lvaluex_domain y" (is ?thesis2)
proof -
  obtain xlv xf where x: "x = LValueX xlv xf"
    using lvaluex.exhaust_sel by blast
  obtain ylv yf where y: "y = LValueX ylv yf"
    using lvaluex.exhaust_sel by blast
  from valid_x have valid_xlv: "valid_lvalue_raw0 xlv" 
    unfolding x apply cases by simp
  from valid_y have valid_ylv: "valid_lvalue_raw0 ylv" 
    unfolding y apply cases by simp
  from compat have compat0: "compatible_lvalue_raw0 xlv ylv" 
    unfolding x y apply cases by simp
  show ?thesis1
    by (simp add: x y map_prod_surj_on lvaluex_domain_compose_lvalue_raw0'(1)[OF valid_xlv valid_ylv compat0])
  show ?thesis2
    by (simp add: x y map_prod_surj_on lvaluex_domain_compose_lvalue_raw0'(2)[OF valid_xlv valid_ylv compat0])
qed

lemma compatible_compose_lvalue_raw0':
  assumes "valid_lvalue_raw0 lv1"
  assumes "valid_lvalue_raw0 lv2"
  assumes "valid_lvalue_raw0 lv3"
  assumes compat: "compatible_lvalue_raw0 lv1 lv2"
  assumes "compatible_lvalue_raw0 lv1 lv3"
  assumes "compatible_lvalue_raw0 lv2 lv3"
  shows "compatible_lvalue_raw0 (lvaluex_lvalue (compose_lvalue_raw0' lv1 lv2)) lv3"
  using compat assms
proof (induction arbitrary: lv3)
  case compatible_lvalue_raw0_unitleft
  then show ?case
    by simp
next
  case (compatible_lvalue_raw0_unitright lv1)
  then show ?case
    apply (cases lv1)
    by auto
next
  case (compatible_lvalue_raw0_merge F lvs1 rg1 repr1 lvs2 rg2 repr2)
  define D compose12 where "D = lvalue_domain0 (LValue0 F lvs1 rg1 repr1)"
        and "compose12 = compose_lvalue_raw0' (LValue0 F lvs1 rg1 repr1) (LValue0 F lvs2 rg2 repr2)"
  have D_compose12: "D = lvaluex_domain compose12"
    unfolding D_def compose12_def
    apply (rule lvaluex_domain_compose_lvalue_raw0'[symmetric])
    by (fact compatible_lvalue_raw0_merge.prems)+

  from compatible_lvalue_raw0_merge have "compatible_lvalue_raw0 (LValue0 F lvs1 rg1 repr1) lv3" by simp
  then consider (lv3_unit) r3 where "lv3 = LValueUnit0 D r3" | (lv3_mix) lvs3 rg3 repr3 where "lv3 = LValue0 F lvs3 rg3 repr3" 
    apply cases unfolding D_def by auto
  then show "compatible_lvalue_raw0 (lvaluex_lvalue compose12) lv3"
  proof cases
    case lv3_unit
    show ?thesis unfolding lv3_unit
      apply (rule compatible_lvalue_raw0_unitright)
      unfolding D_compose12
      by (metis lvaluex.exhaust_sel lvaluex_domain.simps)
  next
    case lv3_mix
    define lvs' lvs'' depfuns  f'' repr' rg' lvs0 "fun" lv1 lv2 where
      "lvs' = (\<lambda>i. compose_lvalue_raw0' (lvs1 i) (lvs2 i))" and
      "lvs'' = (\<lambda>i. lvaluex_lvalue (lvs' i))" and
      "depfuns = (dependent_functions (index_set F) (\<lambda>i. lvalue_range0 (lvs'' i)))" and
      "f'' = (\<lambda>i. if i\<in>index_set F then lvaluex_fun (lvs' i) else (\<lambda>_. undefined))" and
      "repr' = (SOME repr'. inj_on repr' depfuns)" and
      "rg' = repr' ` depfuns" and
      "lvs0 = LValue0 F lvs'' rg' repr'" and
      "fun  = (map_prod repr1 repr2) o (dependent_functions_split (index_set F)) o (\<lambda>g i. (f'' i) (g i)) o (inv_into depfuns repr')" and
      "lv1 = (LValue0 F lvs1 rg1 repr1)" and
      "lv2 = (LValue0 F lvs2 rg2 repr2)"
    note defs = this

    have compose12: "compose12 = LValueX lvs0 fun"
      unfolding compose12_def defs by (simp add: Let_def)

    from compatible_lvalue_raw0_merge
    have valid1: "valid_lvalue_raw0 lv1"
      and valid2: "valid_lvalue_raw0 lv2"
      and valid3: "valid_lvalue_raw0 lv3"
      and compat12: "compatible_lvalue_raw0 lv1 lv2"
      and compat13: "compatible_lvalue_raw0 lv1 lv3"
      and compat23: "compatible_lvalue_raw0 lv2 lv3"
      unfolding lv1_def lv2_def by simp_all
  
    have valid12: "valid_lvaluex compose12"
      unfolding compose12_def
      using valid1 valid2 compat12 unfolding lv1_def lv2_def by (rule valid_compose_lvalue_raw0')
    then have valid0: "valid_lvalue_raw0 lvs0"
      unfolding compose12 apply cases by simp
    from valid1 have valid1s: "valid_lvalue_raw0 (lvs1 i)" if "i \<in> index_set F" for i
      unfolding lv1_def apply cases using that by simp
    from valid2 have valid2s: "valid_lvalue_raw0 (lvs2 i)" if "i \<in> index_set F" for i
      unfolding lv2_def apply cases using that by simp
    from valid3 have valid3s: "valid_lvalue_raw0 (lvs3 i)" if "i \<in> index_set F" for i
      unfolding lv3_mix apply cases using that by simp
    from compat12 have compat12s: "compatible_lvalue_raw0 (lvs1 i) (lvs2 i)" if "i \<in> index_set F" for i
      unfolding lv1_def lv2_def apply cases using that by simp
    from compat13 have compat13s: "compatible_lvalue_raw0 (lvs1 i) (lvs3 i)" if "i \<in> index_set F" for i
      unfolding lv1_def lv3_mix apply cases using that by simp
    from compat23 have compat23s: "compatible_lvalue_raw0 (lvs2 i) (lvs3 i)" if "i \<in> index_set F" for i
      unfolding lv2_def lv3_mix apply cases using that by simp

    have compat''3: "compatible_lvalue_raw0 (lvs'' i) (lvs3 i)" if "i \<in> index_set F" for i
      unfolding lvs''_def lvs'_def
      using that valid1s valid2s valid3s compat12s compat13s compat23s
      apply (rule compatible_lvalue_raw0_merge.IH)
      by (fact that)+
    have "compatible_lvalue_raw0 lvs0 lv3"
      using valid0 valid3 compat''3
      unfolding lv3_mix lvs0_def 
      by (rule compatible_lvalue_raw0.intros)
    then show ?thesis
      by (metis compose12 lvaluex.sel(1))
  qed
qed

function lvalue_raw_representation_range0 :: "'a lvalue_raw0 \<Rightarrow> 'a set" where
  "lvalue_raw_representation_range0 (LValueUnit0 D r) = D"
| "lvalue_raw_representation_range0 (LValueAll0 D repr) = {undefined}"
| "lvalue_raw_representation_range0 (LValue0 F lvs rg repr) = 
    (let leftover_f = SOME f. inj_on f (dependent_functions (index_set F) (\<lambda>i. lvalue_raw_representation_range0 (lvs i)))
     in leftover_f ` (dependent_functions (index_set F) (\<lambda>i. lvalue_raw_representation_range0 (lvs i))))"
  by pat_completeness auto
termination 
  apply (relation "lvalue_raw0_termination_relation")
   apply (fact wf_lvalue_raw0_termination_relation)
  by (auto simp: lvalue_raw0_termination_relation.simps)

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
  by pat_completeness auto
termination 
  apply (relation "relation_prod lvalue_raw0_termination_relation UNIV")
   apply (rule wf_relation_prod)
   apply (fact wf_lvalue_raw0_termination_relation)
  by (auto simp: relation_prod_def lvalue_raw0_termination_relation.simps)

(* TODO: definition that interprets an ('a,'b) lvalue as a bijection domain \<rightarrow> range * something *)

definition lvaluex_representation :: "('a,'b) lvaluex \<Rightarrow> 'a \<Rightarrow> 'b\<times>'a" where
  "lvaluex_representation lv x = apfst (lvaluex_fun lv) (lvalue_raw_representation0 (lvaluex_lvalue lv) x)"

definition lvaluex_representation_range :: "('a,'b) lvaluex \<Rightarrow> 'a set" where
  "lvaluex_representation_range lv = lvalue_raw_representation_range0 (lvaluex_lvalue lv)"

definition "lvalue_update0 f lv x = inv (lvalue_raw_representation0 lv)
                                        (apfst f (lvalue_raw_representation0 lv x))"
fun lvaluex_update where
  "lvaluex_update f (LValueX lv g) = lvalue_update0 (inv g o f o g) lv"

(* definition lvalue_map where "lvalue_map f lv x = inv (lvalue_raw_representation lv) (apfst f (lvalue_raw_representation lv x))" *)

lemma nonempty_range:
  assumes "valid_lvalue_raw0 lv"
  shows "lvalue_range0 lv \<noteq> {}"
using assms proof induction
  case (valid_lvalue_raw0_all D repr)
  then show ?case by auto
next
  case (valid_lvalue_raw0_unit D uu)
  then show ?case by auto
next
  case (valid_lvalue_raw0_mix F lvs repr rg)
  from valid_lvalue_raw0_mix.IH
  have "dependent_functions (index_set F) (\<lambda>i. lvalue_range0 (lvs i)) \<noteq> {}"
    by (rule dependent_functions_nonempty)
  with valid_lvalue_raw0_mix.hyps have "rg \<noteq> {}"
    using bij_betw_empty2 by blast
  then show ?case
    by simp
qed

lemma bij_lvalue_raw_representation0:
  assumes "valid_lvalue_raw0 lv"
  shows "bij_betw (lvalue_raw_representation0 lv) (lvalue_domain0 lv) (lvalue_range0 lv \<times> lvalue_raw_representation_range0 lv)"
  using assms proof induction
  case (valid_lvalue_raw0_all D repr)
  have "bij_betw (\<lambda>d. (repr d, undefined)) D (repr ` D \<times> {undefined})"
    apply (rule bij_betwI')
    using valid_lvalue_raw0_all apply (metis (full_types) fst_conv the_inv_into_f_f)
     apply simp
    by blast
  then show ?case by simp
next
  case (valid_lvalue_raw0_unit D r)
  have "bij_betw (\<lambda>d. (r,d)) D ({r} \<times> D)"
    apply (rule bij_betwI')
    using valid_lvalue_raw0_unit by auto
  then show ?case by simp
next
  case (valid_lvalue_raw0_mix F lvs repr rg)
  define I representation domain range representation_range factors factors_repr factors_result
    leftover leftover_f where
    "I = index_set F" and
    "representation = lvalue_raw_representation0 (LValue0 F lvs rg repr)" and
    "domain = (lvalue_domain0 (LValue0 F lvs rg repr))" and
    "range = lvalue_range0 (LValue0 F lvs rg repr)" and
    "representation_range = lvalue_raw_representation_range0 (LValue0 F lvs rg repr)" and

    "factors x = isomorphism F x" and
    "factors_repr x = (\<lambda>i::'a index. 
              if i\<in>I then lvalue_raw_representation0 (lvs i) (factors x i)
                               else (undefined,undefined))" and
    "factors_result x = fst o (factors_repr x)" and
    "leftover x = snd o (factors_repr x)" and
    "leftover_f = (SOME f::_\<Rightarrow>'a. inj_on f (dependent_functions I (\<lambda>i. lvalue_raw_representation_range0 (lvs i))))"
  for x
  note defs = this

  have representation: "representation x = (repr (factors_result x), leftover_f (leftover x))" for x
    unfolding defs by (simp add: Let_def)

  from valid_lvalue_raw0_mix
  have valid_F: "valid_lvalue_factorization F"
    and domain_lvs: "\<And>i. i \<in> I \<Longrightarrow> lvalue_domain0 (lvs i) = sets F i"
    unfolding I_def by simp_all

  have bij_comp: "bij_betw f A B \<Longrightarrow> bij_betw g B C \<Longrightarrow> bij_betw (\<lambda>x. g (f x)) A C" for f g A B C
    using bij_betw_trans[unfolded o_def] by metis

  from valid_F
  have bij_factors: "bij_betw factors domain (dependent_functions I (sets F))"
    unfolding factors_def[abs_def] domain_def I_def
    apply cases by simp

(*   have if_retest: "(if a then (if a then yy else yn) else (if a then ny else nn))
                  = (if a then yy else nn)" for yy yn ny nn a
    by auto *)

  from bij_factors 
  have bij_factors_result_leftover: "bij_betw (\<lambda>x i. (factors_result x i, leftover x i)) domain
     (dependent_functions' (undefined,undefined) I 
                           (\<lambda>i. lvalue_range0 (lvs i) \<times> lvalue_raw_representation_range0 (lvs i)))"
    unfolding factors_repr_def factors_result_def leftover_def o_def if_distrib fst_conv snd_conv
    apply (rule bij_comp)
    apply (rule bij_betw_dependent_functions)
     apply simp_all
    apply (subst domain_lvs[symmetric], simp)
    unfolding I_def
    by (rule valid_lvalue_raw0_mix.IH)

  have factors_result_undefined: "\<And>i. i \<notin> I \<longrightarrow> factors_result x i = undefined" for x
    unfolding factors_result_def factors_repr_def o_def by auto
  have leftover_undefined: "\<And>i. i \<notin> I \<longrightarrow> leftover x i = undefined" for x
    unfolding leftover_def factors_repr_def o_def by auto

  have factor_result_leftover: "(factors_result x, leftover x) = dependent_functions_split I ((\<lambda>x i. (factors_result x i, leftover x i)) x)" for x
    unfolding dependent_functions_split_def
    apply auto apply (rule ext) using factors_result_undefined apply simp
    apply (rule ext) using leftover_undefined by simp

  have bij_factors_result_leftover': "bij_betw (\<lambda>x. ((factors_result x), (leftover x))) domain
             (dependent_functions I (%i. lvalue_range0 (lvs i)) 
            \<times> dependent_functions I (%i. lvalue_raw_representation_range0 (lvs i)))"
    unfolding factor_result_leftover
    using bij_factors_result_leftover apply (rule bij_comp)
    apply (rule bij_betw_dependent_functions_split) by simp

  from valid_lvalue_raw0_mix.hyps
  have bij_repr: "bij_betw repr (dependent_functions I (\<lambda>i. lvalue_range0 (lvs i))) range"
    by (simp add: I_def range_def)

  have "leq_card (lvalue_raw_representation_range0 (lvs i)) (lvalue_range0 (lvs i) \<times> lvalue_raw_representation_range0 (lvs i))" if "i\<in>I" for i
    apply (rule leq_card_prod2)
    apply (rule nonempty_range)
    using that unfolding I_def by (rule valid_lvalue_raw0_mix.hyps)
  also have "leq_card (\<dots> i) (sets F i)" if "i:I" for i
    using I_def domain_lvs leq_cardI_bij' that valid_lvalue_raw0_mix.IH by fastforce
  finally have "leq_card (dependent_functions I (%i. lvalue_raw_representation_range0 (lvs i)))
                            (dependent_functions I (sets F))"
    by (rule dependent_functions_mono)
  also have "leq_card \<dots> domain"
    apply (rule leq_cardI_bij')
    by (rule bij_factors)
  finally have "\<exists>f::_\<Rightarrow>'a. inj_on f (dependent_functions I (\<lambda>i. lvalue_raw_representation_range0 (lvs i)))"
    unfolding leq_card_def by auto 
  then have "inj_on leftover_f
      (dependent_functions I (\<lambda>i. lvalue_raw_representation_range0 (lvs i)))"
    unfolding leftover_f_def
    by (rule someI_ex[where P="\<lambda>f. inj_on f _"])
  then have bij_leftover_f: "bij_betw leftover_f
      (dependent_functions I (\<lambda>i. lvalue_raw_representation_range0 (lvs i)))
          representation_range"
    unfolding representation_range_def
    by (simp add: I_def inj_on_imp_bij_betw leftover_f_def)

  have "bij_betw (\<lambda>x. map_prod repr leftover_f (factors_result x, leftover x)) domain (range \<times> representation_range)"
    using bij_factors_result_leftover'
    apply (rule bij_comp)
    using bij_repr bij_leftover_f by (rule bij_betw_map_prod)

  then show "bij_betw representation domain (range \<times> representation_range)"
    unfolding representation by auto
qed

lemma bij_lvaluex_representation:
  assumes "valid_lvaluex lv"
  shows "bij_betw (lvaluex_representation lv) (lvaluex_domain lv) 
                  (lvaluex_range lv \<times> lvaluex_representation_range lv)"
proof -
  obtain f lv0 where lv: "lv = LValueX lv0 f"
    using lvaluex.exhaust_sel by blast
  from assms
  have valid0: "valid_lvalue_raw0 lv0"
    using lv valid_lvaluex.cases by auto
  from assms
  have inj_f: "inj_on f (lvalue_range0 lv0)"
    using lv valid_lvaluex.cases by auto
  note bij_lvalue_raw_representation0[OF valid0]
  moreover
  have "bij_betw (apfst f) (lvalue_range0 lv0 \<times> lvalue_raw_representation_range0 lv0)
                           (f ` lvalue_range0 lv0 \<times> lvalue_raw_representation_range0 lv0)"
    apply (rule bij_betwI')
    using inj_f inj_on_contraD apply fastforce
    by auto 
  ultimately
  show ?thesis
    apply (simp add: lv lvaluex_representation_def[abs_def] lvaluex_representation_range_def)
    by (rule bij_betw_trans[unfolded o_def], auto)
qed

(* lemma
  fixes lv1 :: "('a,'b) lvaluex" and lv2 :: "('a,'c) lvaluex"
  assumes "valid_lvaluex lv1"
  assumes "valid_lvaluex lv2"
  assumes "compatible_lvaluex lv1 lv2"
  shows "lvaluex_update f1 lv1 (lvaluex_update f2 lv2 x)
       = lvaluex_update (map_prod f1 f2) (compose_lvaluex lv1 lv2) x"
  orry *)
(* TODO same the other way around *)

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
" valid_lvaluex x \<Longrightarrow> valid_lvaluex y \<Longrightarrow> compatible_lvaluex x y
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
proof -
  have valid_x: "valid_lvaluex x"
    and valid_y: "valid_lvaluex y"
    and compat: "compatible_lvaluex x y"
    using left_composition_f
    using left_composition_f.cases by blast+
  have valid_xy: "valid_lvaluex xy"
    unfolding xy_def using valid_x valid_y compat by (rule valid_compose_lvaluex)
  have x_dom: "lvaluex_domain xy = lvaluex_domain x"
    unfolding xy_def apply (rule domain_compose_lvaluex)
    using valid_x valid_y compat by simp_all
  with z1_dom have z1_dom': "z1 \<in> lvaluex_domain xy"
    unfolding xy_def by simp
  from x_dom z2_dom have z2_dom': "z2 \<in> lvaluex_domain xy"
    unfolding xy_def by simp
  have inj: "inj_on f' (lvaluex_range y \<times> lvaluex_representation_range (compose_lvaluex x y))"
    using left_composition_f apply cases
    by (simp add: bij_betw_imp_surj_on inj_on_inv_into)
  have Rxy_z1_rg: "Rxy z1 \<in> (lvaluex_range x \<times> lvaluex_range y) \<times> lvaluex_representation_range xy"
    using bij_lvaluex_representation[OF valid_xy] 
    unfolding Rxy_def xy_def[symmetric] range_compose_lvaluex[OF valid_x valid_y compat, symmetric]
    using z1_dom' bij_betwE by blast 
  have Rxy_z2_rg: "Rxy z2 \<in> (lvaluex_range x \<times> lvaluex_range y) \<times> lvaluex_representation_range xy"
    using bij_lvaluex_representation[OF valid_xy] 
    unfolding Rxy_def xy_def[symmetric] range_compose_lvaluex[OF valid_x valid_y compat, symmetric]
    using z2_dom' bij_betwE by blast 
  from Rxy_z1_rg
  have 1: "(y1,r1) \<in> (lvaluex_range y \<times> lvaluex_representation_range (compose_lvaluex x y))"
    unfolding Rxy_z1 unfolding xy_def by auto
  from Rxy_z2_rg
  have 2: "(y2,r2) \<in> (lvaluex_range y \<times> lvaluex_representation_range (compose_lvaluex x y))"
    unfolding Rxy_z2 unfolding xy_def by auto
  from inj 1 2
  show ?thesis
    by (simp add: inj_on_eq_iff)
qed

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
proof -
  have valid_x: "valid_lvaluex x"
    and valid_y: "valid_lvaluex y"
    and compat: "compatible_lvaluex x y"
    using right_composition_f
    using right_composition_f.cases by blast+
  have valid_xy: "valid_lvaluex xy"
    unfolding xy_def using valid_x valid_y compat by (rule valid_compose_lvaluex)
  have y_dom: "lvaluex_domain xy = lvaluex_domain y"
    unfolding xy_def apply (rule domain_compose_lvaluex)
    using valid_x valid_y compat by simp_all
  with z1_dom have z1_dom': "z1 \<in> lvaluex_domain xy"
    unfolding xy_def by simp
  from y_dom z2_dom have z2_dom': "z2 \<in> lvaluex_domain xy"
    unfolding xy_def by simp
  have inj: "inj_on f' (lvaluex_range x \<times> lvaluex_representation_range (compose_lvaluex x y))"
    using right_composition_f apply cases
    by (simp add: bij_betw_imp_surj_on inj_on_inv_into)
  have Rxy_z1_rg: "Rxy z1 \<in> (lvaluex_range x \<times> lvaluex_range y) \<times> lvaluex_representation_range xy"
    using bij_lvaluex_representation[OF valid_xy] 
    unfolding Rxy_def xy_def[symmetric] range_compose_lvaluex[OF valid_x valid_y compat, symmetric]
    using z1_dom' bij_betwE by blast 
  have Rxy_z2_rg: "Rxy z2 \<in> (lvaluex_range x \<times> lvaluex_range y) \<times> lvaluex_representation_range xy"
    using bij_lvaluex_representation[OF valid_xy] 
    unfolding Rxy_def xy_def[symmetric] range_compose_lvaluex[OF valid_x valid_y compat, symmetric]
    using z2_dom' bij_betwE by blast 
  from Rxy_z1_rg
  have 1: "(x1,r1) \<in> (lvaluex_range x \<times> lvaluex_representation_range (compose_lvaluex x y))"
    unfolding Rxy_z1 unfolding xy_def by auto
  from Rxy_z2_rg
  have 2: "(x2,r2) \<in> (lvaluex_range x \<times> lvaluex_representation_range (compose_lvaluex x y))"
    unfolding Rxy_z2 unfolding xy_def by auto
  from inj 1 2
  show ?thesis
    by (simp add: inj_on_eq_iff)
qed

lemma left_composition_map_back: 
  assumes left_composition_f: "left_composition_f x y f f'"
  defines "xy == compose_lvaluex x y"
  defines "Rx == lvaluex_representation x"
  defines "Rxy == lvaluex_representation xy"
  assumes z: "z \<in> lvaluex_domain x"
  shows "Rx z = left_composition_map_back f' (Rxy z)"
proof -
  from left_composition_f
  have Rxy: "left_composition_map f (Rx z) = Rxy z" for z
    unfolding xy_def Rxy_def Rx_def
    apply cases by simp
  from left_composition_f
  have f': "f' = inv_into (lvaluex_representation_range x) f"
    apply cases by simp
  from left_composition_f
  have valid_x: "valid_lvaluex x"
    apply cases by simp

  have [simp]: "r = f' (f r)" if "Rx z = (a, r)" and "z \<in> lvaluex_domain x" for z a r
  proof -
    note bij_lvaluex_representation[OF valid_x]
    then have "Rx z \<in> (lvaluex_range x \<times> lvaluex_representation_range x)"
      unfolding that Rx_def using that bij_betwE by fastforce
    then have "r \<in> lvaluex_representation_range x"
      unfolding that by simp
    then show ?thesis
      unfolding f'
      by (metis bij_betw_def inv_into_f_f left_composition_f left_composition_f.cases)
  qed
  show ?thesis
    unfolding Rxy[symmetric]
    apply (cases "Rx z") using z
    unfolding left_composition_map_def left_composition_map_back_def 
    by (auto simp: case_prod_beta)
qed

lemma right_composition_map_back: 
  assumes right_composition_f: "right_composition_f x y f f'"
  defines "xy == compose_lvaluex x y"
  defines "Ry == lvaluex_representation y"
  defines "Rxy == lvaluex_representation xy"
  assumes z: "z \<in> lvaluex_domain y"
  shows "Ry z = right_composition_map_back f' (Rxy z)"
proof -
  from right_composition_f
  have Rxy: "right_composition_map f (Ry z) = Rxy z" for z
    unfolding xy_def Rxy_def Ry_def
    apply cases by simp
  from right_composition_f
  have f': "f' = inv_into (lvaluex_representation_range y) f"
    apply cases by simp
  from right_composition_f
  have valid_y: "valid_lvaluex y"
    apply cases by simp

  have [simp]: "r = f' (f r)" if "Ry z = (a, r)" and "z \<in> lvaluex_domain y" for z a r
  proof -
    note bij_lvaluex_representation[OF valid_y]
    then have "Ry z \<in> (lvaluex_range y \<times> lvaluex_representation_range y)"
      unfolding that Ry_def using that bij_betwE by fastforce
    then have "r \<in> lvaluex_representation_range y"
      unfolding that by simp
    then show ?thesis
      unfolding f'
      by (metis bij_betw_def inv_into_f_f right_composition_f right_composition_f.cases)
  qed
  show ?thesis
    unfolding Rxy[symmetric]
    apply (cases "Ry z") using z
    unfolding right_composition_map_def right_composition_map_back_def 
    by (auto simp: case_prod_beta)
qed

lemma composed_lvalue_relationship_left:
  fixes x :: "('a,'b) lvaluex" and y :: "('a,'c) lvaluex"
  assumes "valid_lvaluex x"
  assumes "valid_lvaluex y"
  assumes "compatible_lvaluex x y"
  defines "xy == compose_lvaluex x y"
  obtains f f' where "left_composition_f x y f f'"
  sorry

lemma composed_lvalue_relationship_right:
  fixes x :: "('a,'b) lvaluex" and y :: "('a,'c) lvaluex"
  assumes "valid_lvaluex x"
  assumes "valid_lvaluex y"
  assumes "compatible_lvaluex x y"
  defines "xy == compose_lvaluex x y"
  obtains f f' where "right_composition_f x y f f'"
  sorry

typedef 'a::finite matrix = "UNIV::('a\<Rightarrow>'a\<Rightarrow>complex) set" by simp
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
  sorry

definition fst_lvalue :: "('a*'b, 'a) lvaluex" where
  "fst_lvalue = LValueX (LValue0 pair_factorization 
      (\<lambda>i. if i=value1 then LValueAll0 fst_subset id else LValueUnit0 snd_subset undefined)
      fst_subset (\<lambda>x. fst_iso (fst (x value1)))) (inv fst_iso)" *)

instantiation matrix :: (finite) ring_1 begin
lift_definition times_matrix :: "'a matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" is "%A B i k. (\<Sum>j\<in>UNIV. A i j * B j k)".
lift_definition one_matrix :: "'a matrix" is "\<lambda>i j. if i=j then 1 else 0".
instance sorry
end

axiomatization
  fst_lvalue :: "('a*'b, 'a) lvaluex" and
  snd_lvalue :: "('a*'b, 'b) lvaluex" where
  valid_fst_lvalue: "valid_lvaluex fst_lvalue" and
  valid_snd_lvalue: "valid_lvaluex snd_lvalue" and
  compatible_fst_snd: "compatible_lvaluex fst_lvalue snd_lvalue" and
  compatible_snd_fst: "compatible_lvaluex snd_lvalue fst_lvalue"

abbreviation "delta x y == (if x=y then 1 else 0)"

lift_definition matrix_on :: "'b::finite matrix \<Rightarrow> ('a::finite,'b) lvaluex \<Rightarrow> 'a matrix" is
  "\<lambda>B lv (r::'a) (c::'a). B (fst (lvaluex_representation lv r)) (fst (lvaluex_representation lv c))
  * delta (snd (lvaluex_representation lv r)) (snd (lvaluex_representation lv c))".

lemma matrix_on_lift_left:
  assumes "valid_lvaluex x" and "valid_lvaluex y" and "compatible_lvaluex x y"
  assumes domain[simp]: "lvaluex_domain x = UNIV"
  defines "xy == compose_lvaluex x y"
  shows "matrix_on A x = matrix_on (tensor A 1) xy"
proof (transfer fixing: x y xy, rule ext, rule ext)
  fix A :: "'b \<Rightarrow> 'b \<Rightarrow> complex" and r c
  define Rx where "Rx = lvaluex_representation x"
  define Rxy where "Rxy = lvaluex_representation xy"
  from composed_lvalue_relationship_left[OF assms(1-3)]
  obtain f f' where f: "left_composition_f x y f f'"
    by auto
  have valid_xy: "valid_lvaluex xy"
    unfolding xy_def using assms(1-3) by (rule valid_compose_lvaluex)
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
  assumes "valid_lvaluex x" and "valid_lvaluex y" and "compatible_lvaluex x y"
  assumes domain[simp]: "lvaluex_domain y = UNIV"
  defines "xy == compose_lvaluex x y"
  shows "matrix_on A y = matrix_on (tensor 1 A) xy"
proof (transfer fixing: x y xy, rule ext, rule ext)
  fix A :: "'c \<Rightarrow> 'c \<Rightarrow> complex" and r c
  define Ry where "Ry = lvaluex_representation y"
  define Rxy where "Rxy = lvaluex_representation xy"
  from composed_lvalue_relationship_right[OF assms(1-3)]
  obtain f f' where f: "right_composition_f x y f f'"
    by auto
  have valid_xy: "valid_lvaluex xy"
    unfolding xy_def using assms(1-3) by (rule valid_compose_lvaluex)
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
  sorry

lemma matrix_on_times: 
  assumes "valid_lvaluex x"
  shows "matrix_on A x * matrix_on B x = matrix_on (A*B) x"
  apply (transfer fixing: x, rule ext, rule ext)
  sorry

lemma
  assumes "valid_lvaluex x" and "valid_lvaluex y" and "compatible_lvaluex x y"
  assumes "lvaluex_domain x = UNIV"
  defines "xy == compose_lvaluex x y"
  shows "matrix_on A x * matrix_on B y = matrix_on (tensor A B) xy"
  apply (subst matrix_on_lift_left[where A=A and y=y])
  using assms(1-4) apply simp_all[4]
  apply (subst matrix_on_lift_right[where A=B and x=x])
  using assms(1-3) apply simp_all[3]
  using assms(3,4)
  using assms(1-2) domain_compose_lvaluex apply fastforce
  apply (subst matrix_on_times)
   apply (simp add: assms(1) assms(2) assms(3) valid_compose_lvaluex)
  unfolding xy_def[symmetric]
  by (simp add: tensor_distrib)

end
