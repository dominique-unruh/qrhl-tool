theory LValue
  imports Main "HOL-Library.Rewrite" (* "HOL-Cardinals.Cardinals" *)
begin

typedef 'a index = "UNIV::'a set" ..
(* typedef 'a target = "UNIV::'a set" .. *)

inductive_set dependent_functions :: "_ \<Rightarrow> _ \<Rightarrow> ('a\<Rightarrow>'b) set"
  for domain :: "'a set" and range :: "'a \<Rightarrow> 'b set" where
  "\<lbrakk> \<And>a. a\<notin>domain \<Longrightarrow> f a = undefined;
     \<And>a. a\<in>domain \<Longrightarrow> f a \<in> range a \<rbrakk>
   \<Longrightarrow> f \<in> dependent_functions domain range"

definition "leq_card A B = (\<exists>f. inj_on f A \<and> f`A \<subseteq> B)" (* Equivalent to (card_of A \<le>o card_of B). TODO use that? *)

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

lemma bij_betw_dependent_functions: 
  assumes bij_f: "\<And>i. i \<in> I \<Longrightarrow> bij_betw (f i) (A i) (B i)"
  assumes f_undef: "\<And>i x. i \<notin> I \<Longrightarrow> f i x = undefined"
  shows "bij_betw (\<lambda>g i. f i (g i)) (dependent_functions I A) (dependent_functions I B)"
proof (rule bij_betwI')
  fix x y
  assume x: "x \<in> dependent_functions I A"
  show "(\<lambda>i. f i (x i)) \<in> dependent_functions I B"
    apply (rule dependent_functions.intros)
    apply (simp add: assms(2))
    by (meson x assms(1) bij_betwE dependent_functions.cases)
  assume y: "y \<in> dependent_functions I A"
  from bij_f have inj_f: "inj_on (f i) (A i)" if "i:I" for i
    by (simp add: bij_betw_def that)
  have "x = y" if "(\<lambda>i. f i (x i)) = (\<lambda>i. f i (y i))"
    apply (rule ext)
    using that inj_f
    by (metis (full_types) dependent_functions.cases inj_on_eq_iff x y)
  then show "((\<lambda>i. f i (x i)) = (\<lambda>i. f i (y i))) = (x = y)"
    by auto
next
  fix y
  assume y: "y \<in> dependent_functions I B"
  have "\<exists>x'. (y i = f i x' \<and> (i\<in>I \<longrightarrow> x' \<in> A i) \<and> (i\<notin>I \<longrightarrow> x' = undefined))" for i
    apply (cases "i\<in>I")
    apply (metis bij_betw_def bij_f dependent_functions.cases image_iff y)
    using dependent_functions.simps f_undef y by fastforce 
  then obtain x where x: "(y i = f i (x i) \<and> (i\<in>I \<longrightarrow> x i \<in> A i) \<and> (i\<notin>I \<longrightarrow> x i = undefined))" for i
    apply atomize_elim apply (rule choice) by simp
  then have "x\<in>dependent_functions I A" 
    apply (rule_tac dependent_functions.intros) by auto
  moreover
  from x have "y = (\<lambda>i. f i (x i))"
    by auto
  ultimately show "\<exists>x\<in>dependent_functions I A. y = (\<lambda>i. f i (x i))"
    by auto
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
    unfolding F_def apply (rule dependent_functions.intros) apply auto
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
  shows "bij_betw (dependent_functions_split I) (dependent_functions I AB)
     (dependent_functions I A \<times> dependent_functions I B)"
proof (rule bij_betwI')
  fix x y :: "'a \<Rightarrow> 'b \<times> 'c"
  assume x: "x \<in> dependent_functions I AB"
  then have x_undef: "i \<notin> I \<Longrightarrow> x i = undefined" for i
    by cases
  assume y: "y \<in> dependent_functions I AB"
  then have y_undef: "i \<notin> I \<Longrightarrow> y i = undefined" for i
    by cases
  show "(dependent_functions_split I x = dependent_functions_split I y) = (x = y)"
    unfolding o_def dependent_functions_split_def 
    apply auto
    by (metis prod_eq_iff x_undef y_undef ext)
  have "(\<lambda>i. if i \<in> I then fst (x i) else undefined) \<in> dependent_functions I A"
    using x apply cases apply (subst dependent_functions.simps)
    using assms by force
  moreover
  have "(\<lambda>i. if i \<in> I then snd (x i) else undefined) \<in> dependent_functions I B"
    using x apply cases apply (subst dependent_functions.simps)
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
    by (metis dependent_functions.cases g1)
  obtain f2 where f2: "g2 i = (if i \<in> I then f2 i else undefined)" for i
    by (metis dependent_functions.cases g2)
  define f where "f i = (if i:I then (f1 i, f2 i) else undefined)" for i
  have fAB: "f \<in> dependent_functions I AB"
    apply (rule dependent_functions.intros) unfolding f_def using assms apply auto
    apply (metis dependent_functions.cases f1 g1)
    by (metis dependent_functions.cases f2 g2)
  show "\<exists>f\<in>dependent_functions I AB. g = dependent_functions_split I f"
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
  valid_lvalue_raw0_all: "inj_on repr D \<Longrightarrow> valid_lvalue_raw0 (LValueAll0 D repr)"
| valid_lvalue_raw0_unit: "D \<noteq> {} \<Longrightarrow> valid_lvalue_raw0 (LValueUnit0 D _)"
| valid_lvalue_raw0_mix: "\<lbrakk> 
     valid_lvalue_factorization F;
     \<And>i. i\<in>index_set F \<Longrightarrow> valid_lvalue_raw0 (lvalues i);
     \<And>i. i\<in>index_set F \<Longrightarrow> lvalue_domain0 ( (lvalues i)) = sets F i;
     bij_betw repr (dependent_functions (index_set F) (\<lambda>i. lvalue_range0 (lvalues i))) rg
   \<rbrakk> \<Longrightarrow> valid_lvalue_raw0 (LValue0 F lvalues rg repr)"

inductive valid_lvaluex where
  "valid_lvalue_raw0 lv \<Longrightarrow> inj_on f (lvalue_range0 lv) \<Longrightarrow> valid_lvaluex (LValueX lv f)"

(* TODO remove *)
inductive valid_lvalue_raw :: "('a,'b) lvalue_raw \<Rightarrow> bool" where
  "inj_on repr D \<Longrightarrow> valid_lvalue_raw (LValueAll D repr)"
| "valid_lvalue_raw (LValueUnit _ _)"
| "\<lbrakk> 
     valid_lvalue_factorization F;
     \<And>i. i\<in>index_set F \<Longrightarrow> valid_lvalue_raw0 (lvalues i);
     \<And>i. i\<in>index_set F \<Longrightarrow> lvalue_domain (of_lvalue0 (lvalues i)) = sets F i;
     bij_betw repr (dependent_functions (index_set F) (\<lambda>i. lvalue_range (of_lvalue0 (lvalues i)))) rg
   \<rbrakk> \<Longrightarrow> valid_lvalue_raw (LValue F lvalues rg repr)"

(* TODO remove *)
lemma to_lvalue0_subst: "(\<And>x. P (to_lvalue0 x)) \<Longrightarrow> P y"
  by (metis lvalue_raw0.exhaust to_lvalue0.simps(1) to_lvalue0.simps(2) to_lvalue0.simps(3))
  
(* TODO remove *)
lemma valid_lvalue_raw_of_lvalue0: "valid_lvalue_raw (of_lvalue0 lv0) = valid_lvalue_raw0 lv0" 
proof -
  have "valid_lvalue_raw0 (to_lvalue0 lv)" if "valid_lvalue_raw lv" for lv
    using that apply induction 
      apply auto
      apply (subst valid_lvalue_raw0.simps) apply simp
     apply (subst valid_lvalue_raw0.simps) sorry
    (* apply (subst valid_lvalue_raw0.simps) sorry *)
  note this[of "of_lvalue0 lv0", simplified]
  moreover have "valid_lvalue_raw (of_lvalue0 lv0)" if "valid_lvalue_raw0 lv0"
    using that apply induction sorry
  ultimately show ?thesis 
    by blast
qed

typedef ('a,'b) lvalue = "UNIV :: (('a,'b) lvalue_raw) set" ..
setup_lifting type_definition_lvalue

lift_definition valid_lvalue :: "('a,'b) lvalue \<Rightarrow> bool" is
 "\<lambda>lvalue::('a,'b) lvalue_raw. valid_lvalue_raw lvalue \<and> lvalue_domain lvalue = (UNIV::'a set)
     \<and> lvalue_range lvalue = (UNIV::'b set)" .

inductive compatible_lvalue_raw0 :: "'a lvalue_raw0 \<Rightarrow> 'a lvalue_raw0 \<Rightarrow> bool" where
  compatible_lvalue_raw0_unitleft: "lvalue_domain0 lv2 = D \<Longrightarrow> compatible_lvalue_raw0 (LValueUnit0 D _) lv2"
| compatible_lvalue_raw0_unitright: "lvalue_domain0 lv1 = D \<Longrightarrow> compatible_lvalue_raw0 lv1 (LValueUnit0 D _)"
| compatible_lvalue_raw0_merge:
  "\<lbrakk> valid_lvalue_raw0 (LValue0 F lvs1 rg1 repr1);
     valid_lvalue_raw0 (LValue0 F lvs2 rg2 repr2);
     \<And>i. i\<in>index_set F \<Longrightarrow> compatible_lvalue_raw0 (lvs1 i) (lvs2 i)
   \<rbrakk> \<Longrightarrow> compatible_lvalue_raw0 (LValue0 F lvs1 rg1 repr1) (LValue0 F lvs2 rg2 repr2)"

(* TODO remove *)
inductive compatible_lvalue_raw :: "('a,'b) lvalue_raw \<Rightarrow> ('a,'c) lvalue_raw \<Rightarrow> bool" where
  "lvalue_domain lv2 = D \<Longrightarrow> compatible_lvalue_raw (LValueUnit D _) lv2"
| "lvalue_domain lv1 = D \<Longrightarrow> compatible_lvalue_raw lv1 (LValueUnit D _)"
| "\<lbrakk> valid_lvalue_raw (LValue F lvs1 rg1 repr1);
     valid_lvalue_raw (LValue F lvs2 rg2 repr2);
     \<And>i. i\<in>index_set F \<Longrightarrow> compatible_lvalue_raw0 (lvs1 i) (lvs2 i)
   \<rbrakk> \<Longrightarrow> compatible_lvalue_raw (LValue F lvs1 rg1 repr1) (LValue F lvs2 rg2 repr2)"

inductive compatible_lvaluex where
  "compatible_lvalue_raw0 lv1 lv2 \<Longrightarrow> compatible_lvaluex (LValueX lv1 _) (LValueX lv2 _)"

(* TODO remove *)
lemma compatible_lvalue_raw_of_lvalue0: "compatible_lvalue_raw (of_lvalue0 lv0) (of_lvalue0 lv0') = compatible_lvalue_raw0 lv0 lv0'" 
proof -
  have "compatible_lvalue_raw0 (to_lvalue0 lv) (to_lvalue0 lv')" if "compatible_lvalue_raw lv lv'" for lv lv' :: "('a,'a) lvalue_raw"
    using that apply induction 
      apply auto
      apply (subst compatible_lvalue_raw0.simps) apply simp
      sorry
    
  note this[of "of_lvalue0 lv0" "of_lvalue0 lv0'", simplified]
  moreover have "compatible_lvalue_raw (of_lvalue0 lv0) (of_lvalue0 lv0')" if "compatible_lvalue_raw0 lv0 lv0'"
    using that apply induction
      apply (auto simp: compatible_lvalue_raw.simps)[2]
    (* by (metis compatible_lvalue_raw.intros(3) of_lvalue0.simps(3) valid_lvalue_raw_of_lvalue0) *)
    sorry
  ultimately show ?thesis 
    by blast
qed

lift_definition compatible_lvalue :: "('a,'b) lvalue \<Rightarrow> ('a,'c) lvalue \<Rightarrow> bool" is 
  "compatible_lvalue_raw :: ('a,'b) lvalue_raw \<Rightarrow> ('a,'c) lvalue_raw \<Rightarrow> bool" .

(* TODO remove *)
fun map_lvalue :: "('b\<Rightarrow>'c) \<Rightarrow> ('a,'b) lvalue_raw \<Rightarrow> ('a,'c) lvalue_raw" where
  "map_lvalue f (LValueUnit D r) = LValueUnit D (f r)"
| "map_lvalue f (LValueAll D repr) = LValueAll D (f o repr)"
| "map_lvalue f (LValue F lvs rg repr) = LValue F lvs (f ` rg) (f o repr)"

fun map_lvaluex where
  "map_lvaluex g (LValueX lv f) = LValueX lv (g o f)"

definition "lvalue_raw0_to_lvaluex lv = LValueX lv id"


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

(* TODO remove *)
function (sequential) compose_lvalue_raw0 :: "'a lvalue_raw0 \<Rightarrow> 'a lvalue_raw0 \<Rightarrow> ('a,'a\<times>'a) lvalue_raw" where
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
  by (auto simp: relation_prod_def lvalue_raw0_termination_relation.simps)

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
         fun :: 'a\<Rightarrow>'a*'a = (map_prod repr1 repr2) o (dependent_functions_split (index_set F1)) o (\<lambda>g i. (f'' i) (g i)) o (inv_into depfuns repr')
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
fun compose_lvalue_raw :: "('a,'b) lvalue_raw \<Rightarrow> ('a,'c) lvalue_raw \<Rightarrow> ('a,'b\<times>'c) lvalue_raw" where
  "compose_lvalue_raw (LValueUnit _ r) lv2 = map_lvalue (\<lambda>x2. (r,x2)) (lv2)"
| "compose_lvalue_raw lv1 (LValueUnit _ r) = map_lvalue (\<lambda>x1. (x1,r)) (lv1)"
| "compose_lvalue_raw (LValueAll _ _) _ = undefined" (* cannot be compatible *)
| "compose_lvalue_raw _ (LValueAll _ _) = undefined" (* cannot be compatible *)
| "compose_lvalue_raw (LValue F1 lvs1 rg1 repr1) (LValue F2 lvs2 rg2 repr2) = 
    (let f = \<lambda>i. SOME f. inj_on f (lvalue_range0 (lvs1 i) \<times> lvalue_range0 (lvs2 i)) in
     let f' = \<lambda>all. let all1 = \<lambda>i. fst (inv (f i) (all i)); all2 = \<lambda>i. snd (inv (f i) (all i)) in (repr1 all1, repr2 all2) in
    LValue F1 (\<lambda>i. to_lvalue0 (map_lvalue (f i) (compose_lvalue_raw0 (lvs1 i) (lvs2 i)))) (rg1\<times>rg2) f')"

lemma lvaluex_domain_compose_lvalue_raw0':
  assumes valid1: "valid_lvalue_raw0 lv1"
  assumes valid2: "valid_lvalue_raw0 lv2"
  assumes compat: "compatible_lvalue_raw0 lv1 lv2"
  shows "lvaluex_domain (compose_lvalue_raw0' lv1 lv2) = lvalue_domain0 lv1"
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

lemma conj_to_conjunctionI: "A \<and> B \<Longrightarrow> (A &&& B)"
  by presburger

lemma 
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
  shows "valid_lvaluex (compose_lvalue_raw0' lv1 lv2)" 
    and "lvaluex_range (compose_lvalue_raw0' lv1 lv2) = lvalue_range0 lv1 \<times> lvalue_range0 lv2"
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
    by x *)
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
    have "leq_card (lvalue_range0 (lvs'' i)) (sets F i)" if "i\<in>index_set F" for i
      using valid_lvs''[OF that] apply (cases)

    
    from valid_lvs'
    thm compatible_lvalue_raw0_merge
    thm 1
\<comment> \<open>Sketch:

depfuns = I->(\<lambda>i. lvalue_range0 (lvs'' i))

lvalue_range0 (lvs'' i) = compose (lvalue_range0 (lvs1 i) * lvalue_range0 (lvs2 i))
<= F_i (IH???)

Thus depfuns <= I->F_i <= UNIV('a)

Thus \<exists>f

\<close>

thm depfuns_def
    show "\<exists>f. inj_on f depfuns"
      by x
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
  

lemma
  assumes "valid_lvalue_raw0 lv1"
  assumes "valid_lvalue_raw0 lv2"
  assumes "valid_lvalue_raw0 lv3"
  assumes "compatible_lvalue_raw0 lv1 lv2"
  assumes "compatible_lvalue_raw0 lv1 lv3"
  assumes "compatible_lvalue_raw0 lv2 lv3"
  shows "compatible_lvalue_raw0 (lvaluex_lvalue (compose_lvalue_raw0' lv1 lv2)) lv3"
  sorry

definition "TODO = undefined"

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

definition "lvalue_update0 f lv x = inv (lvalue_raw_representation0 lv) (apfst f (lvalue_raw_representation0 lv x))"
fun lvaluex_update where
  "lvaluex_update f (LValueX lv g) = lvalue_update0 (inv g o f o g) lv"

(* definition lvalue_map where "lvalue_map f lv x = inv (lvalue_raw_representation lv) (apfst f (lvalue_raw_representation lv x))" *)

lemma 
  assumes "valid_lvalue_raw0 lv"
  shows "bij_betw (lvalue_raw_representation0 lv) (lvalue_domain0 lv) (lvalue_range0 lv \<times> lvalue_raw_representation_range0 lv)"
  sorry



lemma
  fixes lv1 :: "('a,'b) lvaluex" and lv2 :: "('a,'c) lvaluex"
  assumes "valid_lvaluex lv1"
  assumes "valid_lvaluex lv2"
  assumes "compatible_lvaluex lv1 lv2"
  shows "lvaluex_update f1 lv1 (lvaluex_update f2 lv2 x) = lvaluex_update (map_prod f1 f2) (compose_lvaluex lv1 lv2) x"
  sorry
(* TODO same the other way around *)

end
