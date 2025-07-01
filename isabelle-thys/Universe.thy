theory Universe
  imports Main "HOL.BNF_Cardinal_Order_Relation" (* Misc Tools *) "HOL-Library.Nat_Bijection" "HOL-Library.Rewrite" "HOL-ZF.HOLZF" ML_Term_Antiquot
    Deriving.Derive_Manager 
    BOLegacy (* Importing this to get Registers.Misc, so that "prod :: default" is not redefined here. *)
begin

hide_const (open) HOLZF.Inf
unbundle no m_inv_syntax

(* For proving instances of types declared with 
  "datatype" (not "datatype_new"), see, e.g., "char"

  For proving instances of types declared with 
  "typedef", see, e.g., "ell1"
*)                                           

    

lemma ZF_Pow_explode: "Pow (explode z) = explode ` explode (Power z)"
proof (rule; rule)
  fix x assume "x \<in> Pow (explode z)" 
  hence "x \<subseteq> explode z" by simp
      
  hence "y \<in> (explode z)" if "y \<in> x" for y  
    using that by blast
  hence yz: "Elem y z" if "y \<in> x" for y
    by (simp add: explode_Elem that) 
      
  define y where "y = Replacement z (\<lambda>t. if (t \<in> x) then Some t else None)"
  have xy: "x = explode y"
    unfolding y_def explode_def Replacement
    using yz by auto 
  have "Elem y (Power z)"
    unfolding y_def
    using Power xy y_def explode_Elem subset_def yz by force
      
  with xy show "x \<in> explode ` explode (Power z)" 
    apply (subst explode_def) by auto
next
  fix x assume "x \<in> explode ` explode (Power z)"
  thus "x \<in> Pow (explode z)"
    using Power explode_Elem subset_def by auto
qed

  
typedef universe = "{(x,n) | x n. Elem x ((Power ^^ n) HOLZF.Inf)}" 
  apply (rule exI[of _ "(Empty,0)"])
  by (simp add: Infinity)
(*
Alternatively, universe can be axiomatized as follows, which is weaker than the ZF axioms 
(the consts below is implied by existence of a smaller cardinal, namely beth_\<omega>)

typedecl universe
consts universe_powertower :: "nat \<Rightarrow> universe set" where
    universe_powertower: "\<exists>i. inj_on i (Pow (universe_powertower n)) \<and> i ` (Pow (universe_powertower n)) \<subseteq> universe_powertower (Suc n)"
and universe_powertower_disjoint: "x \<in> universe_powertower n \<Longrightarrow> x \<in> universe_powertower m \<Longrightarrow> n=m"
and universe_powertower_nat: "\<exists>n (i::nat\<Rightarrow>universe). inj i \<and> range i \<subseteq> universe_powertower n" 
and universe_powertower_all: "(\<Union>n. universe_powertower n) = UNIV"
*)

    
setup_lifting type_definition_universe
definition "universe_powertower n = {Abs_universe (x,n) | x. Elem x ((Power ^^ n) HOLZF.Inf)}"
lemma universe_powertower: "\<exists>i. inj_on i (Pow (universe_powertower n)) \<and> i ` (Pow (universe_powertower n)) \<subseteq> universe_powertower (Suc n)"
proof -
  define D0 where "D0 = Pow (universe_powertower n)"
  define i0 where "i0 x = Rep_universe ` x" for x
  have "inj_on i0 D0"
    by (metis Rep_universe_inverse \<open>i0 \<equiv> (`) Rep_universe\<close> inj_on_image inj_on_inverseI)
  define D1 where "D1 = i0 ` D0"
  have D1: "D1 = Pow {(x,n) | x. Elem x ((Power ^^ n) HOLZF.Inf)}" 
    unfolding D1_def i0_def D0_def universe_powertower_def
    apply (subst image_Pow_surj) apply rule
    apply (subst image_Collect)
    using Abs_universe_inverse by force
  define i1 where i1_def: "i1 x = fst ` x" for x :: "(ZF*nat) set"
  have "inj_on i1 D1"
    apply (rule inj_onI) unfolding i1_def D1 
    apply auto
    apply (smt \<open>i1 \<equiv> (`) fst\<close> contra_subsetD fst_conv imageI image_iff mem_Collect_eq old.prod.exhaust prod.inject)
    by (smt \<open>i1 \<equiv> (`) fst\<close> contra_subsetD fst_conv imageI image_iff mem_Collect_eq old.prod.exhaust prod.inject)

  define D2 where "D2 = i1 ` D1" 
  have "D2 = Pow (explode ((Power ^^ n) HOLZF.Inf))"
    unfolding D2_def i1_def D1 explode_def
    apply (subst image_Pow_surj) apply rule
    apply (subst image_Collect) by auto
  hence D2: "D2 = explode ` explode ((Power ^^ Suc n) HOLZF.Inf)"
    unfolding ZF_Pow_explode by simp
      
  define i2 where "i2 = implode"
  have "inj_on i2 D2"
    apply (rule inj_onI) unfolding D2 i2_def by auto

  define D3 where "D3 = i2 ` D2"
  have D3: "D3 = explode ((Power ^^ Suc n) HOLZF.Inf)"
    unfolding D3_def D2 i2_def  image_comp o_def  by simp
  define i3 where "i3 z = Abs_universe (z, Suc n)" for z
  have "inj_on i3 D3"
    apply (rule inj_onI)
    unfolding i3_def
    by (metis D3 Domainp.cases Rep_universe_inverse cr_universe_def explode_Elem prod.sel(1) universe.domain_eq universe.pcr_cr_eq)
      
  define D4 where "D4 = i3 ` D3" 
  have D4: "D4 = universe_powertower (Suc n)" 
    unfolding universe_powertower_def D4_def D3 i3_def
    by (simp add: explode_def image_Collect)
      
  define i where "i = i3 o i2 o i1 o i0"
  have inj_i: "inj_on i D0" 
    unfolding i_def 
    apply (rule comp_inj_on, fact \<open>inj_on i0 D0\<close>)
    unfolding D1_def[symmetric]
    apply (rule comp_inj_on, fact \<open>inj_on i1 D1\<close>)
    unfolding D2_def[symmetric]
    apply (rule comp_inj_on, fact \<open>inj_on i2 D2\<close>)
    unfolding D3_def[symmetric]
    by (fact \<open>inj_on i3 D3\<close>)
      
  have i_D0: "i ` D0 = D4" 
    unfolding D4_def D3_def D2_def D1_def i_def by auto
      
  show ?thesis
    apply (rule exI[of _ i])
    using D0_def inj_i i_D0 D4
    by auto
qed
  
lemma universe_powertower_disjoint: "x \<in> universe_powertower n \<Longrightarrow> x \<in> universe_powertower m \<Longrightarrow> n=m"
  using type_definition.Abs_inject type_definition_universe universe_powertower_def by fastforce
  
lemma universe_powertower_nat: "\<exists>n (i::nat\<Rightarrow>universe). inj i \<and> range i \<subseteq> universe_powertower n"
proof - 
  define i where "i m = Abs_universe (nat2Nat m, 0)" for m
  have "inj i" 
    apply (rule injI) unfolding i_def
    apply (subst (asm) Abs_universe_inject)
      apply (simp add: Elem_nat2Nat_inf)
     apply (simp add: Elem_nat2Nat_inf)
    by (meson injD inj_nat2Nat old.prod.inject)
      
  moreover have "range i \<subseteq> universe_powertower 0"
    unfolding universe_powertower_def i_def by auto
      
  ultimately show ?thesis
    by auto
qed
  
lemma universe_powertower_all: "(\<Union>n. universe_powertower n) = UNIV"
  unfolding universe_powertower_def
  apply auto
  by (smt Rep_universe Rep_universe_inverse mem_Collect_eq)


instantiation universe :: equal begin
definition "equal_universe (v::universe) w = (v=w)"
instance apply intro_classes
  by (simp add: equal_universe_def)
end

(* definition "small_cardinal (_::'a itself) = (\<exists>t n (i::'a\<Rightarrow>universe). powertower t \<and> inj i \<and> range i \<subseteq> t n)" *)

class "universe" = default +
  fixes embedding' :: "('a \<Rightarrow> universe) \<times> nat"
  assumes embedding'_range: "range (fst embedding') \<subseteq> universe_powertower (snd embedding')"
  assumes inj_embedding': "inj (fst embedding')"
  (* assumes small_cardinal: "\<exists>t n. powertower t \<and> range embedding \<subseteq> t n" *)

definition embedding'_default :: "('a\<Rightarrow>universe) \<times> nat" where 
  "embedding'_default == (SOME fn. inj (fst fn) \<and> range (fst fn) \<subseteq> universe_powertower (snd fn))"

definition "embedding = fst embedding'" 
(* definition embedding :: "'a::universe \<Rightarrow> universe" where
  "embedding == (SOME f::'a\<Rightarrow>universe. inj f)" *)

syntax "_type_embedding" :: "type => ('a::universe\<Rightarrow>universe)" ("(1EMBEDDING/(1'(_')))")

translations "EMBEDDING('t)" => "CONST embedding :: 't::universe\<Rightarrow>universe"

lemma embedding_inv [simp]: "(embedding x = embedding y) = (x = y)"
  using inj_embedding' unfolding embedding_def inj_on_def by auto

lemma embedding_inv' [simp]: "inv embedding (embedding x) = x"
  by (metis embedding_inv f_inv_into_f range_eqI)
  
type_synonym 'a universe_embedding = "('a\<Rightarrow>universe)\<times>nat"

instantiation "nat" :: "universe" begin
definition "(embedding'::nat universe_embedding) = embedding'_default"
instance proof (intro_classes, goal_cases)
case 1
  let ?e = "embedding'::nat universe_embedding"
  from universe_powertower_nat obtain f::"nat\<Rightarrow>universe" and n where inj: "inj f" and range: "range f \<subseteq> universe_powertower n" by auto
  have theses: "inj (fst ?e) \<and> range (fst ?e) \<subseteq> universe_powertower (snd ?e)"
    unfolding embedding'_nat_def embedding'_default_def 
    apply (rule someI[where P="\<lambda>fn. inj (fst fn) \<and> range (fst fn) \<subseteq> universe_powertower (snd fn)" and x="(f,n)"])
    using inj range by auto
  thus ?case by simp
case 2 show ?case using theses by simp
qed
end

lemma universe_classI':
  assumes "inj (f::'a\<Rightarrow>'b::universe)"
  shows "range (fst (embedding'_default::'a universe_embedding)) \<subseteq> universe_powertower (snd (embedding'_default::'a universe_embedding))" and "inj (fst (embedding'_default::'a universe_embedding))"
proof -
(*   obtain n where range: "range (embedding::'b\<Rightarrow>universe) \<subseteq> universe_powertower n"
    using embedding_range by auto *)
  let ?e = "(\<lambda>x. fst embedding' (f x), snd (embedding'::'b universe_embedding))"
  let ?e' = "embedding'_default :: 'a universe_embedding"
  have theses: "inj (fst ?e) \<and> range (fst ?e) \<subseteq> universe_powertower (snd ?e)"
    using assms[THEN injD] embedding'_range inj_embedding'[THEN injD] unfolding inj_on_def apply auto by blast
  have "inj (fst ?e') \<and> range (fst ?e') \<subseteq> universe_powertower (snd ?e')"
    unfolding embedding'_default_def 
    apply (rule someI[where P="\<lambda>f. inj (fst f) \<and> range (fst f) \<subseteq> universe_powertower (snd f)"])
    by (fact theses)
  then show "range (fst ?e') \<subseteq> universe_powertower (snd (embedding'_default::'a universe_embedding))" 
       and "inj (fst (embedding'_default::'a universe_embedding))"
     by auto
qed

(* Hack to allow to state lemma universe_classI. Is there a cleaner way? *)
ML \<open>
  val consts_to_unconstrain = [\<^const_name>\<open>embedding'\<close>]
  val consts_orig_constraints = map (Sign.the_const_constraint \<^theory>) consts_to_unconstrain
\<close>
setup \<open>
  fold (fn c => fn thy => Sign.add_const_constraint (c,NONE) thy) consts_to_unconstrain
\<close>

lemma universe_classI:
  assumes emb: "(embedding'::'a universe_embedding) = embedding'_default"
  assumes inj: "inj (f::'a\<Rightarrow>'b::universe)"
  shows "OFCLASS('a, universe_class)"
apply intro_classes using universe_classI'[OF inj] unfolding emb by auto

(* Recover stored type constraints *)
setup \<open>
  fold2 (fn c => fn T => fn thy => Sign.add_const_constraint (c,SOME (Logic.unvarifyT_global T)) thy)
      consts_to_unconstrain consts_orig_constraints
\<close>

definition universe_powertower_level :: "universe \<Rightarrow> nat" where
  "universe_powertower_level x = (SOME n. x \<in> universe_powertower n)"
lemma universe_powertower_level: "x \<in> universe_powertower (universe_powertower_level x)"
  unfolding universe_powertower_level_def apply (rule someI_ex)
  using universe_powertower_all by auto

definition val_set_embedding :: "nat \<Rightarrow> universe set \<Rightarrow> universe" where
  "val_set_embedding n = (SOME f. inj_on f (Pow (universe_powertower n)) \<and> f ` Pow (universe_powertower n) \<subseteq> universe_powertower (Suc n))"
(* definition val_set_embedding_level :: "nat \<Rightarrow> nat" where
  "val_set_embedding_level n == (SOME m. \<forall>x. x \<subseteq> universe_powertower n \<longrightarrow> val_set_embedding x \<in> universe_powertower m)" *)

lemma val_set_embedding_inj: "inj_on (val_set_embedding n) (Pow (universe_powertower n))" (is ?thesis1)
  and val_set_embedding_range: "x \<subseteq> universe_powertower n \<Longrightarrow> (val_set_embedding n) x \<in> universe_powertower (Suc n)" (is "PROP ?thesis2")
proof -
  obtain f where "inj_on f (Pow (universe_powertower n)) \<and> f ` Pow (universe_powertower n) \<subseteq> universe_powertower (Suc n)"
    apply atomize_elim using universe_powertower by simp
  hence "inj_on f (Pow (universe_powertower n)) \<and> f ` Pow (universe_powertower n) \<subseteq> universe_powertower (Suc n)"
    by auto
  hence "inj_on (val_set_embedding n) (Pow (universe_powertower n)) \<and> (val_set_embedding n) ` Pow (universe_powertower n) \<subseteq> universe_powertower (Suc n)"
    unfolding val_set_embedding_def by (rule someI[where P="\<lambda>f. inj_on f (Pow (universe_powertower n)) \<and> f ` Pow (universe_powertower n) \<subseteq> universe_powertower (Suc n)"])
  thus ?thesis1 and "PROP ?thesis2" by auto
qed

instantiation set :: ("universe") "universe" begin
definition "(embedding' :: 'a set universe_embedding) = 
  (\<lambda>M. val_set_embedding (snd (embedding'::'a universe_embedding)) (fst (embedding'::'a universe_embedding) ` M), 
        Suc (snd (embedding'::'a universe_embedding)))"
instance proof
  let ?ea = "embedding' :: 'a universe_embedding"
  let ?e = "embedding' :: 'a set universe_embedding"
  show "range (fst ?e) \<subseteq> universe_powertower (snd ?e)"
    unfolding embedding'_set_def apply auto
    apply (rule val_set_embedding_range[where n="snd ?ea"])
    using embedding'_range by auto
  show "inj (fst ?e)"
    unfolding embedding'_set_def  
    apply simp apply (rule injI)
    apply (frule val_set_embedding_inj[THEN inj_onD])
      using embedding'_range image_subsetI apply auto[2]
    using inj_embedding'[THEN injD] by auto
qed
end

(*instantiation set :: (universe) universe begin
definition "(embedding :: 'a set \<Rightarrow> universe) = embedding_default"
instance proof
  obtain n where range: "range (embedding::'a\<Rightarrow>universe) \<subseteq> universe_powertower n"
    using embedding_range by auto

  obtain i2::"universe set\<Rightarrow>universe" where i2inj: "inj_on i2 (Pow (universe_powertower n))" 
                                       and i2rng: "i2 ` Pow(universe_powertower n) \<subseteq> universe_powertower (Suc n)"
    using universe_powertower by blast
  define i3 where "i3 \<equiv> \<lambda>s::'a set. i2 (embedding ` s)"
  have "inj i3"
  proof (rule injI, unfold i3_def)
    fix x y :: "'a set"
    from inj_embedding have i: "embedding ` x = embedding ` y \<Longrightarrow> x = y"
      by (metis inj_image_eq_iff)
    show "i2 (embedding ` x) = i2 (embedding ` y) \<Longrightarrow> x = y"
      apply (rule i)
      apply (subst inj_on_eq_iff[symmetric, where f=i2 and A="Pow(universe_powertower n)"])
      using i2inj range by auto
  qed
  have i3rng: "range i3 \<subseteq> universe_powertower (Suc n)"
  proof (unfold i3_def, auto)
    fix s :: "'a set"
    have "embedding ` s \<in> Pow (universe_powertower n)" using range by auto
    hence "i2 (embedding ` s) \<in> i2 ` (Pow (universe_powertower n))" by auto
    with i2rng show "i2 (embedding ` s) \<in> universe_powertower (Suc n)" by auto
  qed

  let ?e = "embedding::'a set\<Rightarrow>_"
  have ex_emb: "inj i3 \<and> (\<exists>n. range i3 \<subseteq> universe_powertower n)"
    using i3rng `inj i3` by auto
  have "inj ?e \<and> (\<exists>n. range ?e \<subseteq> universe_powertower n)"
    unfolding embedding_set_def embedding_default_def 
    apply (rule someI[where P="\<lambda>f. inj f \<and> (\<exists>n. range f \<subseteq> universe_powertower n)"])
    using ex_emb by simp
  (* thus "inj (embedding::'a set \<Rightarrow> universe)" by simp *)
  thus "\<exists>n. range (embedding::'a set\<Rightarrow>universe) \<subseteq> universe_powertower n"
   and "inj (embedding::'a set\<Rightarrow>universe)"  by auto
qed
end*)

instantiation bool :: "universe" begin
definition "(embedding' :: bool universe_embedding) = embedding'_default"
instance apply (rule universe_classI[OF embedding'_bool_def, of "\<lambda>b. if b then 0 else Suc 0"])
  apply (rule injI)
  by (case_tac x, case_tac y, auto)
end

(* TODO needed? *)
lemma ordered_cardinals: "(\<exists>i::'a\<Rightarrow>'b. inj i) \<or> (\<exists>j::'b\<Rightarrow>'a. inj j)"
proof -
  have leq: "ordLeq2 (card_of (Inl ` UNIV :: ('a+'b)set)) (card_of (Inr ` UNIV :: ('a+'b)set)) \<or>
        ordLeq2 (card_of (Inr ` UNIV :: ('a+'b)set)) (card_of (Inl ` UNIV :: ('a+'b)set))"
        by (rule ordLeq_total, rule card_of_Well_order, rule card_of_Well_order)
  show ?thesis proof (rule leq[THEN disjE], fold card_of_ordLeq)
    assume "\<exists>f::'a+'b \<Rightarrow> 'a+'b. inj_on f (range Inl) \<and> f ` range Inl \<subseteq> range Inr"
    then obtain f::"'a+'b \<Rightarrow> 'a+'b" where finj: "inj_on f (range Inl)" and frng: "f ` range Inl \<subseteq> range Inr" by auto
    define i where "i == \<lambda>x. case f (Inl x) of Inr y \<Rightarrow> y"
    have "inj i" proof (rule injI, unfold i_def) 
      fix x y assume eq:"(case f (Inl x) of Inr y \<Rightarrow> y) = (case f (Inl y) of Inr y \<Rightarrow> y)"
      from frng obtain x' where x': "f (Inl x) = Inr x'" by blast
      from frng obtain y' where y': "f (Inl y) = Inr y'" by blast
      from eq have "f (Inl x) = f (Inl y)" unfolding x' y' by simp
      with finj have "Inl x = Inl y" unfolding inj_on_def by simp
      thus "x = y" by auto
    qed
    thus ?thesis by auto
  next
    assume "\<exists>f::'a+'b \<Rightarrow> 'a+'b. inj_on f (range Inr) \<and> f ` range Inr \<subseteq> range Inl"
    then obtain f::"'a+'b \<Rightarrow> 'a+'b" where finj: "inj_on f (range Inr)" and frng: "f ` range Inr \<subseteq> range Inl" by auto
    define j where "j == \<lambda>x. case f (Inr x) of Inl y \<Rightarrow> y"
    have "inj j" proof (rule injI, unfold j_def) 
      fix x y assume eq:"(case f (Inr x) of Inl y \<Rightarrow> y) = (case f (Inr y) of Inl y \<Rightarrow> y)"
      from frng obtain x' where x': "f (Inr x) = Inl x'" by blast
      from frng obtain y' where y': "f (Inr y) = Inl y'" by blast
      from eq have "f (Inr x) = f (Inr y)" unfolding x' y' by simp
      with finj have "Inr x = Inr y" unfolding inj_on_def by simp
      thus "x = y" by auto
    qed
    thus ?thesis by auto
  qed
qed

function val_embed_up :: "nat \<Rightarrow> nat \<Rightarrow> universe \<Rightarrow> universe" where
  "val_embed_up n n x = x"
| "m > n \<Longrightarrow> val_embed_up n m x = val_set_embedding (m-1) {val_embed_up n (m-1) x}"
| "m < n \<Longrightarrow> val_embed_up n m x = undefined"
apply auto apply atomize_elim by auto
termination by lexicographic_order


lemma range_val_embed_up: 
  "m\<ge>n \<Longrightarrow> x \<in> universe_powertower n \<Longrightarrow> val_embed_up n m x \<in> universe_powertower m"
proof (induction "m-n" arbitrary: m)
case 0 thus ?case by simp
next case (Suc m_n)
  from Suc have "m > n" by auto
  hence m: "m = Suc (m - Suc 0)" by auto
  show ?case
    apply (simp add: \<open>m > n\<close>)
    apply (subst m, rule val_set_embedding_range)
    using Suc by simp
qed

lemma inj_val_embed_up: 
  "m\<ge>n \<Longrightarrow> val_embed_up n m x = val_embed_up n m y \<Longrightarrow>
       x \<in> universe_powertower n \<Longrightarrow> y \<in> universe_powertower n \<Longrightarrow> x = y"
proof (induction "m-n" arbitrary: m)
case 0 thus ?case by simp
next case (Suc m_n)
  from Suc have "m > n" by auto
  with Suc.prems have set: "val_set_embedding (m-1) {val_embed_up n (m-1) x} = val_set_embedding (m-1) {val_embed_up n (m-1) y}" by auto
  have "{val_embed_up n (m-1) x} = {val_embed_up n (m-1) y}"
    apply (rule val_set_embedding_inj[THEN inj_onD, of "m-1"])
      using set apply auto[1]
    using range_val_embed_up Suc.hyps Suc.prems by auto
  with Suc.hyps(1)[of "m-1"] show ?case apply auto
    by (metis One_nat_def Suc.hyps(2) Suc.prems(3) Suc.prems(4) Suc_diff_Suc \<open>n < m\<close> diff_Suc_1 le_add1 less_imp_Suc_add)
qed

definition val_sum_embedding :: "nat \<Rightarrow> nat \<Rightarrow> universe+universe \<Rightarrow> universe" where
  "val_sum_embedding n m x = (let mn = prod_encode (n,m) in val_set_embedding (Suc mn) (val_set_embedding mn ` 
      (case x of Inl a \<Rightarrow> {{val_embed_up n mn a}} | Inr b \<Rightarrow> {{val_embed_up m mn b},{}})))"
lemma inj_val_sum_embedding: "inj_on (val_sum_embedding n m) (universe_powertower n <+> universe_powertower m)"
  and range_val_sum_embedding: "x \<in> universe_powertower n <+> universe_powertower m 
              \<Longrightarrow> val_sum_embedding n m x \<in> universe_powertower (prod_encode (n,m) + 2)"
proof -
  have range2: "\<And>x. x \<in> universe_powertower n <+> universe_powertower m \<Longrightarrow>
           (case x of Inl a \<Rightarrow> {{val_embed_up n (prod_encode(n,m)) a}} | Inr b \<Rightarrow> {{val_embed_up m (prod_encode(n,m)) b}, {}})
           \<subseteq> Pow (universe_powertower (prod_encode(n,m)))" 
    apply auto 
    apply (rule range_val_embed_up, auto intro: le_prod_encode_1)
    by (rule range_val_embed_up, auto intro: le_prod_encode_2)
  have range1: "\<And>x. x \<in> universe_powertower n <+> universe_powertower m \<Longrightarrow>
           val_set_embedding (prod_encode(n,m)) `
           (case x of Inl a \<Rightarrow> {{val_embed_up n (prod_encode(n,m)) a}} 
                   | Inr b \<Rightarrow> {{val_embed_up m (prod_encode(n,m)) b}, {}})
           \<in> Pow (universe_powertower (Suc (prod_encode(n,m))))" 
    apply (simp add: image_subset_iff, rule ballI)
    apply (rule val_set_embedding_range)
    using range2 by auto
  have range2: "(case x of Inl a \<Rightarrow> {{val_embed_up n (prod_encode(n,m)) a}} 
                         | Inr b \<Rightarrow> {{val_embed_up m (prod_encode(n,m)) b}, {}})
                   \<subseteq> Pow (universe_powertower (prod_encode(n,m)))" 
           if "x \<in> universe_powertower n <+> universe_powertower m" for x
    apply (cases x; simp)
     apply (rule range_val_embed_up) using le_prod_encode_1 that apply auto[2]
    apply (rule range_val_embed_up) using le_prod_encode_2 that by auto
  have inj1: "\<And>xa xb. val_embed_up n (prod_encode(n,m)) xa = val_embed_up n (prod_encode(n,m)) xb \<Longrightarrow>
             xa \<in> universe_powertower n \<Longrightarrow> xb \<in> universe_powertower n \<Longrightarrow> xa = xb" using inj_val_embed_up
    using le_prod_encode_1 by blast
  have inj2: "\<And>ya yb. {{val_embed_up m (prod_encode(n,m)) ya}, {}} = {{val_embed_up m (prod_encode(n,m)) yb}, {}} \<Longrightarrow>
             ya \<in> universe_powertower m \<Longrightarrow> yb \<in> universe_powertower m \<Longrightarrow> ya = yb"
    by (metis doubleton_eq_iff inj_val_embed_up le_prod_encode_2)
  show "val_sum_embedding n m x \<in> universe_powertower (prod_encode(n,m) + 2)"
          if "x \<in> universe_powertower n <+> universe_powertower m" 
    unfolding val_sum_embedding_def Let_def apply simp
    apply (rule val_set_embedding_range)
    apply (rule image_subset_iff[THEN iffD2, rule_format])
    apply (rule val_set_embedding_range)
    apply (cases x, auto)
     apply (rule range_val_embed_up) using le_prod_encode_1 that apply auto[2]
    apply (rule range_val_embed_up) using le_prod_encode_2 that by auto
  show "inj_on (val_sum_embedding n m) (universe_powertower n <+> universe_powertower m)"
    apply (rule inj_onI) unfolding val_sum_embedding_def Let_def
    apply (subst (asm) val_set_embedding_inj[THEN inj_on_eq_iff])
      apply (rule range1, simp)
     apply (rule range1, simp)
    apply (subst (asm) val_set_embedding_inj[THEN inj_on_image_eq_iff])
      apply (rule range2, simp)
     apply (rule range2, simp)
    by (auto intro: inj1 inj2)
qed

instantiation sum :: ("universe","universe") "universe" begin
definition "(embedding' :: ('a+'b) universe_embedding) = 
  (\<lambda>x. val_sum_embedding (snd (embedding'::'a universe_embedding)) (snd (embedding'::'b universe_embedding))
    (map_sum (fst embedding') (fst embedding') x), 
  prod_encode (snd (embedding'::'a universe_embedding), snd (embedding'::'b universe_embedding)) + 2)"
instance proof (intro_classes, goal_cases)
case 1
  show ?case unfolding embedding'_sum_def 
    apply auto apply (rule range_val_sum_embedding[simplified])
    apply (case_tac xa) using embedding'_range by auto
case 2
  show ?case unfolding embedding'_sum_def
    apply (rule injI) apply simp 
    apply (drule_tac inj_val_sum_embedding[THEN inj_onD])
    unfolding map_sum_def
      apply (case_tac x; auto intro!: embedding'_range[unfolded image_subset_iff, rule_format]) 
     apply (case_tac y; auto intro!: embedding'_range[unfolded image_subset_iff, rule_format]) 
    apply (case_tac x; case_tac y; simp)
    using inj_embedding'[THEN injD] by auto
qed
end

(*instantiation sum :: (universe,universe) universe begin
instance proof (intro_classes, cases "\<exists>i::'a\<Rightarrow>'b. inj i")
case True
  then obtain i::"'a\<Rightarrow>'b" where "inj i" by auto
  define i2 where "i2 \<equiv> \<lambda>x::'a+'b. case x of Inl a \<Rightarrow> {{i a}} | Inr b \<Rightarrow> {{b},{}}"
  have "inj i2" apply (rule injI) unfolding i2_def 
    apply (case_tac x, case_tac y, auto)
    apply (metis `inj i` inj_eq)
    by (case_tac y, auto)
  hence "\<exists>f::'a+'b\<Rightarrow>'b set set. inj f"
    by (rule exI[of _ i2])
  thus "\<exists>t n (i::'a+'b\<Rightarrow>universe). powertower t \<and> inj i \<and> range i \<subseteq> t n"
    by (rule universe_classI')
next 
case False
  with ordered_cardinals obtain i::"'b\<Rightarrow>'a" where "inj i" by auto
  define i2 where "i2 \<equiv> \<lambda>x::'a+'b. case x of Inl a \<Rightarrow> {{a},{}} | Inr b \<Rightarrow> {{i b}}"
  have "inj i2" apply (rule injI) unfolding i2_def 
    apply (case_tac x, case_tac y, auto)
    apply (case_tac y, auto)
    by (metis `inj i` inj_eq)
  hence "\<exists>f::'a+'b\<Rightarrow>'a set set. inj f"
    by (rule exI[of _ i2])
  thus "\<exists>t n (i::'a+'b\<Rightarrow>universe). powertower t \<and> inj i \<and> range i \<subseteq> t n"
    by (rule universe_classI')
qed
end*)

definition val_prod_embedding' :: "nat \<Rightarrow> nat \<Rightarrow> universe*universe \<Rightarrow> universe" where
  "val_prod_embedding' n m x = val_set_embedding (prod_encode(n,m) + 2) (val_sum_embedding n m ` {Inl (fst x), Inr (snd x)})"
lemma inj_val_prod_embedding': "inj_on (val_prod_embedding' n m) (universe_powertower n \<times> universe_powertower m)" (is ?inj)
  and range_val_prod_embedding': "x \<in> universe_powertower n \<times> universe_powertower m \<Longrightarrow> val_prod_embedding' n m x \<in> universe_powertower (prod_encode(n,m) + 3)" (is "?assm \<Longrightarrow> ?range")
proof -
  have range1: "val_sum_embedding n m ` {Inl (fst x), Inr (snd x)} \<in> Pow (universe_powertower (prod_encode (n, m) + 2))" 
               if "x \<in> universe_powertower n \<times> universe_powertower m" for x
    apply auto
     apply (rule range_val_sum_embedding[simplified])
     using that apply auto[1]
    apply (rule range_val_sum_embedding[simplified])
    using that by auto
  have inj1: "inj_on (val_sum_embedding n m) ({Inl (fst x), Inr (snd x)} \<union> {Inl (fst y), Inr (snd y)})" 
             if "x \<in> universe_powertower n \<times> universe_powertower m" and "y \<in> universe_powertower n \<times> universe_powertower m" for x y
    apply (rule inj_onI)
    apply (drule inj_val_sum_embedding[THEN inj_onD])
    using that by auto
  show ?inj
    apply (rule inj_onI)
    unfolding val_prod_embedding'_def
    apply (drule val_set_embedding_inj[THEN inj_onD])
      using range1 apply auto[2]
    apply (subst (asm) inj_on_Un_image_eq_iff[where f="val_sum_embedding n m"])
     using inj1 apply auto[1]
    by force
  assume ?assm
  show ?range
    unfolding val_prod_embedding'_def
    apply (rewrite at "_ + 3" to "Suc (_ + 2)" eq_reflection) apply auto[1]
    apply (rule val_set_embedding_range)
    using range1[OF `?assm`] by auto
qed

definition val_prod_embedding :: "universe\<times>universe \<Rightarrow> universe" where
  "val_prod_embedding xy = val_prod_embedding' (universe_powertower_level (fst xy)) (universe_powertower_level (snd xy)) xy"
(* Could be made injective on all universe\<times>universe, by fixing a monotone nat\<Rightarrow>nat\<Rightarrow>nat: prod_encode *)
lemma inj_val_prod_embedding: "inj val_prod_embedding"
proof (rule injI)
  fix x y :: "universe\<times>universe"
  assume emb_eq: "val_prod_embedding x = val_prod_embedding y"

  obtain x1 x2 where x: "x=(x1,x2)" by (atomize_elim, auto)
  define n1 n2 
    where "n1 == universe_powertower_level x1"
      and "n2 == universe_powertower_level x2"
  have "x1 \<in> universe_powertower n1"  
   and "x2 \<in> universe_powertower n2" unfolding n1_def n2_def by (simp_all add: universe_powertower_level) 
  hence x_tower: "x \<in> universe_powertower n1 \<times> universe_powertower n2" unfolding x by auto
  hence emb_x: "val_prod_embedding' n1 n2 x \<in> universe_powertower (prod_encode(n1,n2) + 3)"
    by (rule range_val_prod_embedding')

  obtain y1 y2 where y: "y=(y1,y2)" by (atomize_elim, auto)
  define m1 m2
    where "m1 == universe_powertower_level y1"
      and "m2 == universe_powertower_level y2"
  have "y1 \<in> universe_powertower m1"  
   and "y2 \<in> universe_powertower m2" unfolding m1_def m2_def by (simp_all add: universe_powertower_level) 
  hence y_tower: "y \<in> universe_powertower m1 \<times> universe_powertower m2" unfolding y by auto
  hence emb_y: "val_prod_embedding' m1 m2 y \<in> universe_powertower (prod_encode(m1,m2) + 3)"
    by (rule range_val_prod_embedding')

  have emb_eq': "val_prod_embedding' n1 n2 x = val_prod_embedding' m1 m2 y"
    using emb_eq unfolding val_prod_embedding_def x y n1_def n2_def m1_def m2_def
    by simp

  from emb_x emb_y have "prod_encode(n1,n2) + 3 = prod_encode(m1,m2) + 3"
    unfolding emb_eq' by (rule universe_powertower_disjoint)
  hence eq1: "n1 = m1" and eq2: "n2 = m2"
    by (simp_all add: prod_encode_eq) 

  show "x=y"
    apply (rule inj_val_prod_embedding'[THEN inj_onD])
    using emb_eq' eq1 eq2 x_tower y_tower by auto
qed

lemma range_val_prod_embedding: 
  assumes "x \<in> universe_powertower n \<times> universe_powertower m"
  shows "val_prod_embedding x \<in> universe_powertower (prod_encode(n,m) + 3)"
proof -
  obtain x1 x2 where x: "x=(x1,x2)" by (atomize_elim,auto)
  have n: "n = universe_powertower_level x1"
    using assms unfolding x
    using universe_powertower_disjoint universe_powertower_level by auto
  have m: "m = universe_powertower_level x2"
    using assms unfolding x
    using universe_powertower_disjoint universe_powertower_level by auto
  show ?thesis
    unfolding val_prod_embedding_def 
    using range_val_prod_embedding'[OF assms] 
    unfolding x n m by simp
qed

instantiation prod :: ("universe","universe") "universe" begin
definition "(embedding' :: ('a\<times>'b) universe_embedding) = 
  (\<lambda>x. val_prod_embedding (map_prod (fst embedding') (fst embedding') x), 
  prod_encode (snd (embedding'::'a universe_embedding), snd (embedding'::'b universe_embedding)) + 3)"
instance proof
  let ?e = "embedding'::('a\<times>'b)universe_embedding"
  show "range (fst ?e) \<subseteq> universe_powertower (snd ?e)"
    apply auto unfolding embedding'_prod_def apply simp
    apply (rule range_val_prod_embedding) apply auto
    using embedding'_range by auto
  show "inj (fst ?e)"
    apply (rule injI)
    unfolding embedding'_prod_def apply simp
    apply (frule inj_val_prod_embedding[THEN injD])
    by (auto simp: inj_embedding' inj_eq)
qed
end

instantiation "fun" :: ("universe","universe")"universe" begin
definition "(embedding' :: ('a\<Rightarrow>'b) universe_embedding) = embedding'_default"
instance apply (rule universe_classI[OF embedding'_fun_def, of "\<lambda>f. {(x,f x)| x. True}"])
  by (rule injI, auto)
end

(* instantiation list :: ("universe") "universe" begin
definition "(embedding' :: 'a list universe_embedding) = embedding'_default"
instance apply (rule universe_classI[OF embedding'_list_def, of "\<lambda>l. (length l, nth l)"])
  by (rule injI, metis nth_equalityI old.prod.inject)
end *)

local_setup \<open>
  Local_Theory.define ((\<^binding>\<open>embedding'_UNCONSTRAINED\<close>,NoSyn),((\<^binding>\<open>embedding'_UNCONSTRAINED_def\<close>,[]),
      Const(\<^const_name>\<open>embedding'\<close>,\<^typ>\<open>'a universe_embedding\<close>))) #> snd
\<close>

lemma OFCLASS_universe_typedef[unfolded embedding'_UNCONSTRAINED_def]:
  fixes Rep::"'a\<Rightarrow>'b::universe"
  assumes emb: "(embedding'_UNCONSTRAINED :: 'a universe_embedding) \<equiv> (fst embedding' o Rep, snd (embedding'::'b universe_embedding))"
  assumes inj: "\<And>x y. (Rep x = Rep y) = (x = y)" 
  shows "OFCLASS('a,universe_class)"
proof (intro_classes, fold embedding'_UNCONSTRAINED_def)
  let ?e = "embedding'_UNCONSTRAINED :: 'a universe_embedding"
  show "range (fst ?e) \<subseteq> universe_powertower (snd ?e)"
    unfolding emb apply simp using embedding'_range by auto
  have "inj Rep" apply (rule injI) using inj by simp
  show "inj (fst ?e)"
    unfolding emb using inj inj_embedding' `inj Rep` by (auto intro: inj_compose)
qed


subsection "Automatically instantiate new types using @{command derive}"

(* datatype 'a::finite xxx = XXX 'a 
typedef 'a::finite y = "UNIV :: 'a set" by simp
datatype z = Z "(int+int) xxx"
typedef zz = "UNIV :: int set" by simp
typedef ('a,'b) t = "UNIV :: 'a set" by simp *)

ML_file "universe.ML"

setup \<open>Derive_Manager.register_derive "universe" "Instantiates the given type with sort universe" Universe.generate_universe_cmd\<close>

(* declare[[show_sorts]]
(* term "Rep_y" *)
derive universe t
ML \<open>
Sign.arity_sorts \<^theory> \<^type_name>\<open>t\<close> \<^sort>\<open>universe\<close>
|> map (Syntax.string_of_sort \<^context>) |> map writeln
\<close>
 *)

(* setup {* Typedef.interpretation (Local_Theory.background_theory o Universe.try_instantiate_universe) *} *)

derive universe int
derive universe unit
derive universe list
derive universe char
derive universe tuple_isomorphism
derive universe integer
derive universe property_pre_property_bdT
derive universe sumbool
derive universe Enum.finite_1 Enum.finite_2 Enum.finite_3 Enum.finite_4 Enum.finite_5
derive universe "Code_Evaluation.term"
derive universe String.literal
derive universe typerep
derive universe num
derive universe natural
derive universe Quickcheck_Exhaustive.three_valued
derive universe lazy_sequence
derive universe property_pre_property
derive universe Quickcheck_Narrowing.cfun
derive universe Quickcheck_Exhaustive.unknown
derive universe option
derive universe Predicate.pred
derive universe Nitpick.word
derive universe Predicate.seq
derive universe filter
derive universe Quickcheck_Narrowing.ffun
derive universe Nitpick.pair_box
derive universe Nitpick.fun_box

ML \<open> (* Lists all types that are not declared as sort universe *)
\<^context>
|> Proof_Context.tsig_of
|> Type.rep_tsig
|> #log_types
|> app (fn tn => (Proof_Context.arity_sorts \<^context> tn @{sort universe}; ()) 
    handle ERROR _ => tracing ("NO: "^Syntax.string_of_typ \<^context> (Type(tn,[]))^"    "^tn))
\<close>


end
