theory Classical_Registers
  imports Registers.Classical_Extra
    Misc_Missing
begin

subsection \<open>Raw\<close>

type_synonym 'a cupdate = \<open>'a \<Rightarrow> 'a option\<close>

abbreviation \<open>cregister_raw \<equiv> Axioms_Classical.register\<close>

lemma cregister_raw_empty: \<open>cregister_raw F \<Longrightarrow> F Map.empty = Map.empty\<close>
  by (simp add: register_empty)
lemma cregister_raw_1: \<open>cregister_raw F \<Longrightarrow> F Some = Some\<close>
  by simp

definition non_cregister_raw :: \<open>'a cupdate \<Rightarrow> 'b cupdate\<close> where \<open>non_cregister_raw a = Map.empty\<close>

lemma cregister_raw_inj: \<open>inj_on F X\<close> if \<open>cregister_raw F\<close>
proof -
  note [[simproc del: Laws_Classical.compatibility_warn]]
  define get set where \<open>get = Axioms_Classical.getter F\<close> and \<open>set = Axioms_Classical.setter F\<close>
  have get_set: \<open>get (set a b) = a\<close> and set_set: \<open>set a (set a' b) = set a b\<close> for a a' b
     apply (metis get_def local.set_def that valid_getter_setter_def valid_getter_setter_getter_setter)
    by (metis local.set_def that valid_getter_setter_def valid_getter_setter_getter_setter)
  fix b
  define G :: \<open>'b Axioms_Classical.update \<Rightarrow> 'a Axioms_Classical.update\<close> 
    where \<open>G g a = map_option get (g (set a b))\<close> for g a
  have \<open>G (F f) a = f a\<close> for f a
    apply (subst register_from_getter_setter_of_getter_setter[OF that, symmetric])
    unfolding G_def 
    apply (cases \<open>f a\<close>)
    by (simp_all add: register_from_getter_setter_def[abs_def] set_set get_set
        del: register_from_getter_setter_of_getter_setter
        flip: get_def set_def)
  then show \<open>inj_on F X\<close>
    by (metis ext inj_onI)
qed


lemma non_cregister_raw: \<open>\<not> cregister_raw non_cregister_raw\<close>
  by (metis cregister_raw_1 non_cregister_raw_def not_Some_eq)

subsection \<open>Registers\<close>


typedef ('a,'b) cregister = \<open>{f :: 'a cupdate \<Rightarrow> 'b cupdate. cregister_raw f} \<union> {non_cregister_raw}\<close>
  morphisms apply_cregister Abs_cregister by auto
setup_lifting type_definition_cregister


lift_definition apply_cregister_total :: \<open>('a,'b) cregister \<Rightarrow> ('a\<Rightarrow>'a) \<Rightarrow> ('b\<Rightarrow>'b)\<close> is
  \<open>\<lambda>F f. the o F (Some o f)\<close>.

lift_definition non_cregister :: \<open>('a,'b) cregister\<close> is non_cregister_raw by auto

lift_definition cregister :: \<open>('a,'b) cregister \<Rightarrow> bool\<close> is cregister_raw.

lemma non_cregister: \<open>\<not> cregister F \<longleftrightarrow> F = non_cregister\<close>
  apply transfer using non_cregister_raw by blast

lemma non_cregister'[simp]: \<open>\<not> cregister non_cregister\<close>
  by (simp add: non_cregister)

lemma apply_cregister_of_0[simp]: \<open>apply_cregister F Map.empty = Map.empty\<close>
  apply transfer apply (auto simp: non_cregister_raw_def)
  by (simp add: cregister_raw_empty)

lemma apply_cregister_of_id[simp]: \<open>cregister F \<Longrightarrow> apply_cregister F Some = Some\<close>
  using cregister.rep_eq cregister_raw_1 by blast

lemma cregister_partial_fun_compatible:
  assumes \<open>cregister F\<close>
  assumes \<open>partial_fun_compatible f g\<close>
  shows \<open>partial_fun_compatible (apply_cregister F f) (apply_cregister F g)\<close>
proof -
  have [simp]: \<open>cregister_raw (apply_cregister F)\<close>
    using assms(1) cregister.rep_eq by auto
  show \<open>partial_fun_compatible (apply_cregister F f) (apply_cregister F g)\<close>
    apply (subst (2) register_from_getter_setter_of_getter_setter[symmetric], simp)
    apply (subst register_from_getter_setter_of_getter_setter[symmetric], simp)
    using assms(2)
    apply (auto simp add: register_from_getter_setter_def[abs_def] partial_fun_compatible_def
        simp del: register_from_getter_setter_of_getter_setter
        split: option.split)
    by (metis option.sel option.simps(3))
qed
(* (* IFF version *)
lemma cregister_partial_fun_compatible:
  assumes \<open>cregister F\<close>
  shows \<open>partial_fun_compatible (apply_cregister F f) (apply_cregister F g) \<longleftrightarrow> partial_fun_compatible f g\<close>
proof (rule iffI)
  have [simp]: \<open>cregister_raw (apply_cregister F)\<close>
    using assms(1) cregister.rep_eq by auto
  show \<open>partial_fun_compatible f g \<Longrightarrow>
            partial_fun_compatible (apply_cregister F f) (apply_cregister F g)\<close>
    apply (subst (2) register_from_getter_setter_of_getter_setter[symmetric], simp)
    apply (subst register_from_getter_setter_of_getter_setter[symmetric], simp)
    apply (auto simp add: register_from_getter_setter_def[abs_def] partial_fun_compatible_def
        simp del: register_from_getter_setter_of_getter_setter
        split: option.split)
    by (metis option.sel option.simps(3))
  show \<open>partial_fun_compatible (apply_cregister F f) (apply_cregister F g) \<Longrightarrow>
    partial_fun_compatible f g\<close>
    apply (subst (asm) (2) register_from_getter_setter_of_getter_setter[symmetric], simp)
    apply (subst (asm) register_from_getter_setter_of_getter_setter[symmetric], simp)
    apply (auto simp add: register_from_getter_setter_def[abs_def] partial_fun_compatible_def
        simp del: register_from_getter_setter_of_getter_setter
        split: option.split_asm)
    by (smt (verit) \<open>cregister_raw (apply_cregister F)\<close> option.exhaust valid_getter_setter_def valid_getter_setter_getter_setter)
qed *)

lemma cregister_partial_fun_Sup:
  assumes \<open>cregister F\<close>
  shows \<open>partial_fun_Sup (apply_cregister F ` \<FF>) = apply_cregister F (partial_fun_Sup \<FF>)\<close>
proof (insert assms, transfer fixing: \<FF>)
  fix F :: \<open>'a cupdate \<Rightarrow> 'b cupdate\<close>
  assume \<open>cregister_raw F\<close>
  show \<open>partial_fun_Sup (F ` \<FF>) = F (partial_fun_Sup \<FF>)\<close>
  proof (rule ext)
    fix m
    define Fm \<FF>Fm where \<open>Fm = Axioms_Classical.getter F m\<close> and \<open>\<FF>Fm = (\<lambda>f. f Fm) ` \<FF>\<close>
    have \<open>partial_fun_Sup (F ` \<FF>) m =
        partial_fun_Sup (register_from_getter_setter (Axioms_Classical.getter F) (Axioms_Classical.setter F) ` \<FF>) m\<close>
      by (simp add: \<open>cregister_raw F\<close>)
    also have \<open>\<dots> = option_Sup
          (map_option (\<lambda>a. Axioms_Classical.setter F a m) ` \<FF>Fm)\<close>
      by (simp add: register_from_getter_setter_def partial_fun_Sup_def
          image_image Fm_def \<FF>Fm_def map_option_case)
    also have \<open>\<dots> = map_option (\<lambda>a. Axioms_Classical.setter F a m) (option_Sup \<FF>Fm)\<close>
      by (smt (verit) \<open>cregister_raw F\<close> inj_onI map_option_option_Sup valid_getter_setter_def valid_getter_setter_getter_setter)
    also have \<open>\<dots> = register_from_getter_setter (Axioms_Classical.getter F) (Axioms_Classical.setter F) (partial_fun_Sup \<FF>) m\<close>
      by (simp add: partial_fun_Sup_def[abs_def] register_from_getter_setter_def map_option_case
          flip: Fm_def \<FF>Fm_def)
    also have \<open>\<dots> = F (partial_fun_Sup \<FF>) m\<close>
      by (simp add: \<open>cregister_raw F\<close>)
    finally show \<open>partial_fun_Sup (F ` \<FF>) m = F (partial_fun_Sup \<FF>) m\<close>
      by -
  qed
qed

lemma cregister_compose: \<open>apply_cregister F (a \<circ>\<^sub>m b) = apply_cregister F a \<circ>\<^sub>m apply_cregister F b\<close>
  apply (transfer fixing: a b)
  by (auto simp: non_cregister_raw_def Axioms_Classical.register_mult)

lemma inj_cregister: \<open>inj (apply_cregister F)\<close> if \<open>cregister F\<close>
  using that apply transfer
  by (simp add: cregister_raw_inj)

lift_definition cregister_id :: \<open>('a,'a) cregister\<close> is id by simp

lemma apply_cregister_id[simp]: \<open>apply_cregister cregister_id = id\<close>
  by (rule cregister_id.rep_eq)

lemma cregister_id[simp]: \<open>cregister cregister_id\<close>
  apply transfer by simp

definition \<open>empty_cregister_raw = register_from_getter_setter (\<lambda>_. undefined) (\<lambda>_::_::CARD_1. id)\<close> 
lemma cregister_raw_empty_cregister_raw: \<open>cregister_raw empty_cregister_raw\<close>
  apply (auto intro!: exI simp add: Axioms_Classical.register_def empty_cregister_raw_def)
  by (simp add: valid_getter_setter_def)

lift_definition empty_cregister :: \<open>('a::{CARD_1,enum}, 'b) cregister\<close> is
  empty_cregister_raw
  using cregister_raw_empty_cregister_raw by fast
lemma empty_cregister_is_register[simp]: \<open>cregister empty_cregister\<close>
  apply transfer by (rule cregister_raw_empty_cregister_raw)


definition ccommuting_raw :: \<open>('a cupdate \<Rightarrow> 'c cupdate) \<Rightarrow> ('b cupdate \<Rightarrow> 'c cupdate) \<Rightarrow> bool\<close> where
  \<open>ccommuting_raw F G \<longleftrightarrow> (\<forall>a b. F a \<circ>\<^sub>m G b = G b \<circ>\<^sub>m F a)\<close>

abbreviation \<open>ccompatible_raw \<equiv> Laws_Classical.compatible\<close>
lemmas ccompatible_raw_def = Laws_Classical.compatible_def

lift_definition cregister_pair :: \<open>('a,'c) cregister \<Rightarrow> ('b,'c) cregister \<Rightarrow> ('a\<times>'b, 'c) cregister\<close>
  is \<open>\<lambda>F G. if ccompatible_raw F G then Axioms_Classical.register_pair F G else non_cregister_raw\<close>
  by simp

abbreviation (input) \<open>ccompatible F G \<equiv> cregister (cregister_pair F G)\<close>

lemma ccompatible_def: \<open>ccompatible F G \<longleftrightarrow> cregister F \<and> cregister G \<and> Laws_Classical.compatible (apply_cregister F) (apply_cregister G)\<close>
  by (metis Laws_Classical.compatible_register1 Laws_Classical.compatible_register2 Laws_Classical.pair_is_register cregister.rep_eq cregister_pair.rep_eq non_cregister_raw)

lemma ccompatibleI: \<open>cregister F \<Longrightarrow> cregister G \<Longrightarrow> (\<And>a b. apply_cregister F a \<circ>\<^sub>m apply_cregister G b = apply_cregister G b \<circ>\<^sub>m apply_cregister F a) \<Longrightarrow> ccompatible F G\<close>
  apply transfer
  by (simp add: Laws_Classical.compatible_def[abs_def])

lemma ccompatible_commute:
  assumes \<open>ccompatible F G\<close>
  shows \<open>apply_cregister F a \<circ>\<^sub>m apply_cregister G b = apply_cregister G b \<circ>\<^sub>m apply_cregister F a\<close>
  using Laws_Classical.swap_registers assms ccompatible_def by blast

abbreviation \<open>tensor_map \<equiv> Axioms_Classical.tensor_update\<close>

lemma apply_cregister_pair: \<open>ccompatible F G \<Longrightarrow>
  apply_cregister (cregister_pair F G) (tensor_map a b) = apply_cregister F a \<circ>\<^sub>m apply_cregister G b\<close>
  apply transfer
  using Laws_Classical.register_pair_apply Laws_Classical.compatible_register1 Laws_Classical.compatible_register2 non_cregister_raw by auto

lemma empty_cregisters_same[simp]:
  fixes F :: \<open>('a::{CARD_1,enum},'b) cregister\<close>
  assumes [simp]: \<open>cregister F\<close>
  shows \<open>F = empty_cregister\<close>
proof (rule apply_cregister_inject[THEN iffD1], rule ext)
  fix a :: \<open>'a cupdate\<close>
  consider \<open>a = Map.empty\<close> | \<open>a = Some\<close>
  proof (atomize_elim, cases \<open>a undefined\<close>)
    case None
    then have \<open>a = Map.empty\<close>
      apply (rule_tac ext, subst everything_the_same[of _ undefined])
      by simp
    then show \<open>a = Map.empty \<or> a = Some\<close>
      by simp
  next
    case (Some x)
    then have \<open>a = Some\<close>
      apply (rule_tac ext, subst everything_the_same[of _ undefined])
      by simp
    then show \<open>a = Map.empty \<or> a = Some\<close>
      by simp
  qed
  then show \<open>apply_cregister F a = apply_cregister empty_cregister a\<close>
    apply cases apply auto
    by -
qed


lemma ccompatible_sym: \<open>ccompatible F G \<Longrightarrow> ccompatible G F\<close> for F :: \<open>('a,'c) cregister\<close> and G :: \<open>('b,'c) cregister\<close>
  apply transfer
  using compatible_sym non_cregister_raw register_pair_is_register by fastforce

lemma ccompatible3: \<open>ccompatible (cregister_pair F G) H \<longleftrightarrow> ccompatible F G \<and> ccompatible F H \<and> ccompatible G H\<close>
  unfolding ccompatible_def
  apply transfer
  apply (auto simp: non_cregister_raw)
  apply (metis Laws_Classical.compatible_comp_left Laws_Classical.register_Fst Laws_Classical.register_pair_Fst)
  by (metis Laws_Classical.compatible_comp_left Laws_Classical.register_Snd Laws_Classical.register_pair_Snd)

lemma ccompatible3': \<open>ccompatible H (cregister_pair F G) \<longleftrightarrow> ccompatible F G \<and> ccompatible H F \<and> ccompatible H G\<close>
  by (metis ccompatible3 ccompatible_sym)

lemma compatible_empty_cregister_raw:
  \<open>cregister_raw Q \<Longrightarrow> ccompatible_raw Q empty_cregister_raw\<close>
  apply (simp add: ccompatible_raw_def cregister_raw_empty_cregister_raw)
  apply (auto intro!: ext simp add: empty_cregister_raw_def register_from_getter_setter_def[abs_def] map_comp_def)
  apply (case_tac \<open>Q a k\<close>)
  apply (case_tac \<open>b undefined\<close>)
  apply auto
  apply (case_tac \<open>b undefined\<close>)
  by auto

lemma ccompatible_empty[simp]: \<open>ccompatible Q empty_cregister \<longleftrightarrow> cregister Q\<close>
  apply transfer
  apply (auto simp: compatible_empty_cregister_raw non_cregister_raw)
  by (auto simp: ccompatible_raw_def non_cregister_raw)

lemma ccompatible_empty'[simp]: \<open>ccompatible empty_cregister Q \<longleftrightarrow> cregister Q\<close>
  by (metis ccompatible_empty ccompatible_sym)
lemma ccompatible_register1: \<open>ccompatible F G \<Longrightarrow> cregister F\<close>
  apply transfer
  by (auto simp add: ccompatible_raw_def non_cregister_raw non_cregister_raw)
lemma ccompatible_register2: \<open>ccompatible F G \<Longrightarrow> cregister G\<close>
  apply transfer
  by (auto simp add: ccompatible_raw_def non_cregister_raw non_cregister_raw)

lemma ccompatible_non_cregister1[simp]: \<open>\<not> ccompatible non_cregister F\<close>
  apply transfer by (simp add: non_cregister_raw ccompatible_raw_def)
lemma ccompatible_non_cregister2[simp]: \<open>\<not> ccompatible F non_cregister\<close>
  apply transfer by (simp add: non_cregister_raw ccompatible_raw_def)

lift_definition cFst :: \<open>('a, 'a\<times>'b) cregister\<close> is \<open>Laws_Classical.Fst\<close>
  by simp
lemma cFst_register[simp]: \<open>cregister cFst\<close>
  apply transfer by simp
lift_definition cSnd :: \<open>('b, 'a\<times>'b) cregister\<close> is \<open>Laws_Classical.Snd\<close>
  by simp
lemma cSnd_register[simp]: \<open>cregister cSnd\<close>
  apply transfer by simp

lemma ccompatible_Fst_Snd[simp]: \<open>ccompatible cFst cSnd\<close>
  by (simp add: cFst.rep_eq cSnd.rep_eq ccompatible_def)

lift_definition cregister_chain :: \<open>('b,'c) cregister \<Rightarrow> ('a,'b) cregister \<Rightarrow> ('a,'c) cregister\<close>
  is \<open>\<lambda>F G. if cregister_raw F \<and> cregister_raw G then F o G else non_cregister_raw\<close>
  by auto

lemmas cregister_raw_chain = Axioms_Classical.register_comp

lemma cregister_chain_apply[simp]: \<open>apply_cregister (cregister_chain F G) = apply_cregister F o apply_cregister G\<close>
  apply (rule ext) apply transfer
  by (auto simp: non_cregister_raw_def cregister_raw_empty)

lemma cregister_id_chain[simp]: \<open>cregister_chain cregister_id F = F\<close>
  apply transfer by auto
lemma cregister_chain_id[simp]: \<open>cregister_chain F cregister_id = F\<close>
  apply transfer by auto

lemma cregister_chain_non_register1[simp]: \<open>cregister_chain non_cregister F = non_cregister\<close>
  apply transfer by (auto simp add: non_cregister_raw)
lemma cregister_chain_non_register2[simp]: \<open>cregister_chain F non_cregister = non_cregister\<close>
  apply transfer by (auto simp add: non_cregister_raw)

lemma cregister_chain_assoc: \<open>cregister_chain (cregister_chain F G) H = cregister_chain F (cregister_chain G H)\<close>
  apply (cases \<open>cregister F\<close>; cases \<open>cregister G\<close>; cases \<open>cregister H\<close>)
  apply (simp_all add: non_cregister)
  apply transfer
  by (auto simp add: cregister_raw_chain)

lemma cregister_chain_is_cregister[simp]: \<open>cregister (cregister_chain F G) \<longleftrightarrow> cregister F \<and> cregister G\<close>
  apply transfer
  by (auto simp: non_cregister_raw cregister_raw_chain)

lemma cregister_chain_pair_Fst[simp]: \<open>ccompatible F G \<Longrightarrow> cregister_chain (cregister_pair F G) cFst = F\<close>
  unfolding ccompatible_def apply transfer
  by (simp add: Laws_Classical.register_pair_Fst)

lemma cregister_chain_pair_Fst_chain[simp]:
  assumes \<open>ccompatible F G\<close>
  shows \<open>cregister_chain (cregister_pair F G) (cregister_chain cFst H) = cregister_chain F H\<close>
  by (metis cregister_chain_pair_Fst assms cregister_chain_assoc)

lemma cregister_chain_pair_Snd[simp]: \<open>ccompatible F G \<Longrightarrow> cregister_chain (cregister_pair F G) cSnd = G\<close>
  unfolding ccompatible_def apply transfer
  by (simp add: Laws_Classical.register_pair_Snd)

lemma cregister_chain_pair_Snd_chain[simp]:
  assumes \<open>ccompatible F G\<close>
  shows \<open>cregister_chain (cregister_pair F G) (cregister_chain cSnd H) = cregister_chain G H\<close>
  by (metis cregister_chain_pair_Snd assms cregister_chain_assoc)

lemma ccompatible_comp_left[simp]: "ccompatible F G \<Longrightarrow> cregister H \<Longrightarrow> ccompatible (cregister_chain F H) G"
  unfolding ccompatible_def apply transfer by auto

lemma ccompatible_comp_right[simp]: "ccompatible F G \<Longrightarrow> cregister H \<Longrightarrow> ccompatible F (cregister_chain G H)"
  by (meson ccompatible_comp_left ccompatible_sym)

lemmas ccompatible_Snd_Fst[simp] = ccompatible_Fst_Snd[THEN ccompatible_sym]


lemma ccompatible3I[simp]: \<open>ccompatible F G \<Longrightarrow> ccompatible G H \<Longrightarrow> ccompatible F H \<Longrightarrow> ccompatible (cregister_pair F G) H\<close>
  by (simp add: ccompatible3)
lemma ccompatible3I'[simp]: \<open>ccompatible F G \<Longrightarrow> ccompatible F H \<Longrightarrow> ccompatible G H \<Longrightarrow> ccompatible F (cregister_pair G H)\<close>
  by (simp add: ccompatible3')

definition \<open>cswap = cregister_pair cSnd cFst\<close>

lemma cregister_cswap[simp]: \<open>cregister cswap\<close>
  by (simp add: ccompatible_sym cswap_def)

lemma cregister_pair_cnonregister1[simp]: \<open>cregister_pair non_cregister F = non_cregister\<close>
  using non_cregister ccompatible_non_cregister1 by blast

lemma cregister_pair_cnonregister2[simp]: \<open>cregister_pair F non_cregister = non_cregister\<close>
  using non_cregister ccompatible_non_cregister2 by blast

lemma not_ccompatible_chain: 
  assumes \<open>\<not> ccompatible G H\<close>
  shows \<open>\<not> ccompatible (cregister_chain F G) (cregister_chain F H)\<close>
proof (rule notI)
  assume asm: \<open>ccompatible (cregister_chain F G) (cregister_chain F H)\<close>
  consider (FGH) \<open>cregister F\<close> \<open>cregister G\<close> \<open>cregister H\<close>
    | (nF) \<open>\<not> cregister F\<close> | (nG) \<open>\<not> cregister G\<close> | (nH) \<open>\<not> cregister H\<close>
    by auto
  then show False
  proof cases
    case FGH
    have \<open>apply_cregister F (apply_cregister G a \<circ>\<^sub>m apply_cregister H b) = apply_cregister F (apply_cregister H b \<circ>\<^sub>m apply_cregister G a)\<close> for a b
      using ccompatible_commute[OF asm]
      by (simp add: cregister_compose)
    moreover from FGH have \<open>inj (apply_cregister F)\<close>
      by (simp add: inj_cregister)
    ultimately have \<open>apply_cregister G a \<circ>\<^sub>m apply_cregister H b = apply_cregister H b \<circ>\<^sub>m apply_cregister G a\<close> for a b
      by (simp add: injD)
    then have \<open>ccompatible G H\<close>
      apply (rule_tac ccompatibleI)
      using FGH by auto
    with assms show False
      by simp
  next
    case nF with asm assms show ?thesis by (simp add: non_cregister)
  next
    case nG with asm assms show ?thesis by (simp add: non_cregister)
  next
    case nH with asm assms show ?thesis by (simp add: non_cregister)
  qed
qed

lemma cregister_chain_pair:
  shows \<open>cregister_chain F (cregister_pair G H) = cregister_pair (cregister_chain F G) (cregister_chain F H)\<close>
proof -
  consider (GH_F) \<open>ccompatible G H\<close> \<open>cregister F\<close> | (nF) \<open>F = non_cregister\<close> | (nGH) \<open>\<not> ccompatible G H\<close>
    by (auto simp flip: non_cregister)
  then show ?thesis
  proof cases
    case GH_F
    then show ?thesis
      unfolding ccompatible_def
      apply transfer
      by (simp add: Laws_Classical.register_comp_pair)
  next
    case nF
    then show ?thesis
      by simp
  next
    case nGH
    then have \<open>\<not> ccompatible (cregister_chain F G) (cregister_chain F H)\<close>
      by (rule not_ccompatible_chain)
    then have [simp]: \<open>cregister_pair (cregister_chain F G) (cregister_chain F H) = non_cregister\<close>
      using non_cregister by auto
    from nGH have [simp]: \<open>cregister_pair G H = non_cregister\<close>
      using non_cregister by blast
    with nGH show ?thesis 
      by simp
  qed
qed

lemma cregister_chain_cswap_cswap[simp]: \<open>cregister_chain cswap cswap = cregister_id\<close>
  by (metis Laws_Classical.pair_Fst_Snd apply_cregister_inverse cFst.rep_eq cSnd.rep_eq ccompatible_Fst_Snd ccompatible_Snd_Fst ccompatible_def cregister_chain_pair cregister_chain_pair_Fst cregister_chain_pair_Snd cregister_id.abs_eq cregister_pair.rep_eq cswap_def)

definition \<open>iso_cregister I \<longleftrightarrow> cregister I \<and> (\<exists>J. cregister J \<and> cregister_chain I J = cregister_id \<and> cregister_chain J I = cregister_id)\<close>

lift_definition cregister_inv :: \<open>('a,'b) cregister \<Rightarrow> ('b,'a) cregister\<close> is
  \<open>\<lambda>F. if cregister_raw (inv F) then inv F else non_cregister_raw\<close> by auto

lemma iso_cregister_inv_iso: \<open>iso_cregister I \<Longrightarrow> iso_cregister (cregister_inv I)\<close>
  unfolding iso_cregister_def apply transfer apply auto
  using non_cregister_raw apply fastforce
  using inv_unique_comp apply blast
  apply (simp add: inv_unique_comp)
  using inv_unique_comp by blast

lemma iso_cregister_inv_iso_apply: \<open>iso_cregister I \<Longrightarrow> apply_cregister (cregister_inv I) = inv (apply_cregister I)\<close>
  unfolding iso_cregister_def apply transfer using non_cregister_raw inv_unique_comp apply auto by blast

lemma iso_cregister_inv_chain: \<open>iso_cregister I \<Longrightarrow> cregister_chain (cregister_inv I) I = cregister_id\<close>
  apply (rule apply_cregister_inject[THEN iffD1], rule ext)
  apply simp
  by (smt (verit, del_insts) apply_cregister_id inv_unique_comp iso_cregister_def iso_cregister_inv_iso_apply pointfree_idE cregister_chain_apply)

lemma iso_cregister_chain_inv: \<open>iso_cregister I \<Longrightarrow> cregister_chain I (cregister_inv I) = cregister_id\<close>
  apply (rule apply_cregister_inject[THEN iffD1], rule ext)
  apply simp
  by (smt (verit, best) apply_cregister_id iso_cregister_def iso_cregister_inv_chain left_right_inverse_eq pointfree_idE cregister_chain_apply)

lemma cswap_iso[simp]: \<open>iso_cregister cswap\<close>
  by (auto intro!: exI[of _ cswap] simp: iso_cregister_def)

lemma ccompatible_chain[simp]: \<open>cregister F \<Longrightarrow> ccompatible G H \<Longrightarrow> ccompatible (cregister_chain F G) (cregister_chain F H)\<close>
  unfolding ccompatible_def apply transfer by simp  

lemma ccompatible_chain_iso: \<open>iso_cregister I \<Longrightarrow> ccompatible (cregister_chain I F) (cregister_chain I G) \<longleftrightarrow> ccompatible F G\<close>
  apply (cases \<open>cregister F\<close>; cases \<open>cregister G\<close>)
     apply (simp_all add: non_cregister)
  apply (rule iffI)
   apply (subst asm_rl[of \<open>F = cregister_chain (cregister_inv I) (cregister_chain I F)\<close>])
    apply (simp add: cregister_chain_assoc[symmetric] iso_cregister_inv_chain)
   apply (subst asm_rl[of \<open>G = cregister_chain (cregister_inv I) (cregister_chain I G)\<close>])
    apply (simp add: cregister_chain_assoc[symmetric] iso_cregister_inv_chain)
   apply (rule ccompatible_chain)
  using iso_cregister_def iso_cregister_inv_iso apply auto
  by (simp add: iso_cregister_def ccompatible_chain)

lift_definition getter :: \<open>('a,'b) cregister \<Rightarrow> 'b \<Rightarrow> 'a\<close> is
  \<open>\<lambda>F. if cregister_raw F then Axioms_Classical.getter F else (\<lambda>_. undefined)\<close>.
lift_definition setter :: \<open>('a,'b) cregister \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b\<close> is
  \<open>\<lambda>F. if cregister_raw F then Axioms_Classical.setter F else (\<lambda>_. id)\<close>.

lemma getter_non_cregister[simp]: \<open>getter non_cregister m = undefined\<close>
  apply transfer by (simp add: non_cregister_raw)
lemma setter_non_cregister[simp]: \<open>setter non_cregister a = id\<close>
  apply transfer by (simp add: non_cregister_raw)

lemma getter_setter_same[simp]: \<open>cregister x \<Longrightarrow> getter x (setter x a m) = a\<close>
  apply transfer apply (simp add: non_cregister_raw)
  by (meson valid_getter_setter_def valid_getter_setter_getter_setter)

lemma setter_setter_same[simp]: \<open>setter x b (setter x a m) = setter x b m\<close>
  apply transfer apply (simp add: non_cregister_raw)
  by (meson valid_getter_setter_def valid_getter_setter_getter_setter)

(* TODO move to Registers.Classical_Extra *)
lemma getter_setter: \<open>Axioms_Classical.getter F (Axioms_Classical.setter G a m) = Axioms_Classical.getter F m\<close> if \<open>Laws_Classical.compatible F G\<close> for F G
proof -
  have \<open>Axioms_Classical.register F\<close>
    using Laws_Classical.compatible_register1 that by blast
  have \<open>Axioms_Classical.register G\<close>
    using Laws_Classical.compatible_register2 that by auto
  have valid_gsF: \<open>valid_getter_setter (Axioms_Classical.getter F) (Axioms_Classical.setter F)\<close>
    by (simp add: \<open>cregister_raw F\<close>)

  have \<open>Axioms_Classical.getter F (Axioms_Classical.setter G a m)
      = Axioms_Classical.getter F (Axioms_Classical.setter G a 
              (Axioms_Classical.setter F (Axioms_Classical.getter F m) m))\<close>
    by (metis valid_gsF valid_getter_setter_def)
  also have \<open>\<dots> = Axioms_Classical.getter F (Axioms_Classical.setter F
                      (Axioms_Classical.getter F m) (Axioms_Classical.setter G a m))\<close>
    by (metis (mono_tags, lifting) Classical_Extra.compatible_setter 
        \<open>cregister_raw F\<close> \<open>cregister_raw G\<close> o_eq_dest that)
  also have \<open>\<dots> = Axioms_Classical.getter F m\<close>
    by (meson valid_gsF valid_getter_setter_def)
  finally show ?thesis
    by -
qed

(* TODO move to Registers *)
lemma setter_setter_compatI_raw:
  assumes \<open>cregister_raw x\<close> and \<open>cregister_raw y\<close>
  assumes \<open>\<And>a b m. Axioms_Classical.setter x a (Axioms_Classical.setter y b m)
                 = Axioms_Classical.setter y b (Axioms_Classical.setter x a m)\<close>
  shows \<open>ccompatible_raw x y\<close>
proof -
  define sx gx sy gy where \<open>sx = Axioms_Classical.setter x\<close> and \<open>gx = Axioms_Classical.getter x\<close>
    and \<open>sy = Axioms_Classical.setter y\<close> and \<open>gy = Axioms_Classical.getter y\<close>
  have x: \<open>x = register_from_getter_setter gx sx\<close>
    by (simp add: assms(1) gx_def sx_def)
  have y: \<open>y = register_from_getter_setter gy sy\<close>
    by (simp add: assms(2) gy_def sy_def)

  have [simp]: \<open>sx (gx m) m = m\<close> for m
    by (metis assms(1) gx_def sx_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have [simp]: \<open>gx (sx a m) = a\<close> for a m
    by (metis assms(1) gx_def sx_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have [simp]: \<open>sy (gy m) m = m\<close> for m
    by (metis assms(2) gy_def sy_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have [simp]: \<open>gy (sy a m) = a\<close> for a m
    by (metis assms(2) gy_def sy_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have s_comm: \<open>sx a (sy b m) = sy b (sx a m)\<close> for a b m
    using assms(3) by (simp add: sx_def sy_def)
  have [simp]: \<open>gx (sy a m) = gx m\<close> for a m
  proof -
    have \<open>gx (sy a m) = gx (sy a (sx (gx m) m))\<close>
      by simp
    also have \<open>\<dots> = gx (sx (gx m) (sy a m))\<close>
      by (simp add: s_comm)
    also have \<open>\<dots> = gx m\<close>
      by simp
    finally show ?thesis
      by -
  qed
  have [simp]: \<open>gy (sx a m) = gy m\<close> for a m
  proof -
    have \<open>gy (sx a m) = gy (sx a (sy (gy m) m))\<close>
      by simp
    also have \<open>\<dots> = gy (sy (gy m) (sx a m))\<close>
      by (simp flip: s_comm)
    also have \<open>\<dots> = gy m\<close>
      by simp
    finally show ?thesis
      by -
  qed

  have \<open>(x a \<circ>\<^sub>m y b) m = (y b \<circ>\<^sub>m x a) m\<close> for a b m
    apply (cases \<open>a (gx m)\<close>; cases \<open>b (gy m)\<close>)
    by (auto simp add: x y register_from_getter_setter_def[abs_def] s_comm)
  then show ?thesis
    apply (rule_tac Laws_Classical.compatibleI)
    using assms(1,2) by auto
qed

lemma getter_setter_compat[simp]: \<open>ccompatible x y \<Longrightarrow> getter x (setter y a m) = getter x m\<close>
  unfolding ccompatible_def
  apply transfer by (simp add: non_cregister_raw getter_setter)
lemma setter_setter_compat: \<open>ccompatible x y \<Longrightarrow> setter x a (setter y b m) = setter y b (setter x a m)\<close>
  unfolding ccompatible_def
  apply transfer apply (simp add: non_cregister_raw)
  by (metis Classical_Extra.compatible_setter o_def)
lemma setter_setter_compatI: 
  assumes \<open>cregister x\<close> and \<open>cregister y\<close>
  assumes \<open>\<And>a b m. setter x a (setter y b m) = setter y b (setter x a m)\<close>
  shows \<open>ccompatible x y\<close>
  unfolding ccompatible_def using assms
  apply transfer by (auto simp add: non_cregister_raw setter_setter_compatI_raw)
lemma setter_getter_same[simp]: \<open>setter x (getter x m) m = m\<close>
  apply transfer apply (simp add: non_cregister_raw)
  by (metis valid_getter_setter_def valid_getter_setter_getter_setter)

lift_definition cregister_from_getter_setter :: \<open>('b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a,'b) cregister\<close> is
  \<open>\<lambda>g s. if valid_getter_setter g s then register_from_getter_setter g s else non_cregister_raw\<close>
  by auto

lemma setter_of_cregister_from_getter_is_cregister: \<open>valid_getter_setter g s \<Longrightarrow> cregister (cregister_from_getter_setter g s)\<close>
  apply transfer by simp
lemma setter_of_cregister_from_getter_setter: \<open>valid_getter_setter g s \<Longrightarrow> setter (cregister_from_getter_setter g s) = s\<close>
  apply transfer by simp
lemma getter_of_cregister_from_getter_setter: \<open>valid_getter_setter g s \<Longrightarrow> getter (cregister_from_getter_setter g s) = g\<close>
  apply transfer by simp


(* TODO move to Registers *)
lemma valid_getter_setter_pair: 
  assumes \<open>Laws_Classical.compatible F G\<close>
  shows \<open>valid_getter_setter (\<lambda>m. (Axioms_Classical.getter F m, Axioms_Classical.getter G m))
           (\<lambda>(a, b) m. Axioms_Classical.setter F a (Axioms_Classical.setter G b m))\<close>
proof -
  have \<open>Axioms_Classical.register F\<close>
    using Laws_Classical.compatible_register1 assms by blast
  have \<open>Axioms_Classical.register G\<close>
    using Laws_Classical.compatible_register2 assms by auto
  have valid_gsF: \<open>valid_getter_setter (Axioms_Classical.getter F) (Axioms_Classical.setter F)\<close>
    by (simp add: \<open>cregister_raw F\<close>)
  have valid_gsG: \<open>valid_getter_setter (Axioms_Classical.getter G) (Axioms_Classical.setter G)\<close>
    by (simp add: \<open>cregister_raw G\<close>)

  have valid: \<open>valid_getter_setter (\<lambda>m. (Axioms_Classical.getter F m, Axioms_Classical.getter G m))
     (\<lambda>(a, b) m. Axioms_Classical.setter F a (Axioms_Classical.setter G b m))\<close>
    using valid_gsF valid_gsG
    apply (auto simp: valid_getter_setter_def)
     apply (metis Laws_Classical.compatible_sym assms getter_setter)
    by (metis Classical_Extra.compatible_setter Laws_Classical.compatible_register1 Laws_Classical.compatible_register2 assms o_def)
  show ?thesis
    using valid by (auto simp: Axioms_Classical.register_pair_def o_def setter_of_register_from_getter_setter)
qed

(* TODO move to Registers session *)
lemma setter_pair_raw: \<open>Axioms_Classical.setter (F;G) = (\<lambda>(x, y). Axioms_Classical.setter F x \<circ> Axioms_Classical.setter G y)\<close>
  if \<open>Laws_Classical.compatible F G\<close>
  using valid_getter_setter_pair[OF that] 
  by (auto simp: Axioms_Classical.register_pair_def o_def)

lemma setter_pair:
  assumes \<open>ccompatible F G\<close>
  shows \<open>setter (cregister_pair F G) = (\<lambda>(x,y). setter F x o setter G y)\<close>
  using assms unfolding ccompatible_def
  apply transfer using setter_pair_raw by auto

(* TODO move to Registers *)
lemma getter_pair_raw:
  assumes \<open>ccompatible_raw F G\<close>
  shows \<open>Axioms_Classical.getter (F;G) = (\<lambda>m. (Axioms_Classical.getter F m, Axioms_Classical.getter G m))\<close>
  using assms by (simp_all add: Axioms_Classical.register_pair_def valid_getter_setter_pair)

lemma getter_pair:
  assumes \<open>ccompatible F G\<close>
  shows \<open>getter (cregister_pair F G) = (\<lambda>m. (getter F m, getter G m))\<close>
  using assms unfolding ccompatible_def
  apply transfer using getter_pair_raw by auto

(* TODO move to Registers *)
lemma getterI: 
  assumes \<open>Axioms_Classical.register F\<close>
  assumes \<open>Axioms_Classical.setter F a m = m\<close>
  shows \<open>Axioms_Classical.getter F m = a\<close>
  by (metis assms(1) assms(2) valid_getter_setter_def valid_getter_setter_getter_setter)

(* TODO move to Registers *)
lemma register_apply_comp:
  assumes \<open>cregister_raw F\<close> and \<open>cregister_raw G\<close>
  shows \<open>register_apply (F \<circ> G) f m = register_apply F (register_apply G f) m\<close>
  apply (rule option.inject[THEN iffD1])
  by (simp add:
      register_apply[unfolded o_def, OF \<open>cregister_raw F\<close>, THEN fun_cong]
      register_apply[unfolded o_def, OF \<open>cregister_raw G\<close>, THEN fun_cong]
      register_apply[unfolded o_def, OF cregister_raw_chain[OF \<open>cregister_raw G\<close> \<open>cregister_raw F\<close>], THEN fun_cong]
      del: option.inject)

(* TODO move to Registers *)
lemma
  assumes [simp]: \<open>cregister_raw F\<close> \<open>cregister_raw G\<close>
  shows setter_chain_raw: \<open>Axioms_Classical.setter (F \<circ> G) a m =
       Axioms_Classical.setter F
        (Axioms_Classical.setter G a (Axioms_Classical.getter F m)) m\<close>
    and getter_chain_raw: \<open>Axioms_Classical.getter (F \<circ> G) = Axioms_Classical.getter G \<circ> Axioms_Classical.getter F\<close>
proof -
  define sF gF where \<open>sF = Axioms_Classical.setter F\<close> and \<open>gF = Axioms_Classical.getter F\<close>
  from \<open>Axioms_Classical.register F\<close>
  have F: \<open>F u m = (case u (gF m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (sF x m))\<close> for u m
    by (metis gF_def register_from_getter_setter_def register_from_getter_setter_of_getter_setter sF_def)
  have validF: \<open>valid_getter_setter gF sF\<close>
    using gF_def sF_def by auto
  define sG gG where \<open>sG = Axioms_Classical.setter G\<close> and \<open>gG = Axioms_Classical.getter G\<close>
  from \<open>Axioms_Classical.register G\<close>
  have G: \<open>G u m = (case u (gG m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (sG x m))\<close> for u m
    by (metis gG_def register_from_getter_setter_def register_from_getter_setter_of_getter_setter sG_def)
  have validG: \<open>valid_getter_setter gG sG\<close>
    by (simp add: gG_def sG_def)
  define s g where \<open>s a m = sF (sG a (gF m)) m\<close> and \<open>g m = gG (gF m)\<close> for a m
  have *: \<open>(F \<circ> G) a m = register_from_getter_setter g s a m\<close> for a m
    by (auto simp add: option.case_eq_if F G s_def g_def register_from_getter_setter_def)
  have \<open>valid_getter_setter g s\<close>
    using validF validG by (auto simp: valid_getter_setter_def s_def g_def)
  show \<open>Axioms_Classical.setter (F \<circ> G) a m = sF (sG a (gF m)) m\<close>
    apply (simp add: *[abs_def] setter_of_register_from_getter_setter \<open>valid_getter_setter g s\<close>)
    by (simp add: s_def)
  show \<open>Axioms_Classical.getter (F \<circ> G) = gG o gF\<close>
    apply (simp add: *[abs_def] getter_of_register_from_getter_setter \<open>valid_getter_setter g s\<close>)
    by (simp add: g_def[abs_def] o_def)
qed


lemma getter_chain:
  assumes \<open>cregister F\<close>
  shows \<open>getter (cregister_chain F G) = getter G o getter F\<close>
  using assms apply transfer using getter_chain_raw by (auto simp: non_cregister_raw)

definition same_outside_cregister :: \<open>('a,'b) cregister \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool\<close> where
  \<open>same_outside_cregister F x y \<longleftrightarrow> x = setter F (getter F x) y\<close>

lemma same_outside_cregister_non_cregister[simp]: \<open>same_outside_cregister non_cregister = (=)\<close>
  unfolding same_outside_cregister_def
  by simp

lemma equivp_same_outside_cregister[simp]: \<open>equivp (same_outside_cregister F)\<close>
proof (cases \<open>cregister F\<close>)
  case False
  then have [simp]: \<open>F = non_cregister\<close>
    using non_cregister by force
  show ?thesis
    using identity_equivp by simp
next
  case True
  have \<open>reflp (same_outside_cregister F)\<close>
    by (simp add: same_outside_cregister_def reflpI)
  moreover have \<open>symp (same_outside_cregister F)\<close>
    by (metis same_outside_cregister_def setter_getter_same setter_setter_same sympI)
  moreover have \<open>transp (same_outside_cregister F)\<close>
    by (smt (verit, del_insts) same_outside_cregister_def setter_setter_same transpI)
  ultimately show ?thesis
    by (rule equivpI)
qed

lemma cregister_pair_chain_swap[simp]:
  "cregister_chain (cregister_pair A B) cswap = (cregister_pair B A)"
  apply (cases \<open>ccompatible A B\<close>)
   apply (auto simp: non_cregister cregister_chain_pair cswap_def)
  by (metis ccompatible_sym non_cregister)

lemma setter_chain:
  assumes \<open>cregister F\<close> \<open>cregister G\<close>
  shows \<open>setter (cregister_chain F G) a m = setter F (setter G a (getter F m)) m\<close>
  using assms apply transfer using setter_chain_raw apply auto by fast

(* TODO move to Registers *)
lemma valid_getter_setter_fst[simp]: \<open>valid_getter_setter fst (\<lambda>x (_,y). (x,y))\<close>
  by (simp add: valid_getter_setter_def)
lemma Fst_register_from_getter_setter: \<open>Laws_Classical.Fst = register_from_getter_setter fst (\<lambda>x (_,y). (x,y))\<close>
proof -
  have \<open>Axioms_Classical.preregister Laws_Classical.Fst\<close>
    by simp
  moreover have \<open>Axioms_Classical.preregister (register_from_getter_setter fst (\<lambda>x (_, y). (x, y)))\<close>
    by simp
  moreover have \<open>Laws_Classical.Fst (update1 u v) = register_from_getter_setter fst (\<lambda>x (_, y). (x, y)) (update1 u v)\<close> for u v :: 'a
    by (auto intro!: ext 
        simp add: Laws_Classical.Fst_def register_from_getter_setter_def[abs_def] 
        Axioms_Classical.tensor_update_def update1_def)
  ultimately show ?thesis
    by (rule update1_extensionality)
qed
lemma valid_getter_setter_snd[simp]: \<open>valid_getter_setter snd (\<lambda>y (x,_). (x,y))\<close>
  by (simp add: valid_getter_setter_def)
lemma Snd_register_from_getter_setter: \<open>Laws_Classical.Snd = register_from_getter_setter snd (\<lambda>y (x,_). (x,y))\<close>
proof -
  have \<open>Axioms_Classical.preregister Laws_Classical.Snd\<close>
    by simp
  moreover have \<open>Axioms_Classical.preregister (register_from_getter_setter snd (\<lambda>y (x,_). (x, y)))\<close>
    by simp
  moreover have \<open>Laws_Classical.Snd (update1 u v) = register_from_getter_setter snd (\<lambda>y (x,_). (x,y)) (update1 u v)\<close> for u v :: 'a
    by (auto intro!: ext 
        simp add: Laws_Classical.Snd_def register_from_getter_setter_def[abs_def] 
        Axioms_Classical.tensor_update_def update1_def)
  ultimately show ?thesis
    by (rule update1_extensionality)
qed
lemma setter_Fst: \<open>Axioms_Classical.setter Laws_Classical.Fst x' xy = (x',snd xy)\<close>
  apply (subst Fst_register_from_getter_setter)
  by (simp add: case_prod_beta)
lemma getter_Fst: \<open>Axioms_Classical.getter Laws_Classical.Fst = fst\<close>
  apply (subst Fst_register_from_getter_setter)
  by (simp add: case_prod_beta)
lemma setter_Snd: \<open>Axioms_Classical.setter Laws_Classical.Snd y' xy = (fst xy,y')\<close>
  apply (subst Snd_register_from_getter_setter)
  by (simp add: case_prod_beta)
lemma getter_Snd: \<open>Axioms_Classical.getter Laws_Classical.Snd = snd\<close>
  apply (subst Snd_register_from_getter_setter)
  by (simp add: case_prod_beta)

lemma setter_cFst: \<open>setter cFst x' xy = apfst (\<lambda>_. x') xy\<close>
  apply transfer
  by (simp add: setter_Fst[abs_def] case_prod_unfold apfst_def map_prod_def)
lemma setter_cSnd: \<open>setter cSnd y' xy = apsnd (\<lambda>_. y') xy\<close>
  apply transfer
  by (simp add: setter_Snd[abs_def] case_prod_unfold apsnd_def map_prod_def)
lemma getter_cFst[simp]: \<open>getter cFst = fst\<close>
  apply transfer by (simp add: getter_Fst)
lemma getter_cSnd[simp]: \<open>getter cSnd = snd\<close>
  apply transfer by (simp add: getter_Snd)

(* TODO: (and also for quantum, also for COMPATIBLE)
lemma ccompatible_register_tensor[simp]: \<open>ccompatible F F' \<Longrightarrow> ccompatible G G' \<Longrightarrow> ccompatible (cregister_tensor F G) (cregister_tensor F' G')\<close> *)

lemma register_from_getter_setter_id: \<open>id = register_from_getter_setter (\<lambda>m. m) (\<lambda>a m. a)\<close>
  by (auto intro!: ext simp add: register_from_getter_setter_def option.case_eq_if)
lemma valid_getter_setter_id: \<open>valid_getter_setter (\<lambda>m. m) (\<lambda>a m. a)\<close>
  by (simp add: valid_getter_setter_def)

lemma getter_id: \<open>getter cregister_id m = m\<close>
  apply transfer
  apply (subst (2) register_from_getter_setter_id)
  by (simp add: getter_of_register_from_getter_setter valid_getter_setter_id)
lemma setter_id: \<open>setter cregister_id a m = a\<close>
  apply transfer
  apply (subst (2) register_from_getter_setter_id)
  by (simp add: setter_of_register_from_getter_setter valid_getter_setter_id)

(* TODO to Registers *)
lemma getter_from_update1: 
  assumes \<open>cregister_raw F\<close>
  shows \<open>Axioms_Classical.getter F m = a \<longleftrightarrow> F (update1 a b) m \<noteq> None\<close>
  apply (subst (2) register_from_getter_setter_of_getter_setter[symmetric, OF assms])
  by (auto simp add: register_from_getter_setter_def update1_def)

(* TODO to Registers *)
lemma register_apply_mult:
  assumes \<open>cregister_raw F\<close>
  shows \<open>register_apply F a o register_apply F b = register_apply F (a o b)\<close>
proof (rule ext)
  fix x
  have FSome: \<open>F (\<lambda>y. Some (w y)) z \<noteq> None\<close> for z w
    by (meson assms option.simps(3) register_total total_fun_def)

  have \<open>Some ((register_apply F a o register_apply F b) x) = F (Some o a) (register_apply F b x)\<close>
    using register_apply[OF assms, THEN fun_cong]
    by (simp add: o_def)
  also have \<open>\<dots> = F (\<lambda>x. Some (a x)) (the (F (\<lambda>x. Some (b x)) x))\<close>
    by (simp add: register_apply_def o_def)
  also have \<open>\<dots> = (F (Some o a) \<circ>\<^sub>m F (Some o b)) x\<close>
    apply (cases \<open>F (\<lambda>x. Some (b x)) x\<close>)
    using FSome by (auto simp: map_comp_def o_def)
  also have \<open>\<dots> = F ((Some o a) \<circ>\<^sub>m (Some o b)) x\<close>
    by (simp add: Axioms_Classical.register_mult assms)
  also have \<open>\<dots> = F (\<lambda>x. Some (a (b x))) x\<close>
    apply (cases \<open>F (\<lambda>x. Some (b x)) x\<close>)
    using FSome by (auto simp: map_comp_def)
  also have \<open>\<dots> = Some (register_apply F (a o b) x)\<close>
    by (simp add: register_apply_def o_def option.collapse[OF FSome])
  finally show \<open>(register_apply F a \<circ> register_apply F b) x = register_apply F (a \<circ> b) x\<close>
    by simp
qed

(* TODO to Registers (replace register_total?) *)
lemma register_total_iff: 
  assumes \<open>cregister_raw F\<close>
  shows \<open>total_fun (F a) \<longleftrightarrow> total_fun a\<close>
proof (rule iffI)
  show \<open>total_fun a \<Longrightarrow> total_fun (F a)\<close>
    using assms register_total by blast
next
  show \<open>total_fun a\<close> if \<open>total_fun (F a)\<close>
  proof (rule ccontr)
    assume \<open>\<not> total_fun a\<close>
    then obtain x where \<open>a x = None\<close>
      using total_fun_def by blast
    then have \<open>a \<circ>\<^sub>m update1 x x = Map.empty\<close>
      by (metis map_comp_None_iff update1_def)
    then have \<open>F a \<circ>\<^sub>m F (update1 x x) = Map.empty\<close>
      by (simp add: Axioms_Classical.register_mult cregister_raw_empty assms)
    with \<open>total_fun (F a)\<close> have \<open>F (update1 x x) = Map.empty\<close>
      by (meson map_comp_None_iff total_fun_def)
    then have \<open>update1 x x = Map.empty\<close>
      by (smt (verit) assms getter_from_update1 valid_getter_setter_def valid_getter_setter_getter_setter)
    then show False
      by (metis option.discI update1_def)
  qed
qed

(* TODO move to Registers *)
lemma register_apply_via_setter_getter:
  assumes [simp]: \<open>cregister_raw F\<close>
  shows \<open>register_apply F f m = Axioms_Classical.setter F (f (Axioms_Classical.getter F m)) m\<close>
  apply (subst register_from_getter_setter_of_getter_setter[symmetric, OF assms])
  by (simp add: register_from_getter_setter_def[abs_def] register_apply_def
      del: register_from_getter_setter_of_getter_setter)

(* TODO move to Registers *)
lemma getter_register_apply:
  assumes [simp]: \<open>cregister_raw F\<close>
  shows \<open>Axioms_Classical.getter F (register_apply F f m) = f (Axioms_Classical.getter F m)\<close>
  apply (simp add: register_apply_via_setter_getter)
  by (metis assms valid_getter_setter_def valid_getter_setter_getter_setter)

lemma cregister_eqI_setter_raw: 
  assumes [simp]: \<open>cregister_raw F\<close> \<open>cregister_raw G\<close>
  assumes eq: \<open>\<And>a m. Axioms_Classical.setter F a m = Axioms_Classical.setter G a m\<close>
  shows \<open>F = G\<close>
proof -
  from eq \<open>cregister_raw F\<close> \<open>cregister_raw G\<close> have \<open>Axioms_Classical.getter F = Axioms_Classical.getter G\<close>
    by (auto simp: Axioms_Classical.getter_def)
  with eq[abs_def]
  have \<open>register_from_getter_setter (Axioms_Classical.getter F) (Axioms_Classical.setter F)
      = register_from_getter_setter (Axioms_Classical.getter G) (Axioms_Classical.setter G)\<close>
    by simp
  then show ?thesis
    by (simp add: register_from_getter_setter_of_getter_setter)
qed

lemma cregister_eqI_setter: 
  assumes \<open>cregister F\<close> \<open>cregister G\<close>
  assumes eq: \<open>\<And>a m. setter F a m = setter G a m\<close>
  shows \<open>F = G\<close>
  using assms apply transfer
  by (auto intro!: cregister_eqI_setter_raw)

lemma getter_Snd_chain_swap[simp]: \<open>getter (cregister_chain cSnd G) (prod.swap m) = getter (cregister_chain cFst G) m\<close>
  by (simp add: getter_chain)
lemma getter_Fst_chain_swap[simp]: \<open>getter (cregister_chain cFst G) (prod.swap m) = getter (cregister_chain cSnd G) m\<close>
  by (simp add: getter_chain)

lemma apply_cregister_getter_setter:
  assumes \<open>cregister F\<close>
  shows \<open>apply_cregister F a m = (case a (getter F m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (setter F x m))\<close>
  using assms
  apply (transfer' fixing: a)
  apply (subst register_from_getter_setter_of_getter_setter[symmetric])
  by (auto intro!: simp: register_from_getter_setter_def[abs_def])



end
