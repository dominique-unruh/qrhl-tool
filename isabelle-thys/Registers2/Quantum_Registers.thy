theory Quantum_Registers
imports
  Registers.Quantum_Extra2 Missing_Bounded_Operators
begin

subsection \<open>Raw\<close>

type_synonym 'a qupdate = \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
abbreviation \<open>qregister_raw \<equiv> Axioms_Quantum.register\<close>

lemma qregister_raw_1: \<open>qregister_raw F \<Longrightarrow> F id_cblinfun = id_cblinfun\<close>
  by simp
lemma qregister_raw_bounded_clinear: \<open>qregister_raw F \<Longrightarrow> bounded_clinear F\<close>
  by (rule Axioms_Quantum.register_bounded_clinear)
lemma qregister_raw_0: \<open>qregister_raw F \<Longrightarrow> F 0 = 0\<close>
  by (intro complex_vector.linear_0 bounded_clinear.clinear qregister_raw_bounded_clinear)
definition non_qregister_raw :: \<open>'a qupdate \<Rightarrow> 'b qupdate\<close> where \<open>non_qregister_raw a = 0\<close>
lemma qregister_raw_inj: \<open>qregister_raw F \<Longrightarrow> inj_on F X\<close>
  by (rule register_inj)
lemma non_qregister_raw: \<open>\<not> qregister_raw non_qregister_raw\<close>
  by (metis id_cblinfun_not_0 non_qregister_raw_def qregister_raw_1)

typedef ('a,'b) qregister = \<open>{f :: 'a qupdate \<Rightarrow> 'b qupdate. qregister_raw f} \<union> {non_qregister_raw}\<close>
  morphisms apply_qregister Abs_qregister by auto

subsection \<open>Registers\<close>

setup_lifting type_definition_qregister

lemma bounded_clinear_apply_qregister[simp]: \<open>bounded_clinear (apply_qregister F)\<close>
  apply transfer
  unfolding Axioms_Quantum.register_def
  by (auto simp: non_qregister_raw_def[abs_def])

lemma clinear_apply_qregister[simp]: \<open>clinear (apply_qregister F)\<close>
  using bounded_clinear.clinear bounded_clinear_apply_qregister by blast

lift_definition non_qregister :: \<open>('a,'b) qregister\<close> is non_qregister_raw by auto

lift_definition qregister :: \<open>('a,'b) qregister \<Rightarrow> bool\<close> is qregister_raw.


lemma non_qregister: \<open>\<not> qregister F \<longleftrightarrow> F = non_qregister\<close>
  apply transfer using non_qregister_raw by blast

lemma non_qregister'[simp]: \<open>\<not> qregister non_qregister\<close>
  by (simp add: non_qregister)

lemma apply_qregister_bounded_clinear: \<open>bounded_clinear (apply_qregister F)\<close>
  apply transfer by (auto simp add: qregister_raw_bounded_clinear non_qregister_raw_def[abs_def])

lemma apply_qregister_of_0[simp]: \<open>apply_qregister F 0 = 0\<close>
  by (metis non_qregister non_qregister.rep_eq non_qregister_raw_def qregister.rep_eq qregister_raw_0)

lemma apply_qregister_of_id[simp]: \<open>qregister F \<Longrightarrow> apply_qregister F id_cblinfun = id_cblinfun\<close>
  by (simp add: qregister.rep_eq qregister_raw_1)

lemma qregister_compose: \<open>apply_qregister F (a o\<^sub>C\<^sub>L b) = apply_qregister F a o\<^sub>C\<^sub>L apply_qregister F b\<close>
  apply (transfer fixing: a b)
  by (auto simp: non_qregister_raw_def Axioms_Quantum.register_mult)

lemma inj_qregister: \<open>inj (apply_qregister F)\<close> if \<open>qregister F\<close>
  using that apply transfer
  by (simp add: qregister_raw_inj)

lemma apply_qregister_scaleC: \<open>apply_qregister F (c *\<^sub>C A) = c *\<^sub>C apply_qregister F A\<close>
  using clinear_apply_qregister[of F]
  by (rule complex_vector.linear_scale)

lemma apply_qregister_scaleR: \<open>apply_qregister F (c *\<^sub>R A) = c *\<^sub>R apply_qregister F A\<close>
  by (simp add: apply_qregister_scaleC scaleR_scaleC)


lift_definition qregister_id :: \<open>('a,'a) qregister\<close> is id by simp

lemma apply_qregister_id[simp]: \<open>apply_qregister qregister_id = id\<close>
  by (rule qregister_id.rep_eq)

lemma qregister_id[simp]: \<open>qregister qregister_id\<close>
  apply transfer by simp



lift_definition empty_qregister :: \<open>('a::{CARD_1,enum}, 'b) qregister\<close> is
  Quantum_Extra2.empty_var
  by simp
lemma empty_qregister_is_register[simp]: \<open>qregister empty_qregister\<close>
  apply transfer by simp

abbreviation \<open>qregister_decomposition_basis F \<equiv> register_decomposition_basis (apply_qregister F)\<close>

definition qcommuting_raw :: \<open>('a qupdate \<Rightarrow> 'c qupdate) \<Rightarrow> ('b qupdate \<Rightarrow> 'c qupdate) \<Rightarrow> bool\<close> where
  \<open>qcommuting_raw F G \<longleftrightarrow> (\<forall>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a)\<close>

abbreviation \<open>qcompatible_raw \<equiv> Laws_Quantum.compatible\<close>
lemmas qcompatible_raw_def = Laws_Quantum.compatible_def

lift_definition qregister_pair :: \<open>('a,'c) qregister \<Rightarrow> ('b,'c) qregister \<Rightarrow> ('a\<times>'b, 'c) qregister\<close>
  is \<open>\<lambda>F G. if qcompatible_raw F G then Axioms_Quantum.register_pair F G else non_qregister_raw\<close>
  by simp

abbreviation (input) \<open>qcompatible F G \<equiv> qregister (qregister_pair F G)\<close>

lemma qcompatible_def: \<open>qcompatible F G \<longleftrightarrow> qregister F \<and> qregister G \<and> Laws_Quantum.compatible (apply_qregister F) (apply_qregister G)\<close>
  by (metis Laws_Quantum.compatible_register2 Laws_Quantum.compatible_sym Laws_Quantum.pair_is_register non_qregister_raw qregister.rep_eq qregister_pair.rep_eq)



lemma qcompatibleI: \<open>qregister F \<Longrightarrow> qregister G \<Longrightarrow> (\<And>a b. apply_qregister F a o\<^sub>C\<^sub>L apply_qregister G b = apply_qregister G b o\<^sub>C\<^sub>L apply_qregister F a) \<Longrightarrow> qcompatible F G\<close>
  apply transfer
  by (simp add: Laws_Quantum.compatible_def[abs_def])

lemma qcompatible_commute: 
  assumes \<open>qcompatible F G\<close>
  shows \<open>apply_qregister F a o\<^sub>C\<^sub>L apply_qregister G b = apply_qregister G b o\<^sub>C\<^sub>L apply_qregister F a\<close>
  by (metis Laws_Quantum.swap_registers assms non_qregister_raw qregister.rep_eq qregister_pair.rep_eq)

lemma apply_qregister_pair: \<open>qcompatible F G \<Longrightarrow>
  apply_qregister (qregister_pair F G) (a \<otimes>\<^sub>o b) = apply_qregister F a o\<^sub>C\<^sub>L  apply_qregister G b\<close>
  apply transfer
  using Laws_Quantum.register_pair_apply non_qregister_raw by auto

lemma empty_qregisters_same[simp]:
  fixes F :: \<open>('a::{CARD_1,enum},'b) qregister\<close>
  assumes [simp]: \<open>qregister F\<close>
  shows \<open>F = empty_qregister\<close>
proof (rule apply_qregister_inject[THEN iffD1], rule ext)
  fix a :: \<open>'a qupdate\<close>
  define empty :: \<open>('a,'b) qregister\<close> where \<open>empty = empty_qregister\<close>
  have [simp]: \<open>qregister empty\<close>
    using empty_qregister_is_register empty_def by blast

  have [simp]: \<open>clinear (apply_qregister F)\<close> \<open>clinear (apply_qregister empty)\<close>
    by (auto simp add: apply_qregister_bounded_clinear bounded_clinear.clinear)
  have \<open>apply_qregister F a = apply_qregister F (one_dim_iso a *\<^sub>C id_cblinfun)\<close>
    by simp
  also have \<open>\<dots> = one_dim_iso a *\<^sub>C apply_qregister F (id_cblinfun)\<close>
    by (metis \<open>clinear (apply_qregister F)\<close> complex_vector.linear_scale)
  also have \<open>\<dots> = one_dim_iso a *\<^sub>C id_cblinfun\<close>
    by (metis apply_qregister_of_id assms(1))
  also have \<open>\<dots> = one_dim_iso a *\<^sub>C apply_qregister empty (id_cblinfun)\<close>
    by (metis \<open>qregister empty\<close> apply_qregister_of_id)
  also have \<open>\<dots> = apply_qregister empty (one_dim_iso a *\<^sub>C id_cblinfun)\<close>
    by (metis \<open>clinear (apply_qregister empty)\<close> complex_vector.linear_scale)
  also have \<open>\<dots> = apply_qregister empty a\<close>
    by simp
  finally show \<open>apply_qregister F a = apply_qregister empty a\<close>
    by -
qed

lemma qcompatible_sym: \<open>qcompatible F G \<Longrightarrow> qcompatible G F\<close> for F :: \<open>('a,'c) qregister\<close> and G :: \<open>('b,'c) qregister\<close>
  apply transfer
  by (metis (mono_tags) Laws_Quantum.compatible_sym Laws_Quantum.pair_is_register non_qregister_raw)

lemma qcompatible3: \<open>qcompatible (qregister_pair F G) H \<longleftrightarrow> qcompatible F G \<and> qcompatible F H \<and> qcompatible G H\<close>
  unfolding qcompatible_def
  apply transfer
  apply (auto simp: non_qregister_raw)
  apply (metis Laws_Quantum.compatible_comp_left Laws_Quantum.register_Fst Laws_Quantum.register_pair_Fst)
  by (metis Laws_Quantum.compatible_comp_left Laws_Quantum.register_Snd Laws_Quantum.register_pair_Snd)

lemma qcompatible3': \<open>qcompatible H (qregister_pair F G) \<longleftrightarrow> qcompatible F G \<and> qcompatible H F \<and> qcompatible H G\<close>
  by (metis qcompatible3 qcompatible_sym)

lemma qcompatible_empty[simp]: \<open>qcompatible Q empty_qregister \<longleftrightarrow> qregister Q\<close>
  apply transfer
  using [[simproc del: Laws_Quantum.compatibility_warn]]
  apply (auto simp: non_qregister_raw)
  using qcompatible_raw_def
  by (auto simp: qcompatible_raw_def non_qregister_raw)

lemma qcompatible_empty'[simp]: \<open>qcompatible empty_qregister Q \<longleftrightarrow> qregister Q\<close>
  by (meson qcompatible_empty qcompatible_sym)

lemma qcompatible_register1: \<open>qcompatible F G \<Longrightarrow> qregister F\<close>
  apply transfer
  using [[simproc del: Laws_Quantum.compatibility_warn]]
  by (auto simp add: qcompatible_raw_def non_qregister_raw non_qregister_raw)

lemma qcompatible_register2: \<open>qcompatible F G \<Longrightarrow> qregister G\<close>
  apply transfer
  using [[simproc del: Laws_Quantum.compatibility_warn]]
  by (auto simp add: qcompatible_raw_def non_qregister_raw non_qregister_raw)

lemma qcompatible_non_qregister1[simp]: \<open>\<not> qcompatible non_qregister F\<close>
  apply transfer by (simp add: non_qregister_raw qcompatible_raw_def)
lemma qcompatible_non_qregister2[simp]: \<open>\<not> qcompatible F non_qregister\<close>
  apply transfer by (simp add: non_qregister_raw qcompatible_raw_def)

lift_definition qFst :: \<open>('a, 'a\<times>'b) qregister\<close> is \<open>Laws_Quantum.Fst\<close>
  by simp
lemma qFst_register[simp]: \<open>qregister qFst\<close>
  apply transfer by simp

lift_definition qSnd :: \<open>('b, 'a\<times>'b) qregister\<close> is \<open>Laws_Quantum.Snd\<close>
  by simp
lemma qSnd_register[simp]: \<open>qregister qSnd\<close>
  apply transfer by simp

lemma qcompatible_Fst_Snd[simp]: \<open>qcompatible qFst qSnd\<close>
  by (simp add: qFst.rep_eq qSnd.rep_eq qcompatible_def)


lift_definition qregister_chain :: \<open>('b,'c) qregister \<Rightarrow> ('a,'b) qregister \<Rightarrow> ('a,'c) qregister\<close>
  is \<open>\<lambda>F G. if qregister_raw F \<and> qregister_raw G then F o G else non_qregister_raw\<close>
  by simp


lemmas qregister_raw_chain = register_comp


lemma qregister_chain_apply: \<open>apply_qregister (qregister_chain F G) = apply_qregister F o apply_qregister G\<close>
  apply (rule ext) apply transfer
  by (auto simp: non_qregister_raw_def qregister_raw_0)
(* We limit this simplification rule to the case where F is neither Fst nor Snd because those cases are used commonly to encode indexed variables *)
lemma qregister_chain_apply_simp[simp]:
  assumes \<open>NO_MATCH qFst F\<close> \<open>NO_MATCH qSnd F\<close>
  shows \<open>apply_qregister (qregister_chain F G) = apply_qregister F o apply_qregister G\<close>
  by (rule qregister_chain_apply)

lemma qregister_id_chain[simp]: \<open>qregister_chain qregister_id F = F\<close>
  apply transfer by auto

lemma qregister_chain_id[simp]: \<open>qregister_chain F qregister_id = F\<close>
  apply transfer by auto

lemma qregister_chain_non_register1[simp]: \<open>qregister_chain non_qregister F = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)
lemma qregister_chain_non_register2[simp]: \<open>qregister_chain F non_qregister = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)

lemma qregister_chain_assoc: \<open>qregister_chain (qregister_chain F G) H = qregister_chain F (qregister_chain G H)\<close>
  apply (cases \<open>qregister F\<close>; cases \<open>qregister G\<close>; cases \<open>qregister H\<close>)
  apply (simp_all add: non_qregister)
  apply transfer
  by (auto simp add: qregister_raw_chain)

lemma qregister_chain_is_qregister[simp]: \<open>qregister (qregister_chain F G) \<longleftrightarrow> qregister F \<and> qregister G\<close>
  apply transfer
  by (auto simp: non_qregister_raw qregister_raw_chain)

lemma qregister_chain_pair_Fst[simp]: \<open>qcompatible F G \<Longrightarrow> qregister_chain (qregister_pair F G) qFst = F\<close>
  unfolding qcompatible_def apply transfer
  by (simp add: Laws_Quantum.register_pair_Fst)

lemma qregister_chain_pair_Fst_chain[simp]:
  assumes \<open>qcompatible F G\<close>
  shows \<open>qregister_chain (qregister_pair F G) (qregister_chain qFst H) = qregister_chain F H\<close>
  by (metis qregister_chain_pair_Fst assms qregister_chain_assoc)

lemma qregister_chain_pair_Snd[simp]: \<open>qcompatible F G \<Longrightarrow> qregister_chain (qregister_pair F G) qSnd = G\<close>
  unfolding qcompatible_def apply transfer
  by (simp add: Laws_Quantum.register_pair_Snd)

lemma qregister_chain_pair_Snd_chain[simp]:
  assumes \<open>qcompatible F G\<close>
  shows \<open>qregister_chain (qregister_pair F G) (qregister_chain qSnd H) = qregister_chain G H\<close>
  by (metis qregister_chain_pair_Snd assms qregister_chain_assoc)


lemma qregister_chain_empty_right[simp]: \<open>qregister F \<Longrightarrow> qregister_chain F empty_qregister = empty_qregister\<close>
  apply (rule empty_qregisters_same) by auto
lemma qregister_chain_empty_left[simp]: \<open>qregister F \<Longrightarrow> qregister_chain empty_qregister F = empty_qregister\<close>
  apply (rule empty_qregisters_same) by auto


lemma qcompatible_comp_left[simp]: "qcompatible F G \<Longrightarrow> qregister H \<Longrightarrow> qcompatible (qregister_chain F H) G"
  unfolding qcompatible_def apply transfer by auto

lemma qcompatible_comp_right[simp]: "qcompatible F G \<Longrightarrow> qregister H \<Longrightarrow> qcompatible F (qregister_chain G H)"
  by (meson qcompatible_comp_left qcompatible_sym)

lemmas qcompatible_Snd_Fst[simp] = qcompatible_Fst_Snd[THEN qcompatible_sym]

lemma qcompatible3I[simp]: \<open>qcompatible F G \<Longrightarrow> qcompatible G H \<Longrightarrow> qcompatible F H \<Longrightarrow> qcompatible (qregister_pair F G) H\<close>
  by (simp add: qcompatible3)

lemma qcompatible3I'[simp]: \<open>qcompatible F G \<Longrightarrow> qcompatible F H \<Longrightarrow> qcompatible G H \<Longrightarrow> qcompatible F (qregister_pair G H)\<close>
  by (simp add: qcompatible3')

definition \<open>qswap = qregister_pair qSnd qFst\<close>

lemma qregister_qswap[simp]: \<open>qregister qswap\<close>
  by (simp add: qcompatible_sym qswap_def)

lemma qregister_pair_qnonregister1[simp]: \<open>qregister_pair non_qregister F = non_qregister\<close>
  using non_qregister qcompatible_non_qregister1 by blast

lemma qregister_pair_qnonregister2[simp]: \<open>qregister_pair F non_qregister = non_qregister\<close>
  using non_qregister qcompatible_non_qregister2 by blast

lemma not_qcompatible_chain: 
  assumes \<open>\<not> qcompatible G H\<close>
  shows \<open>\<not> qcompatible (qregister_chain F G) (qregister_chain F H)\<close>
proof (rule notI)
  assume asm: \<open>qcompatible (qregister_chain F G) (qregister_chain F H)\<close>
  consider (FGH) \<open>qregister F\<close> \<open>qregister G\<close> \<open>qregister H\<close>
    | (nF) \<open>\<not> qregister F\<close> | (nG) \<open>\<not> qregister G\<close> | (nH) \<open>\<not> qregister H\<close>
    by auto
  then show False
  proof cases
    case FGH
    have \<open>apply_qregister F (apply_qregister G a o\<^sub>C\<^sub>L apply_qregister H b) = apply_qregister F (apply_qregister H b o\<^sub>C\<^sub>L apply_qregister G a)\<close> for a b
      using qcompatible_commute[OF asm]
      by (simp add: qregister_compose)
    moreover from FGH have \<open>inj (apply_qregister F)\<close>
      by (simp add: inj_qregister)
    ultimately have \<open>apply_qregister G a o\<^sub>C\<^sub>L apply_qregister H b = apply_qregister H b o\<^sub>C\<^sub>L apply_qregister G a\<close> for a b
      by (simp add: injD)
    then have \<open>qcompatible G H\<close>
      apply (rule_tac qcompatibleI)
      using FGH by auto
    with assms show False
      by simp
  next
    case nF with asm assms show ?thesis by (simp add: non_qregister)
  next
    case nG with asm assms show ?thesis by (simp add: non_qregister)
  next
    case nH with asm assms show ?thesis by (simp add: non_qregister)
  qed
qed

lemma qregister_chain_pair:
  shows \<open>qregister_chain F (qregister_pair G H) = qregister_pair (qregister_chain F G) (qregister_chain F H)\<close>
proof -
  consider (GH_F) \<open>qcompatible G H\<close> \<open>qregister F\<close> | (nF) \<open>F = non_qregister\<close> | (nGH) \<open>\<not> qcompatible G H\<close>
    by (auto simp flip: non_qregister)
  then show ?thesis
  proof cases
    case GH_F
    then show ?thesis
      unfolding qcompatible_def
      apply transfer
      by (simp add: Laws_Quantum.register_comp_pair)
  next
    case nF
    then show ?thesis
      by simp
  next
    case nGH
    then have \<open>\<not> qcompatible (qregister_chain F G) (qregister_chain F H)\<close>
      by (rule not_qcompatible_chain)
    then have [simp]: \<open>qregister_pair (qregister_chain F G) (qregister_chain F H) = non_qregister\<close>
      using non_qregister by auto
    from nGH have [simp]: \<open>qregister_pair G H = non_qregister\<close>
      using non_qregister by blast
    with nGH show ?thesis 
      by simp
  qed
qed

lemma apply_non_qregister[simp]: \<open>apply_qregister non_qregister x = 0\<close>
  by (simp add: non_qregister.rep_eq non_qregister_raw_def)

lemma qregister_chain_qswap_qswap[simp]: \<open>qregister_chain qswap qswap = qregister_id\<close>
  by (metis Laws_Quantum.compatible_Fst_Snd Laws_Quantum.pair_Fst_Snd apply_qregister_inverse qFst.rep_eq qSnd.rep_eq qcompatible_Snd_Fst qregister_chain_pair qregister_chain_pair_Fst qregister_chain_pair_Snd qregister_id.abs_eq qregister_pair.rep_eq qswap_def)


definition \<open>iso_qregister I \<longleftrightarrow> qregister I \<and> (\<exists>J. qregister J \<and> qregister_chain I J = qregister_id \<and> qregister_chain J I = qregister_id)\<close>

lift_definition qregister_inv :: \<open>('a,'b) qregister \<Rightarrow> ('b,'a) qregister\<close> is
  \<open>\<lambda>F. if qregister_raw (inv F) then inv F else non_qregister_raw\<close> by auto

lemma iso_qregister_inv_iso: \<open>iso_qregister I \<Longrightarrow> iso_qregister (qregister_inv I)\<close>
  unfolding iso_qregister_def apply transfer apply auto
  using non_qregister_raw apply fastforce
  using inv_unique_comp apply blast
  apply (simp add: inv_unique_comp)
  using inv_unique_comp by blast

lemma iso_qregister_inv_iso_apply: \<open>iso_qregister I \<Longrightarrow> apply_qregister (qregister_inv I) = inv (apply_qregister I)\<close>
  unfolding iso_qregister_def apply transfer using non_qregister_raw inv_unique_comp apply auto by blast

lemma iso_qregister_inv_chain: \<open>iso_qregister I \<Longrightarrow> qregister_chain (qregister_inv I) I = qregister_id\<close>
  apply (rule apply_qregister_inject[THEN iffD1], rule ext)
  apply simp
  by (smt (verit, del_insts) apply_qregister_id inv_unique_comp iso_qregister_def iso_qregister_inv_iso_apply pointfree_idE qregister_chain_apply)

lemma iso_qregister_chain_inv: \<open>iso_qregister I \<Longrightarrow> qregister_chain I (qregister_inv I) = qregister_id\<close>
  apply (rule apply_qregister_inject[THEN iffD1], rule ext)
  apply simp
  by (smt (verit, best) apply_qregister_id iso_qregister_def iso_qregister_inv_chain left_right_inverse_eq pointfree_idE qregister_chain_apply)

lemma qswap_iso[simp]: \<open>iso_qregister qswap\<close>
  by (auto intro!: exI[of _ qswap] simp: iso_qregister_def)

lemma qcompatible_chain[simp]: \<open>qregister F \<Longrightarrow> qcompatible G H \<Longrightarrow> qcompatible (qregister_chain F G) (qregister_chain F H)\<close>
  unfolding qcompatible_def apply transfer by simp  

lemma qcompatible_chain_iso: \<open>iso_qregister I \<Longrightarrow> qcompatible (qregister_chain I F) (qregister_chain I G) \<longleftrightarrow> qcompatible F G\<close>
  apply (cases \<open>qregister F\<close>; cases \<open>qregister G\<close>)
     apply (simp_all add: non_qregister)
  apply (rule iffI)
   apply (subst asm_rl[of \<open>F = qregister_chain (qregister_inv I) (qregister_chain I F)\<close>])
    apply (simp add: qregister_chain_assoc[symmetric] iso_qregister_inv_chain)
   apply (subst asm_rl[of \<open>G = qregister_chain (qregister_inv I) (qregister_chain I G)\<close>])
    apply (simp add: qregister_chain_assoc[symmetric] iso_qregister_inv_chain)
   apply (rule qcompatible_chain)
  using iso_qregister_def iso_qregister_inv_iso apply auto
  by (simp add: iso_qregister_def qcompatible_chain)

definition \<open>apply_qregister_space F S = apply_qregister F (Proj S) *\<^sub>S top\<close>

lemma apply_non_qregister_space[simp]: \<open>apply_qregister_space non_qregister x = 0\<close>
  by (simp add: apply_qregister_space_def)

(* TODO Duplicated by is_Proj_apply_qregister' *)
lemma qregister_projector: \<open>qregister F \<Longrightarrow> is_Proj a \<Longrightarrow> is_Proj (apply_qregister F a)\<close>
  apply (transfer fixing: a)
  by (rule register_projector)

lemma qregister_chain_apply_space: \<open>apply_qregister_space (qregister_chain F G) a = apply_qregister_space F (apply_qregister_space G a)\<close>
  apply (cases \<open>qregister G\<close>)
  by (simp_all add: apply_qregister_space_def[abs_def]
      qregister_chain_apply o_def Proj_on_own_range qregister_projector non_qregister)
(* We limit this simplification rule to the case where F is neither Fst nor Snd because those cases are used commonly to encode indexed variables *)
lemma qregister_chain_apply_space_simp[simp]:
  assumes \<open>NO_MATCH qFst F\<close> \<open>NO_MATCH qSnd F\<close> (* TODO do we still need this given that we restricted this rule to applied to a? *)
  shows \<open>apply_qregister_space (qregister_chain F G) a = apply_qregister_space F (apply_qregister_space G a)\<close>
  by (simp add: qregister_chain_apply_space)


lemma qregister_pair_chain_swap[simp]:
  "qregister_chain (qregister_pair A B) qswap = (qregister_pair B A)"
  apply (cases \<open>qcompatible A B\<close>)
   apply (auto simp: non_qregister qregister_chain_pair qswap_def)
  by (metis qcompatible_sym non_qregister)


(* TODO move *)
(* TODO: this should be applied in normalize_register_conv *)
lemma pair_fst_snd[simp]:
  shows \<open>qregister_pair qFst qSnd = qregister_id\<close>
  apply transfer
  using Laws_Quantum.pair_Fst_Snd by auto

lemma apply_qregister_weak_star_continuous[simp]:
  \<open>continuous_map weak_star_topology weak_star_topology (apply_qregister F)\<close>
  apply transfer
  by (auto simp: non_qregister_raw_def[abs_def] weak_star_cont_register)

lemma separating_butterket:
  \<open>Laws_Quantum.separating TYPE('b) (range (\<lambda>(x,y). butterfly (ket x) (ket y)))\<close>
proof -
  thm weak_star_clinear_eq_butterfly_ketI
  have \<open>F = G\<close> if \<open>\<And>a b. F (butterfly (ket a) (ket b)) = G (butterfly (ket a) (ket b))\<close> 
    and \<open>Axioms_Quantum.preregister F\<close> and \<open>Axioms_Quantum.preregister G\<close> for F G :: \<open>'a qupdate \<Rightarrow> 'b qupdate\<close>
    apply (rule weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
    using that
    by (auto simp: Axioms_Quantum.preregister_def bounded_clinear.clinear)
  then show ?thesis
    by (auto simp add: Laws_Quantum.separating_def)
qed

lemma separating_nonempty: \<open>\<not> (X \<subseteq> {0})\<close> if sep: \<open>separating TYPE('b) X\<close> for X :: \<open>'a qupdate set\<close>
proof (rule notI)
  assume \<open>X \<subseteq> {0}\<close>
  have \<open>Axioms_Quantum.preregister 0\<close>
    by (simp add: Axioms_Quantum.preregister_def zero_fun_def)
  fix x
  define F :: \<open>'a qupdate \<Rightarrow> 'b qupdate\<close> where \<open>F a = (ket x \<bullet>\<^sub>C (a *\<^sub>V ket x)) *\<^sub>C id_cblinfun\<close> for a
  have \<open>bounded_clinear F\<close>
    unfolding F_def[abs_def]
    by (intro bounded_linear_intros)
  moreover have \<open>continuous_map weak_star_topology weak_star_topology F\<close>
  proof -
    note continuous_map_compose[trans]
    have \<open>continuous_map weak_star_topology cweak_operator_topology (\<lambda>f :: 'a qupdate. f)\<close>
      by (simp add: wot_weaker_than_weak_star)
    also have \<open>continuous_map cweak_operator_topology euclidean (\<lambda>a. ket x \<bullet>\<^sub>C (a *\<^sub>V ket x))\<close>
      by (simp add: cweak_operator_topology_continuous_evaluation)
    also have \<open>continuous_map euclidean euclidean (\<lambda>c. c *\<^sub>C (id_cblinfun :: 'b qupdate))\<close>
      by (auto intro!: continuous_map_iff_continuous2[THEN iffD2] continuous_at_imp_continuous_on)
    also have \<open>continuous_map euclidean weak_star_topology (\<lambda>f :: 'b qupdate. f)\<close>
      by (simp add: weak_star_topology_weaker_than_euclidean)
    finally show ?thesis
      by (simp add: o_def F_def[abs_def])
  qed
  ultimately have \<open>Axioms_Quantum.preregister F\<close>
    by (simp add: Axioms_Quantum.preregister_def)
  have \<open>0 a = F a\<close> if \<open>a \<in> X\<close> for a
    using \<open>X \<subseteq> {0}\<close> that
    by (auto simp: F_def)
  with sep have \<open>0 = F\<close>
    by (simp add: Laws_Quantum.register_eqI \<open>Axioms_Quantum.preregister 0\<close> \<open>Axioms_Quantum.preregister F\<close>)
  then have \<open>0 (butterfly (ket x) (ket x)) = F (butterfly (ket x) (ket x))\<close>
    by simp
  then show False
    by (simp add: F_def)
qed

lemma qregister_eqI_separating:
  fixes F G :: \<open>('a,'b) qregister\<close>
  assumes sep: \<open>Laws_Quantum.separating TYPE('b) X\<close>
  assumes eq: \<open>\<And>x. x\<in>X \<Longrightarrow> apply_qregister F x = apply_qregister G x\<close>
  shows \<open>F = G\<close>
proof -
  obtain x where \<open>x \<in> X\<close> and \<open>x \<noteq> 0\<close>
    using separating_nonempty[OF sep]
    by auto

  consider (reg) \<open>qregister F\<close> \<open>qregister G\<close> | (notreg) \<open>\<not> qregister F\<close> \<open>\<not> qregister G\<close>
    | (notF) \<open>\<not> qregister F\<close> \<open>qregister G\<close> | (notG) \<open>qregister F\<close> \<open>\<not> qregister G\<close>
    by auto
  then show ?thesis
  proof cases
    case reg
    then show ?thesis
      using assms apply transfer
      by (auto simp: Laws_Quantum.separating_def)
  next
    case notreg
    then show ?thesis
      by (simp add: non_qregister)
  next
    case notF
    have \<open>apply_qregister F x = 0\<close>
      using non_qregister notF(1) by force
    moreover have \<open>apply_qregister G x \<noteq> 0\<close>
      using \<open>x \<noteq> 0\<close> inj_qregister[OF notF(2)] injD by fastforce
    moreover have \<open>apply_qregister F x = apply_qregister G x\<close>
      using eq \<open>x \<in> X\<close> by simp
    ultimately have False
      by simp
    then show ?thesis
      by simp
  next
    case notG
    have \<open>apply_qregister G x = 0\<close>
      using non_qregister notG(2) by force
    moreover have \<open>apply_qregister F x \<noteq> 0\<close>
      using \<open>x \<noteq> 0\<close> inj_qregister[OF notG(1)] injD by fastforce
    moreover have \<open>apply_qregister F x = apply_qregister G x\<close>
      using eq \<open>x \<in> X\<close> by simp
    ultimately have False
      by simp
    then show ?thesis
      by simp
  qed
qed

lemmas qregister_eqI_butterket = qregister_eqI_separating[OF separating_butterket]

lemma qregister_eqI_tensor_op:
  assumes \<open>\<And>a b. apply_qregister F (a \<otimes>\<^sub>o b) = apply_qregister G (a \<otimes>\<^sub>o b)\<close> 
  shows \<open>F = G\<close>
  apply (intro qregister_eqI_separating)
   apply (rule separating_tensor)
    apply (rule separating_UNIV)
   apply (rule separating_UNIV)
  using assms by auto

lift_definition transform_qregister :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>(U :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2). if unitary U then cblinfun_apply (sandwich U) else non_qregister_raw\<close>
  by (auto simp: unitary_sandwich_register)

lemma qregister_transform_qregister[simp]: \<open>unitary U \<Longrightarrow> qregister (transform_qregister U)\<close>
  apply (transfer fixing: U) by (auto simp: unitary_sandwich_register)

lemma apply_qregister_transform_qregister: \<open>unitary U \<Longrightarrow> apply_qregister (transform_qregister U) a = sandwich U a\<close>
  apply (transfer fixing: U a) by (auto simp: unitary_sandwich_register sandwich_apply)

lemma apply_qregister_plus: \<open>apply_qregister X (a+b) = apply_qregister X a + apply_qregister X b\<close>
  using clinear_apply_qregister[of X]
  by (rule complex_vector.linear_add)

lemma apply_qregister_space_of_0: \<open>apply_qregister_space F 0 = 0\<close>
  by (simp add: apply_qregister_space_def)

lemma apply_qregister_space_top: \<open>qregister F \<Longrightarrow> apply_qregister_space F \<top> = \<top>\<close>
  by (simp add: apply_qregister_space_def)

lemma apply_qregister_space_bot: \<open>apply_qregister_space F \<bottom> = \<bottom>\<close>
  by (simp add: apply_qregister_space_def)

lemma apply_qregister_space_scaleC: \<open>qregister F \<Longrightarrow> apply_qregister_space F (c *\<^sub>C A) = c *\<^sub>C apply_qregister_space F A\<close>
  apply (cases \<open>c = 0\<close>)
  by (simp_all add: apply_qregister_space_bot)

lemma apply_qregister_space_scaleR: \<open>qregister F \<Longrightarrow> apply_qregister_space F (c *\<^sub>R A) = c *\<^sub>R apply_qregister_space F A\<close>
  by (simp add: apply_qregister_space_scaleC scaleR_scaleC)

lemma apply_qregister_norm: \<open>qregister F \<Longrightarrow> norm (apply_qregister F A) = norm A\<close>
  by (simp add: qregister.rep_eq register_norm)

lemma apply_qregister_uminus: \<open>apply_qregister F (- A) = - apply_qregister F A\<close>
  apply (subst scaleC_minus1_left[symmetric])
  apply (subst (2) scaleC_minus1_left[symmetric])
  by (simp only: apply_qregister_scaleC)

lemma apply_qregister_minus: \<open>apply_qregister F (A - B) = apply_qregister F A - apply_qregister F B\<close>
  by (simp only: diff_conv_add_uminus apply_qregister_plus apply_qregister_uminus)

lemma apply_qregister_space_image: \<open>apply_qregister_space Q (A *\<^sub>S S) = apply_qregister Q A *\<^sub>S apply_qregister_space Q S\<close>
proof (cases \<open>qregister Q\<close>)
  case False
  then have \<open>Q = non_qregister\<close>
    by (simp add: non_qregister)
  then show ?thesis
    by simp
next
  let ?goal = ?thesis
  case True
  then have \<open>qregister_raw (apply_qregister Q)\<close>
    by (simp add: qregister.rep_eq)
  from register_decomposition[OF this]
  have \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis (apply_qregister Q). ?goal\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>U :: ('b \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2. 
              unitary U \<and> (\<forall>\<theta>. apply_qregister Q \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
    then obtain U :: \<open>('b \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> where
      [simp]: \<open>unitary U\<close> and decomp: \<open>apply_qregister Q \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun\<close> for \<theta>
      by auto
    have \<open>apply_qregister Q A *\<^sub>S apply_qregister_space Q S = apply_qregister Q A *\<^sub>S apply_qregister Q (Proj S) *\<^sub>S \<top>\<close>
      by (simp add: apply_qregister_space_def)
    also have \<open>\<dots> = U *\<^sub>S (A \<otimes>\<^sub>o id_cblinfun) *\<^sub>S (Proj S \<otimes>\<^sub>o id_cblinfun) *\<^sub>S U* *\<^sub>S \<top>\<close>
      by (simp add: decomp sandwich_apply lift_cblinfun_comp[OF unitaryD1] cblinfun_compose_image)
    also have \<open>\<dots> = U *\<^sub>S (A \<otimes>\<^sub>o id_cblinfun) *\<^sub>S (Proj S \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top>\<close>
      by simp
    also have \<open>\<dots> = U *\<^sub>S (A \<otimes>\<^sub>o id_cblinfun) *\<^sub>S (Proj S \<otimes>\<^sub>o id_cblinfun) *\<^sub>S (\<top> \<otimes>\<^sub>S \<top>)\<close>
      by simp
    also have \<open>\<dots> = U *\<^sub>S (A \<otimes>\<^sub>o id_cblinfun) *\<^sub>S ((Proj S *\<^sub>S \<top>) \<otimes>\<^sub>S \<top>)\<close>
      by (simp add: tensor_ccsubspace_via_Proj)
    also have \<open>\<dots> = U *\<^sub>S ((A *\<^sub>S Proj S *\<^sub>S \<top>) \<otimes>\<^sub>S \<top>)\<close>
      by (metis cblinfun_image_id tensor_ccsubspace_image)
    also have \<open>\<dots> = U *\<^sub>S ((Proj (A *\<^sub>S S) *\<^sub>S \<top>) \<otimes>\<^sub>S \<top>)\<close>
      by simp
    also have \<open>\<dots> = U *\<^sub>S (Proj (A *\<^sub>S S) \<otimes>\<^sub>o id_cblinfun) *\<^sub>S (\<top> \<otimes>\<^sub>S \<top>)\<close>
      by (simp add: tensor_ccsubspace_via_Proj)
    also have \<open>\<dots> = U *\<^sub>S (Proj (A *\<^sub>S S) \<otimes>\<^sub>o id_cblinfun) *\<^sub>S U* *\<^sub>S \<top>\<close>
      by simp
    also have \<open>\<dots> = apply_qregister Q (Proj (A *\<^sub>S S)) *\<^sub>S \<top>\<close>
      by (simp add: cblinfun_compose_image decomp sandwich_apply)
    also have \<open>\<dots> = apply_qregister_space Q (A *\<^sub>S S)\<close>
      by (simp add: apply_qregister_space_def)
    finally show ?goal
      by simp
  qed
  from this[cancel_with_type]
  show ?thesis 
    by -
qed

lemma apply_qregister_inject': \<open>apply_qregister F a = apply_qregister F b \<longleftrightarrow> a = b\<close> if \<open>qregister F\<close>
  using that apply (transfer fixing: a b)
  using qregister_raw_inj[of _ UNIV] injD by fastforce

lemma apply_qregister_adj: \<open>apply_qregister F (A*) = (apply_qregister F A)*\<close>
  apply (cases \<open>qregister F\<close>)
   apply transfer
  by (auto simp add: register_adj non_qregister)

lemma apply_qregister_unitary[simp]: \<open>unitary (apply_qregister F U) \<longleftrightarrow> unitary U\<close> if \<open>qregister F\<close>
  unfolding unitary_def
  apply (subst apply_qregister_inject'[symmetric, OF that, of \<open>U* o\<^sub>C\<^sub>L U\<close>])
  apply (subst apply_qregister_inject'[symmetric, OF that, of \<open>U o\<^sub>C\<^sub>L U*\<close>])
  by (simp add: apply_qregister_adj qregister_compose that del: isometryD)

lemma apply_qregister_isometry[simp]: \<open>isometry (apply_qregister F U) \<longleftrightarrow> isometry U\<close> if \<open>qregister F\<close>
  unfolding isometry_def
  apply (subst apply_qregister_inject'[symmetric, OF that, of \<open>U* o\<^sub>C\<^sub>L U\<close>])
  by (simp add: apply_qregister_adj qregister_compose that del: isometryD)

lemma apply_qregister_is_Proj': \<open>is_Proj P \<Longrightarrow> is_Proj (apply_qregister F P)\<close>
  apply (transfer fixing: P)
  by (auto simp add: register_projector non_qregister_raw_def)

lemma apply_qregister_is_Proj[simp]: \<open>is_Proj (apply_qregister F P) \<longleftrightarrow> is_Proj P\<close> if \<open>qregister F\<close>
  using that
  by (auto simp add: is_Proj_algebraic apply_qregister_inject apply_qregister_inject' 
      simp flip: qregister_compose apply_qregister_adj)

lemma apply_qregister_Proj: \<open>apply_qregister F (Proj S) = Proj (apply_qregister_space F S)\<close>
  by (simp add: Proj_on_own_range apply_qregister_space_def apply_qregister_is_Proj')


lemma apply_qregister_partial_isometry: \<open>qregister F \<Longrightarrow> partial_isometry (apply_qregister F U) \<longleftrightarrow> partial_isometry U\<close>
  by (simp add: partial_isometry_iff_square_proj flip: apply_qregister_adj qregister_compose)

lemma apply_qregister_mono: 
  assumes [simp]: \<open>qregister Q\<close>
  shows \<open>apply_qregister Q A \<le> apply_qregister Q B \<longleftrightarrow> A \<le> B\<close>
proof (rule iffI)
  assume \<open>A \<le> B\<close>
  then obtain C :: \<open>'a qupdate\<close> where \<open>B - A = C* o\<^sub>C\<^sub>L C\<close>
    by (metis diff_ge_0_iff_ge positive_hermitianI sqrt_op_pos sqrt_op_square)
  then have \<open>apply_qregister Q B - apply_qregister Q A = (apply_qregister Q C)* o\<^sub>C\<^sub>L apply_qregister Q C\<close>
    by (metis apply_qregister_adj apply_qregister_minus qregister_compose)
  then show \<open>apply_qregister Q A \<le> apply_qregister Q B\<close>
    by (metis diff_ge_0_iff_ge positive_cblinfun_squareI)
next
  assume asm: \<open>apply_qregister Q A \<le> apply_qregister Q B\<close>
  have [simp]: \<open>qregister_raw (apply_qregister Q)\<close>
    using assms qregister.rep_eq by blast
  from register_decomposition[OF this]
  have \<open>\<forall>\<^sub>\<tau> 'z::type = register_decomposition_basis (apply_qregister Q). A \<le> B\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>U::('a \<times> 'z) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. apply_qregister Q \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
    then obtain U :: \<open>('a \<times> 'z) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where
      [simp]: \<open>unitary U\<close> and decomp: \<open>apply_qregister Q \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun\<close> for \<theta>
      by auto
    show \<open>A \<le> B\<close>
    proof (rule cblinfun_leI)
      fix x
      obtain y :: \<open>'z ell2\<close> where \<open>norm y = 1\<close>
        by (meson norm_ket)
      define BA where \<open>BA = B - A\<close>
      from asm have QBA_pos: \<open>apply_qregister Q BA \<ge> 0\<close>
        by (simp add: BA_def apply_qregister_minus)
      have \<open>x \<bullet>\<^sub>C (BA *\<^sub>V x) = (x \<otimes>\<^sub>s y) \<bullet>\<^sub>C ((BA \<otimes>\<^sub>o id_cblinfun) *\<^sub>V (x \<otimes>\<^sub>s y))\<close>
        using \<open>norm y = 1\<close> by (simp add: tensor_op_ell2 cnorm_eq_1)
      also have \<open>\<dots> = (U *\<^sub>V (x \<otimes>\<^sub>s y)) \<bullet>\<^sub>C (apply_qregister Q BA *\<^sub>V U *\<^sub>V (x \<otimes>\<^sub>s y))\<close>
        by (simp add: decomp sandwich_apply lift_cblinfun_comp[OF unitaryD1]
            flip: cinner_adj_right)
      also have \<open>\<dots> \<ge> 0\<close>
        by (meson QBA_pos cinner_pos_if_pos)
      finally show \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<le> x \<bullet>\<^sub>C (B *\<^sub>V x)\<close>
        by (simp add: BA_def cblinfun.diff_left cinner_diff_right apply_qregister_minus)
    qed
  qed
  with this[cancel_with_type]
  show \<open>A \<le> B\<close>
    by -
qed

lemma apply_qregister_space_mono: \<open>qregister F \<Longrightarrow> apply_qregister_space F A \<le> apply_qregister_space F B \<longleftrightarrow> A \<le> B\<close>
  by (simp add: apply_qregister_space_def Proj_on_own_range apply_qregister_mono
      flip: Proj_mono)

lemma apply_qregister_space_inject': \<open>apply_qregister_space F a = apply_qregister_space F b \<longleftrightarrow> a = b\<close> if \<open>qregister F\<close>
  by (simp add: apply_qregister_space_mono order_class.order_eq_iff that)

lemma apply_qregister_space_uminus: \<open>qregister F \<Longrightarrow> apply_qregister_space F (- A) = - apply_qregister_space F A\<close>
  apply (simp only: apply_qregister_space_def Proj_ortho_compl apply_qregister_minus apply_qregister_of_id)
  by (simp only: apply_qregister_Proj Proj_range flip: Proj_ortho_compl)

lemma apply_qregister_space_INF: 
  assumes [simp]: \<open>qregister F\<close>
  shows "apply_qregister_space F (INF x\<in>X. S x) = (INF x\<in>X. apply_qregister_space F (S x))"
proof (cases \<open>X = {}\<close>)
  case True
  then show ?thesis
    by (simp add: apply_qregister_space_top)
next
  let ?goal = ?thesis
  case False
  have \<open>qregister_raw (apply_qregister F)\<close>
    using assms qregister.rep_eq by blast
  from register_decomposition[OF this]
  have \<open>\<forall>\<^sub>\<tau> 'z::type = register_decomposition_basis (apply_qregister F).
        ?goal\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>U::('a \<times> 'z) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. apply_qregister F \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
    then obtain U :: \<open>('a \<times> 'z) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where
      [simp]: \<open>unitary U\<close> and decomp: \<open>apply_qregister F \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun\<close> for \<theta>
      by auto
    from tensor_ccsubspace_INF_left[where X=X and T=\<open>\<top> :: 'z ell2 ccsubspace\<close> and S=S]
    have ?goal if \<open>X \<noteq> {}\<close>
      by (simp add: apply_qregister_space_def decomp sandwich_apply cblinfun_compose_image
          unitary_isometry tensor_ccsubspace_via_Proj False
          flip: cblinfun_image_INF_eq)
    moreover have ?goal if \<open>X = {}\<close>
      using False that by auto
    ultimately show ?goal
      apply (cases \<open>X = {}\<close>) by auto
  qed
  from this[cancel_with_type]
  show ?thesis
    by auto
qed

lemma apply_qregister_space_SUP: "apply_qregister_space F (SUP x\<in>X. S x) = (SUP x\<in>X. apply_qregister_space F (S x))"
  apply (cases \<open>qregister F\<close>)
   apply (rule complement_injective)
   apply (simp add: uminus_SUP apply_qregister_space_INF flip: apply_qregister_space_uminus)
  by (simp add: non_qregister)

lemma apply_qregister_space_inf: \<open>apply_qregister_space F (A \<sqinter> B) = apply_qregister_space F A \<sqinter> apply_qregister_space F B\<close>
  apply (cases \<open>qregister F\<close>)
  using apply_qregister_space_INF[where F=F and X=\<open>{True,False}\<close> and S=\<open>\<lambda> True \<Rightarrow> A | False \<Rightarrow> B\<close>]
  by (auto simp: non_qregister)

lemma apply_qregister_space_sup: \<open>apply_qregister_space F (A \<squnion> B) = apply_qregister_space F A \<squnion> apply_qregister_space F B\<close>
  using apply_qregister_space_SUP[where F=F and X=\<open>{True,False}\<close> and S=\<open>\<lambda> True \<Rightarrow> A | False \<Rightarrow> B\<close>]
  by simp

lemma apply_qregister_space_plus: \<open>apply_qregister_space F (A + B) = apply_qregister_space F A + apply_qregister_space F B\<close>
  by (simp add: plus_ccsubspace_def apply_qregister_space_sup)

lemma apply_qregister_space_minus: \<open>apply_qregister_space F (A - B) = apply_qregister_space F A - apply_qregister_space F B\<close>
  apply (cases \<open>qregister F\<close>)
  by (simp_all add: complemented_lattice_class.diff_eq apply_qregister_space_inf apply_qregister_space_uminus
      non_qregister)

lemma apply_qregister_space_kernel: \<open>qregister F \<Longrightarrow> apply_qregister_space F (Complex_Bounded_Linear_Function.kernel A) = Complex_Bounded_Linear_Function.kernel (apply_qregister F A)\<close>
  by (metis (no_types, lifting) Proj_on_image Proj_top apply_qregister_adj apply_qregister_of_id apply_qregister_space_def apply_qregister_space_image apply_qregister_space_uminus kernel_compl_adj_range)

lemma apply_qregister_space_eigenspace: \<open>qregister F \<Longrightarrow> apply_qregister_space F (eigenspace c A) = eigenspace c (apply_qregister F A)\<close>
  by (simp add: apply_qregister_minus apply_qregister_scaleC apply_qregister_space_kernel eigenspace_def)

lemma apply_qregister_space_orthogonal_spaces: \<open>qregister F \<Longrightarrow> orthogonal_spaces (apply_qregister_space F A) (apply_qregister_space F B) = orthogonal_spaces A B\<close>
  by (metis apply_qregister_space_mono apply_qregister_space_uminus orthogonal_spaces_leq_compl)

lemma apply_qregister_pos: \<open>apply_qregister F A \<ge> 0 \<longleftrightarrow> A \<ge> 0\<close> if \<open>qregister F\<close>
  by (metis that apply_qregister_mono apply_qregister_of_0)

lemma apply_qregister_abs_op: \<open>apply_qregister F (abs_op A) = abs_op (apply_qregister F A)\<close>
proof (cases \<open>qregister F\<close>)
  case True
  note [simp] = this
  show ?thesis
    apply (rule abs_opI)
    by (simp_all add: abs_op_square abs_op_pos apply_qregister_pos flip: apply_qregister_adj qregister_compose
        del: adj_abs_op)
next
  case False
  then show ?thesis
    by (simp add: non_qregister)
qed

lemma apply_qregister_sqrt_op: \<open>apply_qregister F (sqrt_op A) = sqrt_op (apply_qregister F A)\<close>
proof (cases \<open>qregister F\<close>)
  case True
  note posA[simp] = this
  show ?thesis
  proof (cases \<open>A \<ge> 0\<close>)
    case True
    then have posFA: \<open>0 \<le> apply_qregister F (sqrt_op A)\<close>
      by (simp add: apply_qregister_pos)
    have sq: \<open>apply_qregister F (sqrt_op A)* o\<^sub>C\<^sub>L apply_qregister F (sqrt_op A) = apply_qregister F A\<close>
      using True by (simp_all add: abs_op_square positive_hermitianI flip: apply_qregister_adj qregister_compose)
    from posFA sq
    show ?thesis
      by (rule sqrt_op_unique)
  next
    case False
    then have 1: \<open>sqrt_op A = 0\<close>
      by (rule sqrt_op_nonpos)
    from False
    have \<open>\<not> (0 \<le> apply_qregister F A)\<close>
      by (simp add: apply_qregister_pos)
    then have 2: \<open>sqrt_op (apply_qregister F A) = 0\<close>
      by (rule sqrt_op_nonpos)
    from 1 2
    show ?thesis 
      by simp
  qed
next
  case False
  then show ?thesis
    by (simp add: non_qregister)
qed 

lemma apply_qregister_polar_decomposition: \<open>apply_qregister F (polar_decomposition A) = polar_decomposition (apply_qregister F A)\<close>
proof (cases \<open>qregister F\<close>)
  case True
  define PA FPA where \<open>PA = polar_decomposition A\<close> and \<open>FPA = apply_qregister F PA\<close>
  have \<open>kernel (apply_qregister F (polar_decomposition A)) = kernel (apply_qregister F A)\<close>
    by (metis True apply_qregister_space_kernel polar_decomposition_initial_space)
  moreover have \<open>apply_qregister F (polar_decomposition A) o\<^sub>C\<^sub>L abs_op (apply_qregister F A) = apply_qregister F A\<close>
    by (metis apply_qregister_abs_op polar_decomposition_correct qregister_compose)
  ultimately show ?thesis
    by (rule polar_decomposition_unique)
next
  case False
  then show ?thesis 
    by (simp add: polar_decomposition_0 non_qregister)
qed

(* lift_definition ccomplements :: \<open>('a,'c) cregister \<Rightarrow> ('b,'c) cregister \<Rightarrow> bool\<close> is complements. *)
lift_definition qcomplements :: \<open>('a,'c) qregister \<Rightarrow> ('b,'c) qregister \<Rightarrow> bool\<close> is complements.

lemma qcomplements_def': \<open>qcomplements F G \<longleftrightarrow> iso_qregister (qregister_pair F G)\<close>
(* TODO "qcompatible F G" can be dropped *)
  unfolding iso_qregister_def apply transfer 
  by (auto simp: complements_def Laws_Quantum.iso_register_def non_qregister_raw)

  (* TODO move to Prog_Variables *)
  (* TODO same for cregister *)
lemma qregister_raw_apply_qregister: \<open>qregister_raw (apply_qregister X) \<longleftrightarrow> qregister X\<close>
  apply transfer by simp

lemma qregister_Abs_qregister: \<open>qregister_raw F \<Longrightarrow> qregister (Abs_qregister F)\<close>
  by (simp add: Abs_qregister_inverse flip: qregister_raw_apply_qregister)
  
lemma qregister_apply_Abs: \<open>qregister_raw F \<Longrightarrow> apply_qregister (Abs_qregister F) = F\<close>
  by (simp add: Abs_qregister_inverse)

lemma qregister_unitary: \<open>qregister F \<Longrightarrow> unitary U \<Longrightarrow> unitary (apply_qregister F U)\<close>
  apply (transfer fixing: U) by (rule register_unitary)

lemma apply_qregister_empty_qregister[simp]: \<open>apply_qregister empty_qregister A = one_dim_iso A *\<^sub>C id_cblinfun\<close>
  by (simp add: empty_qregister.rep_eq empty_var_def)

(* TODO write lemma (proof in quicksheets 2023 p32)
lemma qregister_invertible_op:
assumes \<open>qregister F\<close>
shows \<open>F X invertible \<longleftrightarrow> X invertible\<close> *)

lemma apply_qregister_space_transform_qregister:
  assumes [simp]: \<open>unitary U\<close>
  shows \<open>apply_qregister_space (transform_qregister U) S = U *\<^sub>S S\<close>
  by (simp add: apply_qregister_transform_qregister apply_qregister_space_def Proj_sandwich)

lemma apply_qregister_qFst: \<open>apply_qregister qFst a = a \<otimes>\<^sub>o id_cblinfun\<close>
  by (simp add: Laws_Quantum.Fst_def qFst.rep_eq)

lemma apply_qregister_qSnd: \<open>apply_qregister qSnd b = id_cblinfun \<otimes>\<^sub>o b\<close>
  by (simp add: Laws_Quantum.Snd_def qSnd.rep_eq)

lemma apply_qregister_image: "apply_qregister Q U *\<^sub>S top = apply_qregister_space Q (U *\<^sub>S top)"
  apply (cases \<open>qregister Q\<close>)
  by (simp_all add: apply_qregister_space_image apply_qregister_space_top non_qregister)
lemma applyOpSpace_lift: "apply_qregister Q U *\<^sub>S apply_qregister_space Q S = apply_qregister_space Q (U *\<^sub>S S)"
  thm apply_qregister_space_image
   by (simp flip: apply_qregister_space_image)

lemma apply_qregister_space_qFst: \<open>apply_qregister_space qFst S = S \<otimes>\<^sub>S \<top>\<close>
  by (simp add: apply_qregister_space_def tensor_ccsubspace_via_Proj apply_qregister_qFst flip: apply_qregister_image)

lemma apply_qregister_space_qSnd: \<open>apply_qregister_space qSnd S = \<top> \<otimes>\<^sub>S S\<close>
  by (simp add: apply_qregister_space_def tensor_ccsubspace_via_Proj apply_qregister_qSnd flip: apply_qregister_image)

lemma apply_qregister_fst: \<open>apply_qregister qFst a = a \<otimes>\<^sub>o id_cblinfun\<close>
  by (simp add: Laws_Quantum.Fst_def qFst.rep_eq)

lemma apply_qregister_snd: \<open>apply_qregister qSnd a = id_cblinfun \<otimes>\<^sub>o a\<close>
  by (simp add: Laws_Quantum.Snd_def qSnd.rep_eq)

lemma apply_qregister_qswap: \<open>apply_qregister qswap (a \<otimes>\<^sub>o b) = b \<otimes>\<^sub>o a\<close>
  by (simp add: qswap_def apply_qregister_pair apply_qregister_fst apply_qregister_snd
      comp_tensor_op)

lemma transform_qregister_swap_ell2: \<open>transform_qregister swap_ell2 = qswap\<close>
  apply (rule qregister_eqI_tensor_op)
  by (auto simp: apply_qregister_transform_qregister apply_qregister_qswap
      swap_tensor_op sandwich_apply)

lemma apply_qregister_space_id[simp]: \<open>apply_qregister_space qregister_id S = S\<close>
  by (simp add: apply_qregister_space_def)

lift_definition qregister_tensor :: \<open>('a,'b) qregister \<Rightarrow> ('c,'d) qregister \<Rightarrow> ('a\<times>'c, 'b\<times>'d) qregister\<close> is
  \<open>\<lambda>F G. if qregister_raw F \<and> qregister_raw G then Laws_Quantum.register_tensor F G else non_qregister_raw\<close>
  by (auto simp: non_qregister_raw Laws_Quantum.register_tensor_is_register)

lemma qcompatible_raw_non_qregister_raw_left[simp]: \<open>\<not> qcompatible_raw non_qregister_raw F\<close>
  using non_qregister_raw qcompatible_raw_def by blast

lemma qcompatible_raw_non_qregister_raw_right[simp]: \<open>\<not> qcompatible_raw F non_qregister_raw\<close>
  using non_qregister_raw qcompatible_raw_def by blast

lemma qregister_pair_chain_left: \<open>qcompatible F G \<Longrightarrow> qregister_pair (qregister_chain F H) G = qregister_chain (qregister_pair F G) (qregister_tensor H qregister_id)\<close>
  unfolding qcompatible_def
  apply transfer
  by (simp add: register_tensor_is_register pair_o_tensor non_qregister_raw)
lemma qregister_pair_chain_right: \<open>qcompatible F G \<Longrightarrow> qregister_pair F (qregister_chain G H) = qregister_chain (qregister_pair F G) (qregister_tensor qregister_id H)\<close>
  unfolding qcompatible_def
  apply transfer
  by (simp add: register_tensor_is_register pair_o_tensor non_qregister_raw)

lemma qregister_tensor_non_qregister_left[simp]: \<open>qregister_tensor non_qregister F = non_qregister\<close>
  apply transfer by (auto simp: non_qregister_raw)
lemma qregister_tensor_non_qregister_right[simp]: \<open>qregister_tensor F non_qregister = non_qregister\<close>
  apply transfer by (auto simp: non_qregister_raw)

lemma qregister_tensor_apply:
  \<open>apply_qregister (qregister_tensor F G) (a \<otimes>\<^sub>o b) = apply_qregister F a \<otimes>\<^sub>o apply_qregister G b\<close>
  apply (cases \<open>qregister F\<close>; cases \<open>qregister G\<close>)
     apply (auto simp: non_qregister)
  apply transfer
  by simp

lemma qregister_tensor_transform_qregister:
  assumes [simp]: \<open>unitary U\<close> \<open>unitary V\<close>
  shows \<open>qregister_tensor (transform_qregister U) (transform_qregister V)
            = transform_qregister (U \<otimes>\<^sub>o V)\<close>
  apply (rule qregister_eqI_tensor_op)
  by (simp add: qregister_tensor_apply apply_qregister_transform_qregister unitary_tensor_op sandwich_tensor_op)

lemma transform_qregister_non_unitary: \<open>\<not> unitary U \<Longrightarrow> transform_qregister U = non_qregister\<close>
  apply (transfer fixing: U) by simp

lemma transform_qregister_id: \<open>transform_qregister id_cblinfun = qregister_id\<close>
  apply (rule apply_qregister_inject[THEN iffD1])
  by (auto intro!: ext simp add: apply_qregister_transform_qregister)


(* TODO _id2 (other side) *)
lemma qregister_tensor_transform_qregister_id1:
  \<open>qregister_tensor (transform_qregister U) qregister_id
            = transform_qregister (U \<otimes>\<^sub>o id_cblinfun)\<close>
proof (cases \<open>unitary U\<close>)
  case True
  note [simp] = True
  have \<open>qregister_tensor (transform_qregister U) qregister_id
      = qregister_tensor (transform_qregister U) (transform_qregister id_cblinfun)\<close>
    by (simp add: transform_qregister_id)
  also have \<open>\<dots> = transform_qregister (U \<otimes>\<^sub>o id_cblinfun)\<close>
    by (simp add: qregister_tensor_transform_qregister)
  finally show ?thesis
    by -
next
  case False
  then show ?thesis
    by (simp add: transform_qregister_non_unitary)
qed

lemma qregister_chain_transform_qregister:
  assumes [simp]: \<open>unitary U\<close> \<open>unitary V\<close>
  shows \<open>qregister_chain (transform_qregister U) (transform_qregister V) = transform_qregister (U o\<^sub>C\<^sub>L V)\<close>
  by (auto intro!: ext apply_qregister_inject[THEN iffD1]
      simp: apply_qregister_transform_qregister sandwich_compose
      simp flip: cblinfun_apply_cblinfun_compose)

lemma register_range_complement_commutant: \<open>commutant (range F) = range G\<close> if \<open>complements F G\<close>
  apply (rule complement_range[symmetric])
  using that by (simp_all add: complements_def)

lemma qcomplements_via_rangeI:
  assumes \<open>qregister F\<close>
  assumes \<open>range (apply_qregister G) = commutant (range (apply_qregister F))\<close>
  shows \<open>qcomplements F G\<close>
proof (cases \<open>qregister G\<close>)
  case True
  have \<open>qregister_raw (apply_qregister F)\<close>
    using assms(1) by (auto simp: qregister_raw_apply_qregister)
  from complement_exists[OF this]
  have \<open>\<forall>\<^sub>\<tau> 'g::type = qregister_decomposition_basis F. qcomplements F G\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>G :: 'g qupdate \<Rightarrow> _. complements (apply_qregister F) G\<close>
    then obtain G' :: \<open>'g qupdate \<Rightarrow> _\<close> where compl: \<open>complements (apply_qregister F) G'\<close>
      by auto
    then have \<open>range G' = commutant (range (apply_qregister F))\<close>
      by (simp add: register_range_complement_commutant)
    with assms have \<open>range G' = range (apply_qregister G)\<close>
      by simp
    then have \<open>equivalent_registers (apply_qregister G) G'\<close>
      by (metis Laws_Complement_Quantum.complement_unique Laws_Quantum.equivalent_registers_register_right True compl qregister.rep_eq same_range_equivalent)
    with compl have \<open>complements (apply_qregister F) (apply_qregister G)\<close>
      using Laws_Quantum.equivalent_registers_sym equivalent_complements by blast
    then show \<open>qcomplements F G\<close>
      by (simp add: qcomplements.rep_eq)
  qed
  from this[cancel_with_type]
  show ?thesis 
    by -
next
  case False
  then have \<open>id_cblinfun \<notin> range (apply_qregister G)\<close>
    by (simp add: non_qregister)
  moreover have \<open>id_cblinfun \<in> commutant (range (apply_qregister F))\<close>
    by simp
  ultimately have False
    using assms by metis
  then show ?thesis
    by simp
qed

lemma qcomplement_exists:
  fixes F :: \<open>('a,'b) qregister\<close>
  assumes \<open>qregister F\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'c::type = qregister_decomposition_basis F.
          \<exists>G :: ('c,'b) qregister. qcomplements F G\<close>
proof -
  have *: \<open>(\<exists>G :: 'c qupdate \<Rightarrow> 'b qupdate. complements (apply_qregister F) G)
    \<longleftrightarrow> (\<exists>G :: ('c,'b) qregister. qcomplements F G)\<close>
    apply (rule Ex_iffI[where f=Abs_qregister and g=apply_qregister])
    by (auto simp: qcomplements_def complements_def Abs_qregister_inverse
        Abs_qregister_inverse Laws_Quantum.compatible_register2)
  show ?thesis
    apply (subst *[symmetric])
    apply (rule complement_exists)
    using assms by (simp add: qregister_raw_apply_qregister)
qed

(* TODO same for cregister *)
lemma qregister_left_right_inverse:
  assumes \<open>qregister_chain A B = qregister_id\<close>
  shows \<open>qregister_chain B A = qregister_id\<close>
proof -
  from assms
  have \<open>qregister A\<close> and \<open>qregister B\<close>
    by (metis qregister_chain_is_qregister qregister_id)+
  with assms show ?thesis
  apply transfer
    apply auto
  by (metis inj_iff isomorphism_expand pointfree_idE qregister_raw_inj)
qed


end
