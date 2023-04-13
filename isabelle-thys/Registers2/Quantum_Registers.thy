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


end
