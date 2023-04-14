theory Quantum_Reg_Conversions
  imports Quantum_Reg_Ranges
begin

lemmas qregister_conversion_raw_register = register_inv_G_o_F
(* lemma qregister_conversion_raw_register: \<open>qregister_raw F \<Longrightarrow> qregister_raw G \<Longrightarrow> range F \<subseteq> range G \<Longrightarrow> qregister_raw (inv G \<circ> F)\<close> *)


lift_definition qregister_conversion :: \<open>('a,'c) qregister \<Rightarrow> ('b,'c) qregister \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>F G. if qregister_raw F \<and> qregister_raw G \<and> range F \<subseteq> range G then inv G o F else non_qregister_raw\<close>
  by (auto intro: qregister_conversion_raw_register)


lemma qregister_conversion_register: \<open>qregister_le F G \<Longrightarrow> qregister (qregister_conversion F G)\<close>
  apply (auto intro!: qregister_conversion_raw_register 
      simp add: qregister_le_def less_eq_QREGISTER_def QREGISTER_of.rep_eq
      qregister.rep_eq qregister_conversion.rep_eq)
  by auto

lemma qregister_chain_conversion: \<open>qregister_le F G  \<Longrightarrow> qregister_chain G (qregister_conversion F G) = F\<close>
  unfolding qregister_le_def
  apply (transfer fixing: F G)
  apply transfer
  by (auto simp: non_qregister_raw qregister_conversion_raw_register f_inv_into_f in_mono intro!: ext)


lemma qregister_apply_conversion:
  assumes \<open>qregister_le F G\<close>
  shows \<open>apply_qregister F x = apply_qregister G (apply_qregister (qregister_conversion F G) x)\<close>
  using assms apply (subst qregister_chain_conversion[where F=F and G=G, symmetric])
  by auto

lemma apply_qregister_space_conversion:
  assumes [simp]: \<open>qregister_le F G\<close>
  shows \<open>apply_qregister_space F S = apply_qregister_space G (apply_qregister_space (qregister_conversion F G) S)\<close>
  by (simp add: apply_qregister_space_def qregister_apply_conversion[OF assms] Proj_on_own_range
      qregister_projector qregister_conversion_register)

lemma qregister_conversion_id[simp]: \<open>qregister_conversion F qregister_id = F\<close>
  apply transfer by auto


lemma qregister_conversion_non_reg_right[simp]: \<open>qregister_conversion F non_qregister = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)

lemma qregister_conversion_non_reg_left[simp]: \<open>qregister_conversion non_qregister F = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)

lemma qregister_conversion_rename:
  fixes F :: \<open>('a,'c) qregister\<close> and G :: \<open>('b,'c) qregister\<close> and H :: \<open>('d, 'c) qregister\<close> and F' G'
  assumes \<open>qregister H\<close>
  assumes \<open>F = qregister_chain H F'\<close> \<open>G = qregister_chain H G'\<close>
  shows \<open>qregister_conversion F G = qregister_conversion F' G'\<close>
proof (cases \<open>qregister F'\<close>, cases \<open>qregister G'\<close>)
  assume \<open>\<not> qregister G'\<close>
  then have [simp]: \<open>G' = non_qregister\<close>
    using non_qregister by blast
  then show ?thesis
    apply (simp add: \<open>G = qregister_chain H G'\<close>)
    by -
next
  assume \<open>\<not> qregister F'\<close>
  then have [simp]: \<open>F' = non_qregister\<close>
    using non_qregister by blast
  then show ?thesis
    by (simp add: \<open>F = qregister_chain H F'\<close>)
next
  have range_le_preserve: \<open>range F' \<subseteq> range G'\<close> if \<open>range (\<lambda>x. H (F' x)) \<subseteq> range (\<lambda>x. H (G' x))\<close> and \<open>qregister_raw H\<close>
    for H :: \<open>'d qupdate \<Rightarrow> 'c qupdate\<close> and F' :: \<open>'a qupdate \<Rightarrow> 'd qupdate\<close> and G' :: \<open>'b qupdate \<Rightarrow> 'd qupdate\<close>
    using qregister_raw_inj[OF \<open>qregister_raw H\<close>] using that(1)
    by (smt (verit, best) image_subset_iff inj_def rangeE rangeI)
  have H_cancel: \<open>inv (H \<circ> G') \<circ> (H \<circ> F') = inv G' \<circ> F'\<close> if \<open>qregister_raw H\<close> and \<open>qregister_raw G'\<close>
    and \<open>range F' \<subseteq> range G'\<close>
    for H :: \<open>'d qupdate \<Rightarrow> 'c qupdate\<close> and F' :: \<open>'a qupdate \<Rightarrow> 'd qupdate\<close> and G' :: \<open>'b qupdate \<Rightarrow> 'd qupdate\<close>
    apply (rule inv_comp_eqI)
    using qregister_raw_inj[OF \<open>qregister_raw H\<close>] qregister_raw_inj[OF \<open>qregister_raw G'\<close>]
    using inj_compose that by (auto simp add: ext f_inv_into_f subset_iff)
  assume [simp]: \<open>qregister F'\<close> \<open>qregister G'\<close>
  then show ?thesis
    using assms apply transfer
    using range_le_preserve H_cancel by (auto simp: qregister_raw_chain)
qed


lemma qregister_conversion_as_register:
  fixes F :: \<open>('a,'c) qregister\<close> and F' G'
  assumes \<open>qregister G\<close>
  assumes \<open>F = qregister_chain G F'\<close>
  shows \<open>qregister_conversion F G = F'\<close>
  apply (subst qregister_conversion_rename[where H=G and G'=qregister_id and F'=F'])
  using assms by auto

end
