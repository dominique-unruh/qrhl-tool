theory Denotation
  imports CQ_Operators QRHL_Core
begin

type_synonym program_state = \<open>((cl\<times>qu) ell2, (cl\<times>qu) ell2) trace_class\<close>

typedef denotation = \<open>{\<EE> :: program_state \<Rightarrow> program_state. is_cq_map qFst \<EE>}\<close>
  morphisms apply_denotation Abs_denotation
  by (auto intro!: exI[of _ 0])

setup_lifting type_definition_denotation

lift_definition denotation_norm :: \<open>denotation \<Rightarrow> real\<close> is km_norm.
(* lift_definition denotation_bounded :: \<open>denotation \<Rightarrow> bool\<close> is \<open>\<lambda>D. km_norm D \<le> 1\<close>. *)

lemma denotation_norm_pos[iff]: \<open>denotation_norm D \<ge> 0\<close>
  apply transfer' by simp

lift_definition denotation_local_c :: \<open>cl CREGISTER \<Rightarrow> cl \<Rightarrow> denotation \<Rightarrow> denotation\<close> is
  cq_map_local_c
  apply (auto intro!: is_cq_map_cq_map_local_c)
  by (meson is_cq_map_def) 

lemma denotation_local_c_bounded[iff]: 
  shows \<open>denotation_norm (denotation_local_c C x D) \<le> denotation_norm D\<close>
  apply transfer
  by (smt (z3) is_cq_map_def kf_norm_cq_map_local_c)

lift_definition denotation_local_q :: 
  \<open>qu QREGISTER \<Rightarrow> (qu ell2, qu ell2) trace_class \<Rightarrow> denotation \<Rightarrow> denotation\<close>
  is \<open>\<lambda>Q \<rho> \<EE>. if ACTUAL_QREGISTER Q \<and> \<rho> \<ge> 0 then cq_map_local_q Q \<rho> \<EE> else 0\<close>
proof (rename_tac Q \<rho> \<EE>)
  fix Q :: \<open>'qu QREGISTER\<close> and \<rho> :: \<open>('qu ell2, 'qu ell2) trace_class\<close> and \<EE> :: \<open>((('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) trace_class \<Rightarrow> (('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) trace_class)\<close>
  assume [iff]: \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q \<EE>\<close>
  then have [iff]: \<open>kraus_map \<EE>\<close>
    using is_cq_map_def by blast
  show \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q (if ACTUAL_QREGISTER Q \<and> \<rho> \<ge> 0 then cq_map_local_q Q \<rho> \<EE> else 0)\<close>
  proof -
    wlog [iff]: \<open>ACTUAL_QREGISTER Q \<and> \<rho> \<ge> 0\<close>
      using negation by simp
    have [iff]: \<open>Qqcompatible (QREGISTER_chain \<lbrakk>#2.\<rbrakk>\<^sub>q Q) \<lbrakk>#1\<rbrakk>\<^sub>q\<close>
      by auto
    have [iff]: \<open>ACTUAL_QREGISTER (QREGISTER_chain \<lbrakk>#2.\<rbrakk>\<^sub>q Q)\<close>
      by (simp add: ACTUAL_QREGISTER_chain)
    have 1: \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q (cq_map_local_q Q \<rho> \<EE>)\<close>
      by (auto intro!: is_cq_map_km_local_register_quantum tc_tensor_pos simp: cq_map_local_q_def)
     then show ?thesis
      by auto
  qed
qed

lemma denotation_local_q_bounded[iff]:
  shows \<open>denotation_norm (denotation_local_q Q \<rho> D) \<le> norm \<rho> * denotation_norm D\<close>
proof (transfer fixing: Q \<rho>)
  fix Q :: \<open>qu QREGISTER\<close> and D :: \<open>((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close>
  assume \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q D\<close>
  then have km: \<open>kraus_map D\<close>
    using is_cq_map_def by blast
  have \<open>km_norm (cq_map_local_q Q \<rho> D) \<le> norm \<rho> * km_norm D\<close> if \<open>ACTUAL_QREGISTER Q \<and> 0 \<le> \<rho>\<close>
    unfolding cq_map_local_q_def
    apply (rule km_norm_local_register[THEN order.trans])
    using that km
    by (auto intro!: tc_tensor_pos mult_le_one simp: cq_map_local_q_def norm_tc_tensor norm_tc_butterfly)
  then show \<open>km_norm (if ACTUAL_QREGISTER Q \<and> 0 \<le> \<rho> then cq_map_local_q Q \<rho> D else 0) \<le> norm \<rho> * km_norm D\<close>
    by auto
qed

lift_definition denotation_measurement :: \<open>(cl \<Rightarrow> (cl, qu) measurement) \<Rightarrow> denotation\<close> is
  \<open>\<lambda>M::cl \<Rightarrow> (cl, qu) measurement. cq_map_from_kraus_family qFst qSnd (\<lambda>c. kf_from_measurement (M c))\<close>
  by (auto intro!: cq_map_from_kraus_family_is_cq_map)


lemma denotation_measurement_bounded[iff]: \<open>denotation_norm (denotation_measurement M) \<le> 1\<close>
  apply (transfer fixing: M)
  by (auto intro!: cq_map_from_kraus_family_norm kf_from_measurement_norm_leq1)

instantiation denotation :: \<open>{zero,one,times,plus}\<close> begin
lift_definition zero_denotation :: denotation is 0
  by simp
lift_definition one_denotation :: denotation is \<open>cq_id qFst\<close>
  by simp
lift_definition times_denotation :: \<open>denotation \<Rightarrow> denotation \<Rightarrow> denotation\<close> is
  \<open>\<lambda>D E. D o E\<close>
  by (smt (verit, best) cq_map_id_left fun.map_comp is_cq_map_def kraus_map_comp)
lift_definition plus_denotation :: \<open>denotation \<Rightarrow> denotation \<Rightarrow> denotation\<close> is
  \<open>\<lambda>D E \<rho>. D \<rho> + E \<rho>\<close>
  by (auto intro!: is_cq_map_plus)
instance..
end

lemma zero_denotation_bounded[iff]: \<open>denotation_norm 0 = 0\<close>
  apply transfer
  by simp

lemma one_denotation_bounded[iff]: \<open>denotation_norm 1 = 1\<close>
  apply transfer
  by simp

lemma times_denotation_bounded: \<open>denotation_norm (D * E) \<le> denotation_norm D * denotation_norm E\<close>
  apply transfer
  by (metis Groups.mult_ac(2) is_cq_map_def km_comp_norm_leq)

instantiation denotation :: monoid_mult begin
instance
proof intro_classes
  fix a b c :: denotation
  show \<open>a * b * c = a * (b * c)\<close>
    apply transfer'
    by fastforce
  show \<open>1 * a = a\<close>
    apply transfer
    using cq_map_id_left by blast
  show \<open>a * 1 = a\<close>
    apply transfer
    using cq_map_id_right by blast
qed
end

instantiation denotation :: topological_space begin
lift_definition open_denotation :: \<open>denotation set \<Rightarrow> bool\<close> is \<open>openin (top_of_set (range apply_denotation))\<close>.
instance
proof intro_classes
  show \<open>open (UNIV :: denotation set)\<close>
    by (simp add: open_denotation_def)
  show \<open>open (S \<inter> T)\<close> if \<open>open S\<close> and \<open>open T\<close> for S T :: \<open>denotation set\<close>
    using that
    apply transfer
    by blast
  show \<open>open (\<Union> K)\<close> if \<open>\<forall>S\<in>K. open S\<close> for K :: \<open>denotation set set\<close>
    using that
    apply transfer
    by blast
qed
end

instantiation denotation :: t2_space begin
instance
proof -
  define S :: \<open>(((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class) set\<close>
    where \<open>S = range (apply_denotation)\<close>
  have hausdorff_S: \<open>Hausdorff_space (top_of_set S)\<close>
  proof -
    define cb :: \<open>_ \<Rightarrow> (((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class)\<close> where \<open>cb = cblinfun_apply\<close>
    note [transfer_rule] = rel_topology_bounded_linear_sot
    have [transfer_rule]: \<open>bi_unique cr_cblinfun\<close>
      by (metis bi_total_eq bi_unique_eq cblinfun.bi_unique cblinfun.pcr_cr_eq)
    
    have hausdorff_range_cb: \<open>Hausdorff_space (top_of_set (Collect (bounded_clinear :: (((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class) \<Rightarrow> _)))\<close>
      using hausdorff_sot[where 'a=\<open>((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close> and 'b=\<open>((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close>]
      by (transfer, blast)

    have \<open>S \<subseteq> Collect bounded_clinear\<close>
      using apply_denotation
      by (auto intro!: kraus_map_bounded_clinear simp add: S_def is_cq_map_def cb_def)
    then have top_S: \<open>top_of_set S = subtopology (top_of_set (Collect bounded_clinear)) S\<close>
      by (metis (no_types, lifting) subtopology_subtopology topspace_euclidean_subtopology
          topspace_subtopology_subset)
    show \<open>Hausdorff_space (top_of_set S)\<close>
      using Hausdorff_space_subtopology top_S hausdorff_range_cb by metis
  qed
  show \<open>OFCLASS(denotation, t2_space_class)\<close>
  proof (intro_classes, transfer, fold S_def)
    fix x y :: \<open>((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close>
    assume \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q x\<close>
    then have \<open>x \<in> S\<close>
      by (metis (no_types, lifting) Abs_denotation_inverse S_def mem_Collect_eq rangeI)
    assume \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q y\<close>
    then have \<open>y \<in> S\<close>
      by (metis (no_types, lifting) Abs_denotation_inverse S_def UNIV_I image_iff mem_Collect_eq)
    assume \<open>x \<noteq> y\<close>
    with hausdorff_S \<open>x \<in> S\<close> \<open>y \<in> S\<close>
    obtain U V where sepUV: \<open>openin (top_of_set S) U \<and> openin (top_of_set S) V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
      apply atomize_elim
      by (simp add: Hausdorff_space_def disjnt_def)
    then have \<open>U\<in>{A. \<forall>\<EE>\<in>A. is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q \<EE>}\<close> and \<open>V\<in>{A. \<forall>\<EE>\<in>A. is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q \<EE>}\<close>
      using apply_denotation by (auto simp: S_def dest!: openin_imp_subset)
    with sepUV
    show \<open>\<exists>U\<in>{A. \<forall>\<EE>\<in>A. is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q \<EE>}. \<exists>V\<in>{A. \<forall>\<EE>\<in>A. is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q \<EE>}.
         openin (top_of_set S) U \<and> openin (top_of_set S) V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
      by blast
  qed
qed
end


instantiation denotation :: comm_monoid_add begin
instance
proof intro_classes
  fix a b c :: denotation
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer' by auto
  show \<open>a + b = b + a\<close>
    apply transfer' by auto
  show \<open>0 + a = a\<close>
    apply transfer' by auto
qed
end

instance denotation :: semiring_1
proof intro_classes
  fix D E F :: denotation
  show \<open>0 * D = 0\<close>
    apply transfer' by auto
  show \<open>D * 0 = 0\<close>
    apply transfer
    by (auto intro!: ext simp: complex_vector.linear_0 is_cq_map_def complex_vector.linear_0 bounded_clinear.clinear kraus_map_bounded_clinear)
  show \<open>(D + E) * F = D * F + E * F\<close>    
    apply transfer
    by (auto intro!: ext simp: complex_vector.linear_add is_cq_map_def complex_vector.linear_0 bounded_clinear.clinear kraus_map_bounded_clinear)
  show \<open>D * (E + F) = D * E + D * F\<close>
    apply transfer
    by (auto intro!: ext simp: complex_vector.linear_add is_cq_map_def complex_vector.linear_0 bounded_clinear.clinear kraus_map_bounded_clinear)
  show \<open>0 \<noteq> (1 :: denotation)\<close>
    apply transfer
    using one_denotation.abs_eq one_denotation_bounded zero_denotation_def by force
qed

instantiation denotation :: order begin
lift_definition less_eq_denotation :: \<open>denotation \<Rightarrow> denotation \<Rightarrow> bool\<close> is
  \<open>\<lambda>D E. \<forall>\<rho>\<ge>0. D \<rho> \<ge> E \<rho>\<close>.
definition \<open>x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x\<close> for x y :: denotation
instance
proof intro_classes
  fix x y z :: denotation
  show \<open>x \<le> x\<close>
    apply transfer' by simp
  show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
    apply transfer' by fastforce
  show \<open>x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
  proof transfer
    fix D E :: \<open>((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close>
    assume \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q D\<close> and \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q E\<close>
    then have \<open>kraus_map D\<close> and \<open>kraus_map E\<close>
      using is_cq_map_def by auto
    then have [intro!]: \<open>clinear D\<close> \<open>clinear E\<close>
      by (simp_all add: bounded_clinear.axioms(1) kraus_map_bounded_clinear)
    assume \<open>\<forall>\<rho>\<ge>0. E \<rho> \<le> D \<rho>\<close> and \<open>\<forall>\<rho>\<ge>0. D \<rho> \<le> E \<rho>\<close>
    then have \<open>\<forall>\<rho>\<ge>0. D \<rho> = E \<rho>\<close>
      by fastforce
    then show \<open>D = E\<close>
      apply (rule_tac eq_from_separatingI[OF separating_density_ops[of 1]])
      by auto
  qed
  show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
    by (simp add: less_denotation_def)
qed
end

instantiation denotation :: minus begin
lift_definition minus_denotation :: \<open>denotation \<Rightarrow> denotation \<Rightarrow> denotation\<close> is
  \<open>\<lambda>D E. if kraus_map (\<lambda>\<rho>. D \<rho> - E \<rho>) then (\<lambda>\<rho>. D \<rho> - E \<rho>) else 0\<close>
proof (rename_tac D E)
  fix D E :: \<open>((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close>
  assume cqmap: \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q D\<close>   \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q E\<close>
  show \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q (if kraus_map (\<lambda>\<rho>. D \<rho> - E \<rho>) then \<lambda>\<rho>. D \<rho> - E \<rho> else 0)\<close>
  proof (cases \<open>kraus_map (\<lambda>\<rho>. D \<rho> - E \<rho>)\<close>)
    case True
    have cqD: \<open>cq_id \<lbrakk>#1\<rbrakk>\<^sub>q (D (cq_id \<lbrakk>#1\<rbrakk>\<^sub>q \<rho>)) = D \<rho>\<close> for \<rho>
      by (metis comp_apply cqmap is_cq_map_def)
    have cqE: \<open>cq_id \<lbrakk>#1\<rbrakk>\<^sub>q (E (cq_id \<lbrakk>#1\<rbrakk>\<^sub>q \<rho>)) = E \<rho>\<close> for \<rho>
      by (metis comp_apply cqmap is_cq_map_def)
    have \<open>cq_id \<lbrakk>#1\<rbrakk>\<^sub>q \<circ> (\<lambda>\<rho>. D \<rho> - E \<rho>) \<circ> cq_id \<lbrakk>#1\<rbrakk>\<^sub>q = (\<lambda>\<rho>. D \<rho> - E \<rho>)\<close>
      by (auto intro!: ext simp: complex_vector.linear_diff bounded_clinear_cq_id bounded_clinear.clinear cqD cqE)
    then show ?thesis
      apply (simp add: True)
      by (intro is_cq_map_def[THEN iffD2] conjI True)
  next
    case False
    then show ?thesis
      by auto
  qed
qed
instance..
end

instance denotation :: semiring_1_cancel
proof intro_classes
  fix D E F :: denotation
  show \<open>D + E - D = E\<close>
  proof transfer
    fix D E :: \<open>((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close>
    assume \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q E\<close>
    then have [simp]: \<open>kraus_map E\<close>
      using is_cq_map_def by blast
    have [simp]: \<open>(\<lambda>\<rho>. D \<rho> + E \<rho> - D \<rho>) = E\<close>
      by fastforce
    show \<open>(if kraus_map (\<lambda>\<rho>. D \<rho> + E \<rho> - D \<rho>) then \<lambda>\<rho>. D \<rho> + E \<rho> - D \<rho> else 0) = E\<close>
      by simp
  qed
  show \<open>D - E - F = D - (E + F)\<close>
  proof transfer
    fix D E F :: \<open>((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close>
    assume \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q F\<close>
    then have [iff]: \<open>kraus_map F\<close>
      using is_cq_map_def by blast
    consider (km_DEF) \<open>kraus_map (\<lambda>\<rho>. D \<rho> - E \<rho> - F \<rho>)\<close> | (km_DE) \<open>\<not> kraus_map (\<lambda>\<rho>. D \<rho> - E \<rho> - F \<rho>)\<close> \<open>kraus_map (\<lambda>\<rho>. D \<rho> - E \<rho>)\<close>
      | (km_D) \<open>\<not> kraus_map (\<lambda>\<rho>. D \<rho> - E \<rho> - F \<rho>)\<close> \<open>\<not> kraus_map (\<lambda>\<rho>. D \<rho> - E \<rho>)\<close>
      by metis
    then show \<open>(if kraus_map (\<lambda>\<rho>. (if kraus_map (\<lambda>\<rho>. D \<rho> - E \<rho>) then \<lambda>\<rho>. D \<rho> - E \<rho> else 0) \<rho> - F \<rho>)
        then \<lambda>\<rho>. (if kraus_map (\<lambda>\<rho>. D \<rho> - E \<rho>) then \<lambda>\<rho>. D \<rho> - E \<rho> else 0) \<rho> - F \<rho> else 0) =
       (if kraus_map (\<lambda>\<rho>. D \<rho> - (E \<rho> + F \<rho>)) then \<lambda>\<rho>. D \<rho> - (E \<rho> + F \<rho>) else 0)\<close>
    proof cases
      case km_DEF
      then have km_DE: \<open>kraus_map (\<lambda>\<rho>. D \<rho> - E \<rho>)\<close>
        apply (rewrite at \<open>kraus_map (\<lambda>\<rho>. \<hole>)\<close> to \<open>(D \<rho> - E \<rho> - F \<rho>) + F \<rho>\<close> DEADID.rel_mono_strong)
        apply simp
        apply (rule kraus_map_add)
        by (auto intro!: simp: )
      show ?thesis
        by (simp add: km_DEF km_DE diff_diff_eq)
    next
      case km_DE
      show ?thesis
        by (simp add: km_DE diff_diff_eq)
    next
      case km_D
      have \<open>F = 0\<close> if \<open>kraus_map (\<lambda>\<rho>. - F \<rho>)\<close>
      proof (rule eq_from_separatingI[OF separating_density_ops])
        show \<open>0 < (1::real)\<close>
          by simp
        show \<open>clinear F\<close>
          by (simp add: bounded_clinear.axioms(1) kraus_map_bounded_clinear)
        show \<open>clinear 0\<close>
          by (simp add: complex_vector.linear_zero func_zero)
        fix \<rho> :: \<open>((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close> assume \<open>\<rho> \<in> {t. 0 \<le> t \<and> norm t \<le> 1}\<close>
        then have \<open>\<rho> \<ge> 0\<close>
          by simp
        from \<open>kraus_map F\<close> have \<open>F \<rho> \<ge> 0\<close>
          using \<open>0 \<le> \<rho>\<close> kraus_map_pos by blast
        moreover from that have \<open>- F \<rho> \<ge> 0\<close>
          using \<open>0 \<le> \<rho>\<close> kraus_map_pos by blast
        ultimately show \<open>F \<rho> = 0 \<rho>\<close>
          by fastforce
      qed
      then show ?thesis
        by (auto simp: km_D simp flip: diff_diff_eq)
    qed
  qed
qed


lift_definition denotation_sample :: \<open>(cl \<Rightarrow> cl distr) \<Rightarrow> denotation\<close> is
  \<open>\<lambda>e. cq_map_from_kraus_family qFst qSnd (\<lambda>c. kf_sample (prob (e c)))\<close>
  by (rule cq_map_from_kraus_family_is_cq_map)

lemma denotation_sample_bounded[iff]: \<open>denotation_norm (denotation_sample d) \<le> 1\<close>
  apply (transfer fixing: d)
  by (auto intro!: cq_map_from_kraus_family_norm simp: kf_sample_norm prob_summable)


lift_definition denotation_cases :: \<open>(cl \<Rightarrow> denotation) \<Rightarrow> denotation\<close> is
  \<open>\<lambda>\<EE>. kf_apply (kf_comp_dependent (\<lambda>(c,_). km_some_kraus_family (\<EE> c)) (kf_tensor kf_complete_measurement_ket kf_id))\<close>
proof (rename_tac \<EE>)
  fix \<EE> :: \<open>cl \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close>
  assume asm: \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q (\<EE> c)\<close> for c
  define \<FF> where \<open>\<FF> c = km_some_kraus_family (\<EE> c)\<close> for c
  have apply\<FF>: \<open>kf_apply (\<FF> c) = \<EE> c\<close> for c
    using asm \<FF>_def[abs_def] is_cq_map_def kf_apply_km_some_kraus_family by blast
  show \<open>is_cq_map qFst
          (kf_apply (kf_comp_dependent (\<lambda>(c, _). \<FF> c) (kf_tensor kf_complete_measurement_ket kf_id)))\<close>
  proof (cases \<open>bdd_above (range (\<lambda>x. kf_norm (\<FF> x)))\<close>)
    case True
    then have bdd2: \<open>bdd_above ((\<lambda>x. kf_norm (\<FF> (f x))) ` X)\<close> for X f
      by (smt (verit, ccfv_threshold) bdd_above_mono2 range_composition top.extremum)
    define kf_cq_id :: \<open>((cl \<times> qu) ell2, (cl \<times> qu) ell2, cl\<times>unit) kraus_family\<close> where \<open>kf_cq_id = kf_tensor kf_complete_measurement_ket kf_id\<close>
    have kf_cq_id_norm: \<open>kf_norm (kf_cq_id) = 1\<close>
      by (simp add: kf_cq_id_def kf_norm_tensor)
    have \<EE>_left_id: \<open>cq_id \<lbrakk>#1\<rbrakk>\<^sub>q (\<EE> c \<rho>) = \<EE> c \<rho>\<close> for c \<rho>
      by (metis asm comp_apply cq_map_id_left)
    have \<FF>_left_id: \<open>kf_comp kf_cq_id (\<FF> c) =\<^sub>k\<^sub>r \<FF> c\<close> for c
      apply (rule kf_eq_weakI)
      using asm \<EE>_left_id
      by (simp add: kf_comp_apply kf_cq_id_def apply\<FF>
          kf_id_apply kf_id_apply[abs_def] is_cq_map_def 
          flip: km_tensor_kf_tensor id_def cq_id_qFst km_complete_measurement_ket_kf_complete_measurement_ket)
    have bdd3: \<open>bdd_above ((\<lambda>(c,_). kf_norm (kf_comp kf_cq_id (\<FF> c))) ` X)\<close> for X :: \<open>(cl\<times>'a) set\<close>
      unfolding case_prod_unfold
      using bdd2 apply (rule bdd_above_mono2[OF _ subset_refl])
      apply (rule kf_comp_norm_leq[THEN order.trans])
      using kf_cq_id_norm by auto
    have \<open>cq_id qFst o kf_apply (kf_comp_dependent (\<lambda>(c, _). \<FF> c) kf_cq_id) o cq_id qFst
      = kf_apply (kf_comp (kf_comp kf_cq_id (kf_comp_dependent (\<lambda>(c, _). \<FF> c) kf_cq_id)) kf_cq_id)\<close>
      by (simp add: cq_id_qFst kf_comp_apply o_def kf_cq_id_def kf_id_apply[abs_def] id_def
          flip: km_tensor_kf_tensor km_complete_measurement_ket_kf_complete_measurement_ket)
    also have \<open>\<dots> = kf_apply (kf_comp (kf_comp_dependent (\<lambda>(c, _). (kf_comp kf_cq_id (\<FF> c))) kf_cq_id) kf_cq_id)\<close>
      apply (intro ext kf_apply_eqI kf_comp_cong_weak)
      unfolding kf_comp_def case_prod_unfold
       apply (rule kf_comp_dependent_assoc_weak[unfolded case_prod_unfold, symmetric, THEN kf_eq_weak_trans])
      using bdd2 by auto
    also have \<open>\<dots> = kf_apply (kf_comp (kf_comp_dependent (\<lambda>(c, _). (\<FF> c)) kf_cq_id) kf_cq_id)\<close>
      apply (intro ext kf_apply_eqI kf_comp_cong_weak kf_comp_dependent_cong_weak)
      using bdd3 by (auto intro!: \<FF>_left_id simp: case_prod_unfold)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (\<lambda>(_, (c,_)). (\<FF> c)) (kf_comp kf_cq_id kf_cq_id))\<close>
      apply (intro ext kf_apply_eqI)
      unfolding kf_comp_def case_prod_unfold
      apply (rule kf_comp_dependent_assoc_weak[unfolded case_prod_unfold, THEN kf_eq_weak_trans])
      using bdd2 by auto
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (\<lambda>(_, (c,_)). \<FF> c) (kf_map (\<lambda>(c,_). ((c,()),(c,()))) kf_cq_id))\<close>
    proof -
      have \<open>kf_comp kf_cq_id kf_cq_id \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>((e, g), f, h). ((e, ()), g, ()))
         (kf_tensor (kf_comp kf_complete_measurement_ket kf_complete_measurement_ket) (kf_comp kf_id kf_id))\<close>
        apply (auto intro!: kf_comp_cong simp: kf_cq_id_def)
        apply (rule kf_tensor_compose_distrib'[THEN kf_eq_trans])
        by simp
      also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>((e, g), f, h). ((e, ()), g, ()))
         (kf_tensor (kf_map (\<lambda>b. (b, b)) kf_complete_measurement_ket) (kf_map (\<lambda>x. ((),x)) kf_id))\<close>
        by (intro kf_map_cong[OF refl] kf_tensor_cong kf_complete_measurement_ket_idem kf_comp_id_left kf_comp_id_right)
      also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>((e, g), f, h). ((e, ()), g, ())) (kf_map (\<lambda>(b,x). ((b,b),((),x)))
                           (kf_tensor kf_complete_measurement_ket kf_id))\<close>
        apply (rule kf_map_cong[OF refl])
        apply (rule kf_tensor_map_both[THEN kf_eq_trans])
        by (simp add: map_prod_def)
      also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map ((\<lambda>((e, g), f, h). ((e, ()), g, ())) o (\<lambda>(b,x). ((b,b),((),x)))) kf_cq_id\<close>
        using kf_cq_id_def kf_map_twice by blast
      also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>p. ((fst p, ()), fst p, ())) kf_cq_id\<close>
        apply (rule kf_map_cong) by auto
      finally show ?thesis
        by (auto intro!: ext kf_apply_eqI kf_comp_dependent_cong_weak bdd2 simp: case_prod_unfold)
    qed
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (\<lambda>(c,_). \<FF> c) kf_cq_id)\<close>
      apply (intro ext kf_apply_eqI kf_comp_dependent_map_right_weak[THEN kf_eq_weak_trans])
      by (simp add: case_prod_unfold)
    finally show ?thesis
      by (simp add: is_cq_map_def flip: kf_cq_id_def)
  next
    case False
    have *: \<open>UNIV = fst ` (UNIV \<times> {()})\<close>
      by auto
     have \<open>kf_comp_dependent (\<lambda>(c, _). \<FF> c) (kf_tensor kf_complete_measurement_ket kf_id) = 0\<close>
       apply (rule kf_comp_dependent_invalid)
       using False
       apply (subst (asm) *, subst (asm) image_image)
       by (simp add: kf_domain_tensor case_prod_unfold)
    then show ?thesis
      by simp
  qed
qed

lemma denotation_cases_bounded:
  assumes \<open>\<And>c. denotation_norm (D c) \<le> B\<close>
  shows \<open>denotation_norm (denotation_cases D) \<le> B\<close>
proof (insert assms, transfer fixing: B)
  fix D :: \<open>cl \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close>
  assume \<open>pred_fun \<top> (is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q) D\<close>
  then have cq: \<open>is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q (D c)\<close> for c
    by fastforce
  assume bdd: \<open>km_norm (D c) \<le> B\<close> for c
  define \<FF> where \<open>\<FF> c = km_some_kraus_family (D c)\<close> for c
  have apply\<FF>: \<open>kf_apply (\<FF> c) = D c\<close> for c
    using cq \<FF>_def[abs_def] is_cq_map_def kf_apply_km_some_kraus_family by blast
  have \<open>B \<ge> 0\<close>
    using bdd[of undefined] km_norm_geq0[of \<open>D undefined\<close>]
    by linarith
  show \<open>km_norm ((*\<^sub>k\<^sub>r) (kf_comp_dependent (\<lambda>(c, _). km_some_kraus_family (D c)) (kf_tensor kf_complete_measurement_ket kf_id))) \<le> B\<close>
    using bdd \<open>B \<ge> 0\<close>
    apply (simp add: flip: \<FF>_def)
    apply (simp add: km_norm_kf_norm flip: apply\<FF>)
    by (metis (mono_tags, lifting) kf_comp_dependent_norm_leq kf_norm_complete_measurement_ket kf_norm_id_eq1 kf_norm_tensor mult_cancel_left2 split_def)
qed

definition denotation_while_n :: \<open>(cl \<Rightarrow> bool) \<Rightarrow> denotation \<Rightarrow> nat \<Rightarrow> denotation\<close> where
  \<open>denotation_while_n e D n = denotation_cases (\<lambda>m. if e m then 0 else 1) * (denotation_cases (\<lambda>m. if e m then D else 0))^n\<close>

lemma denotation_cases_0[simp]: \<open>denotation_cases 0 = 0\<close>
  apply (simp add: func_zero)
  apply transfer'
  by (simp add: case_prod_unfold)

lemma denotation_cases_plus: 
  assumes \<open>bdd_above (range (denotation_norm o D))\<close>
  assumes \<open>bdd_above (range (denotation_norm o E))\<close>
  shows \<open>denotation_cases (\<lambda>c. D c + E c) = denotation_cases D + denotation_cases E\<close>
proof (insert assms, transfer)
  fix D E :: \<open>cl \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close>
  assume \<open>pred_fun \<top> (is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q) D\<close>
  then have [iff]: \<open>kraus_map (D c)\<close> for c
    using is_cq_map_def by auto
  assume \<open>pred_fun \<top> (is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q) E\<close>
  then have [iff]: \<open>kraus_map (E c)\<close> for c
    by (simp add: is_cq_map_def)
  assume bdd0: \<open>bdd_above (range (km_norm \<circ> D))\<close> \<open>bdd_above (range (km_norm \<circ> E))\<close>
  have bdd: \<open>bdd_above ((\<lambda>c. km_norm (\<lambda>\<rho>. D (fst c) \<rho> + E (fst c) \<rho>)) ` X)\<close> for X
  proof -
    from bdd0 obtain B where B: \<open>km_norm (D c) \<le> B\<close> for c
      by (auto intro!: simp: bdd_above_def)
    from bdd0 obtain C where C: \<open>km_norm (E c) \<le> C\<close> for c
      by (auto intro!: simp: bdd_above_def)
    have \<open>km_norm (\<lambda>\<rho>. D c \<rho> + E c \<rho>) \<le> B + C\<close> for c
      using km_norm_triangle[OF \<open>kraus_map (D c)\<close> \<open>kraus_map (E c)\<close>] B[of c] C[of c]
      by (simp add: plus_fun_def)
    then show ?thesis
      by (rule bdd_aboveI2)
  qed
  have bdd1: \<open>bdd_above ((\<lambda>x. km_norm (D (f x))) ` X)\<close> for f X
    using bdd0(1) apply (rule bdd_above_mono) by auto
  have bdd2: \<open>bdd_above ((\<lambda>x. km_norm (E (f x))) ` X)\<close> for f X
    using bdd0(2) apply (rule bdd_above_mono) by auto
  have 1: \<open>km_some_kraus_family (\<lambda>\<rho>. D c \<rho> + E c \<rho>) =\<^sub>k\<^sub>r kf_plus (km_some_kraus_family (D c)) (km_some_kraus_family (E c))\<close> for c
    apply (rule kf_eq_weakI)
    by (simp add: kf_apply_km_some_kraus_family kraus_map_add kf_plus_apply)

  have inj: \<open>inj_on (\<lambda>p. case snd p of Inl d \<Rightarrow> Inl (fst p, ()) | Inr e \<Rightarrow> Inr (fst p, ())) X\<close> for X :: \<open>((cl \<times> unit) \<times> (unit + unit)) set\<close>
    by (auto intro!: inj_onI simp: split!: sum.split_asm)

  show \<open>kf_apply (kf_comp_dependent (\<lambda>(c,_). km_some_kraus_family (\<lambda>\<rho>. D c \<rho> + E c \<rho>)) (kf_tensor kf_complete_measurement_ket kf_id)) =
           (\<lambda>\<rho>. kf_comp_dependent (\<lambda>(c,_). km_some_kraus_family (D c)) (kf_tensor kf_complete_measurement_ket kf_id) *\<^sub>k\<^sub>r \<rho> +
                kf_comp_dependent (\<lambda>(c,_). km_some_kraus_family (E c)) (kf_tensor kf_complete_measurement_ket kf_id) *\<^sub>k\<^sub>r \<rho>)\<close>
    by (auto simp: case_prod_unfold bdd bdd1 bdd2 kf_comp_dependent_kf_plus_left' kf_apply_map_inj inj
        simp flip: kf_comp_dependent_kf_plus_left kf_plus_apply
        intro!: 1 kf_comp_dependent_cong_weak ext kf_apply_eqI)
qed

lemma denotation_merge: 
  assumes \<open>bdd_above (range (denotation_norm o D))\<close>
  assumes \<open>bdd_above (range (denotation_norm o E))\<close>
  shows \<open>denotation_cases D * denotation_cases E = denotation_cases (\<lambda>c. D c * E c)\<close>
proof (insert assms, transfer)
  write kf_comp (infixl "\<bullet>" 70)
  write kf_comp_dependent (infixl "\<bullet>\<bullet>" 70)
  write kf_map (infixr "``" 75)
  fix D E :: \<open>cl \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close>
  assume \<open>pred_fun \<top> (is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q) D\<close> and \<open>pred_fun \<top> (is_cq_map \<lbrakk>#1\<rbrakk>\<^sub>q) E\<close>
  then have [iff]: \<open>kraus_map (D c)\<close>   \<open>kraus_map (E c)\<close> for c
    by (simp_all add: is_cq_map_def)
  define \<DD> \<EE> where \<open>\<DD> c = km_some_kraus_family (D c)\<close> and \<open>\<EE> c = km_some_kraus_family (E c)\<close> for c
  define meas :: \<open>((cl \<times> qu) ell2, (cl \<times> qu) ell2, cl \<times> unit) kraus_family\<close>
    where \<open>meas = kf_tensor kf_complete_measurement_ket kf_id\<close>
  have apply\<DD>: \<open>kf_apply (\<DD> c) = D c\<close> and apply\<EE>: \<open>kf_apply (\<EE> c) = E c\<close> for c
    using \<DD>_def \<EE>_def by force+
  assume bdd\<DD>': \<open>bdd_above (range (km_norm \<circ> D))\<close>
  then have bdd\<DD>: \<open>bdd_above ((\<lambda>x. kf_norm (\<DD> (f x))) ` X)\<close> for f X
    apply (rule bdd_above_mono)
    by (auto simp: km_norm_kf_norm simp flip: apply\<DD>)
  assume bdd\<EE>': \<open>bdd_above (range (km_norm \<circ> E))\<close>
  then have bdd\<EE>: \<open>bdd_above ((\<lambda>x. kf_norm (\<EE> (g x))) ` X)\<close> for g X
    apply (rule bdd_above_mono)
    by (auto simp: km_norm_kf_norm simp flip: apply\<EE>)
  from bdd\<DD> bdd\<EE>
  have bdd\<DD>\<EE>: \<open>bdd_above ((\<lambda>x. kf_norm (\<DD> (g x)) * kf_norm (\<EE> (f x))) ` X)\<close> for f g X
  proof -
    from bdd\<DD>' obtain B where 1: \<open>kf_norm (\<DD> x) \<le> B\<close> for x
      by (auto simp: bdd_above_def km_norm_kf_norm simp flip: apply\<DD>)
    from bdd\<EE>' obtain C where 2: \<open>kf_norm (\<EE> x) \<le> C\<close> for x
      by (auto simp: bdd_above_def km_norm_kf_norm simp flip: apply\<EE>)
    show ?thesis
      apply (rule bdd_aboveI2[where M=\<open>B*C\<close>])
      using 1 2 apply (rule mult_mono')
      by auto
  qed
  then have bdd\<DD>\<EE>: \<open>bdd_above ((\<lambda>x. kf_norm (\<DD> (g x) \<bullet> \<EE> (f x))) ` X)\<close> for f g X
    apply (rule bdd_above_mono2)
     apply (rule order_refl)
    by (rule kf_comp_norm_leq)

  have \<open>kf_apply ((\<lambda>(c, _). \<DD> c) \<bullet>\<bullet> meas) \<circ> kf_apply ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)
    = kf_apply (((\<lambda>(c, _). \<DD> c) \<bullet>\<bullet> meas) \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas))\<close>
    by (simp add: kf_comp_apply)
  also have \<open>\<dots> = kf_apply ((\<lambda>(_, c, _). \<DD> c) \<bullet>\<bullet> (meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)))\<close>
    unfolding kf_comp_def
    apply (intro ext kf_apply_eqI kf_comp_dependent_assoc_weak)
    by (simp_all add: case_prod_unfold bdd\<DD>)
  also have \<open>\<dots> = kf_apply (\<DD> \<bullet>\<bullet> (\<lambda>(_,c,_). c) `` (meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)))\<close>
    apply (rule sym)
    apply (intro ext kf_apply_eqI kf_comp_dependent_assoc_weak kf_comp_dependent_map_right_weak[THEN kf_eq_weak_trans])
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> = kf_apply (\<DD> \<bullet>\<bullet> (\<lambda>(((c,_),_),_). c) `` (meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)))\<close>
    by x (* TODO needs asm *)
  also have \<open>\<dots> = kf_apply (\<DD> \<bullet>\<bullet> (\<lambda>(((c,_),_),_). c) `` (\<lambda>(x,_). (x,())) `` (meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)))\<close>
    apply (rule sym)
    by (auto intro!: ext kf_apply_eqI kf_comp_dependent_cong_weak kf_map_twice[THEN kf_eq_trans] 
        simp: bdd\<DD> o_def case_prod_unfold)
  also have \<open>\<dots> = kf_apply (\<DD> \<bullet>\<bullet> (\<lambda>(((c,_),_),_). c) `` (kf_flatten meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)))\<close>
    apply (rule sym)
    by (auto intro!: ext kf_apply_eqI kf_comp_dependent_cong_weak kf_map_cong kf_comp_map_left[THEN kf_eq_trans]
        simp: bdd\<DD>)
  also have \<open>\<dots> = kf_apply (\<DD> \<bullet>\<bullet> (\<lambda>(((c,_),_),_). c) `` (\<lambda>x. (x,())) `` ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas))\<close>
  proof -
    have \<open>is_cq_map qFst (kf_apply ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas))\<close>
      thm is_cq_map_kf_comp_dependent
      by -
    then have \<open>kf_flatten meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas) =\<^sub>k\<^sub>r (\<lambda>x. (x,())) `` ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)\<close>
      by -
    then have \<open>kf_flatten meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas) \<equiv>\<^sub>k\<^sub>r (\<lambda>x. (x,())) `` ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)\<close>
      by -
    then show ?thesis
      by (auto intro!: ext kf_apply_eqI kf_comp_dependent_cong_weak kf_map_cong simp: bdd\<DD>)
  qed
  also have \<open>\<dots> = kf_apply (\<DD> \<bullet>\<bullet> (\<lambda>((c,_),_). c) `` ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas))\<close>
    by (auto intro!: ext kf_apply_eqI kf_comp_dependent_cong_weak kf_map_cong kf_map_twice[THEN kf_eq_trans]
        simp: bdd\<DD>)
  also have \<open>\<dots> = kf_apply ((\<lambda>((c,_),_). \<DD> c) \<bullet>\<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas))\<close>
    by (auto intro!: ext kf_apply_eqI kf_comp_dependent_map_right_weak[THEN kf_eq_weak_trans] simp: case_prod_unfold)
  also have \<open>\<dots> = kf_apply ((\<lambda>(c,_). \<DD> c \<bullet> \<EE> c) \<bullet>\<bullet> meas)\<close>
    apply (rule sym)
    by (auto intro!: ext kf_apply_eqI kf_comp_dependent_assoc_weak kf_comp_dependent_map_right_weak[THEN kf_eq_weak_trans] kf_comp_dependent_assoc_weak[THEN kf_eq_weak_trans]
        simp: case_prod_unfold bdd\<DD> bdd\<EE> kf_comp_def)
  also have \<open>\<dots> = kf_apply ((\<lambda>(c, _). km_some_kraus_family (D c \<circ> E c)) \<bullet>\<bullet> meas)\<close>
    apply (intro ext kf_apply_eqI kf_comp_dependent_cong_weak kf_eq_refl)
    by (simp_all add: apply\<DD> apply\<EE> kf_comp_apply kf_eq_weak_def kraus_map_comp case_prod_unfold bdd\<DD>\<EE>)
  finally show \<open>kf_apply (kf_comp_dependent (\<lambda>(c, _). \<DD> c) meas) \<circ>
               kf_apply (kf_comp_dependent (\<lambda>(c, _). \<EE> c) meas) =
               kf_apply (kf_comp_dependent (\<lambda>(c, _). km_some_kraus_family (D c \<circ> E c)) meas)\<close>
    by -
qed

lemma denotation_while_n_sum:
  \<open>(\<Sum>n\<le>M. denotation_while_n e D n) = denotation_cases (\<lambda>m. if e m then 0 else 1) * (denotation_cases (\<lambda>m. if e m then D else 1))^M\<close>
proof (induction M)
  case 0
  show ?case
    by (simp add: denotation_while_n_def)
next
  case (Suc M)
  define eD1 eD "note" where \<open>eD1 = denotation_cases (\<lambda>m. if e m then D else 1)\<close>
    and \<open>eD = denotation_cases (\<lambda>m. if e m then D else 0)\<close>
    and \<open>note = denotation_cases (\<lambda>m. if e m then 0 else 1)\<close>
  have bdd_cases: \<open>bdd_above (range (\<lambda>m. denotation_norm (if e m then X else Y)))\<close> for X Y
    apply (rule bdd_aboveI2[where M=\<open>max (denotation_norm X) (denotation_norm Y)\<close>])
    by auto
  have eD1_decomp: \<open>eD1 = eD + note\<close>
    by (auto simp add: eD1_def eD_def note_def bdd_cases simp flip: denotation_cases_plus
        intro!: arg_cong[where f=denotation_cases])
  have note_idem: \<open>note * note = note\<close>
    unfolding note_def
    apply (subst denotation_merge)
    by (auto intro!: arg_cong[where f=denotation_cases] bdd_cases)
  have eD_note: \<open>eD * note = 0\<close>
    unfolding note_def eD_def
    apply (subst denotation_merge)
     apply (auto intro!: arg_cong[where f=denotation_cases] bdd_cases)[3]
    apply (rewrite at \<open>denotation_cases (\<lambda>c. \<hole>)\<close> to 0 DEADID.rel_mono_strong)
    by (auto simp flip: zero_fun_def)

  have \<open>note * eD1^(Suc M) = note * eD1 * eD1^M\<close>
    by (simp add: Extra_Ordered_Fields.sign_simps(4))
  also have \<open>\<dots> = note * (eD + note) * eD1^M\<close>
    using eD1_decomp by fastforce
  also have \<open>\<dots> = note * eD * eD1^M + (note * note) * eD1^M\<close>
    by (simp add: distrib_left distrib_right mult.assoc)
  also have \<open>\<dots> = note * eD * eD1^M + note * eD1^M\<close>
    using note_idem by presburger
  also have \<open>\<dots> = note * eD * eD1^M + (\<Sum>n\<le>M. denotation_while_n e D n)\<close>
    using Suc.IH eD1_def note_def by argo
  also have \<open>\<dots> = denotation_while_n e D (Suc M) + (\<Sum>n\<le>M. denotation_while_n e D n)\<close>
  proof (rule arg_cong[where f=\<open>\<lambda>x. x + _\<close>], induction M)
    case 0
    show ?case
      by (simp add: denotation_while_n_def eD_def note_def)
  next
    case (Suc M)
    have \<open>note * eD * eD1^(Suc M) = denotation_while_n e D (Suc M) * eD1\<close>
      by (simp add: mult.assoc power_commutes flip: Suc.IH)
    also have \<open>\<dots> = denotation_while_n e D M * (eD * (eD + note))\<close>
      apply (simp add: denotation_while_n_def flip: eD1_def eD_def eD1_decomp)
      by (metis Groups.mult_ac(1) power_commutes)
    also have \<open>\<dots> = denotation_while_n e D M * (eD * eD)\<close>
      by (simp add: distrib_left distrib_right eD_note flip: mult.assoc)
    also have \<open>\<dots> = denotation_while_n e D (Suc (Suc M))\<close>
      apply (simp add: denotation_while_n_def flip: eD_def mult.assoc)
      by (simp add: Extra_Ordered_Fields.sign_simps(4) power_commutes)
    finally show ?case
      by -
  qed
  also have \<open>\<dots> = (\<Sum>n\<le>Suc M. denotation_while_n e D n)\<close>
    by (simp add: add.commute)
  finally show \<open>\<dots> = note * eD1^(Suc M)\<close>
    by simp
qed


definition denotation_while :: \<open>(cl \<Rightarrow> bool) \<Rightarrow> denotation \<Rightarrow> denotation\<close> where 
  \<open>denotation_while e D = (\<Sum>\<^sub>\<infinity>n. denotation_while_n e D n)\<close>



end
