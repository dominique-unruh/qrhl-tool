theory Denotation
  imports CQ_Operators QRHL_Core
begin

type_synonym program_state = \<open>((cl\<times>qu) ell2, (cl\<times>qu) ell2) trace_class\<close>

typedef denotation = \<open>{\<EE> :: program_state \<Rightarrow> program_state. is_cq_map qFst \<EE>}\<close>
  morphisms apply_denotation Abs_denotation
  by (auto intro!: exI[of _ 0])

setup_lifting type_definition_denotation

lemma is_cq_map_apply_denotation[iff]: \<open>is_cq_map qFst (apply_denotation E)\<close>
  using apply_denotation by blast

lemma kraus_map_apply_denotation[iff]: \<open>kraus_map (apply_denotation E)\<close>
  using is_cq_map_def by blast


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
  \<open>\<lambda>D E. E o D\<close>
  by (smt (verit, best) cq_map_id_left fun.map_comp is_cq_map_def kraus_map_comp)
lift_definition plus_denotation :: \<open>denotation \<Rightarrow> denotation \<Rightarrow> denotation\<close> is
  \<open>\<lambda>D E \<rho>. D \<rho> + E \<rho>\<close>
  by (auto intro!: is_cq_map_plus)
instance..
end

lemmas [simp] = zero_denotation.rep_eq

lemma zero_denotation_bounded[iff]: \<open>denotation_norm 0 = 0\<close>
  apply transfer
  by simp

lemma one_denotation_bounded[iff]: \<open>denotation_norm 1 = 1\<close>
  apply transfer
  by simp

lemma times_denotation_bounded: \<open>denotation_norm (D * E) \<le> denotation_norm D * denotation_norm E\<close>
  apply transfer
  by (metis Groups.mult_ac(2) is_cq_map_def km_comp_norm_leq)

instance denotation :: power..

lemma power_denotation_bounded: \<open>denotation_norm (D^n) \<le> denotation_norm D ^ n\<close>
  apply (induction n)
  by (auto intro!: times_denotation_bounded[THEN order_trans] mult_mono)

instantiation denotation :: monoid_mult begin
instance
proof intro_classes
  fix a b c :: denotation
  show \<open>a * b * c = a * (b * c)\<close>
    apply transfer'
    by fastforce
  show \<open>1 * a = a\<close>
    apply transfer
    using cq_map_id_right by blast
  show \<open>a * 1 = a\<close>
    apply transfer
    using cq_map_id_left by blast
qed
end

instantiation denotation :: topological_space begin
lift_definition open_denotation :: \<open>denotation set \<Rightarrow> bool\<close> is \<open>openin (top_of_set (Collect (is_cq_map qFst)))\<close>.
instance
proof intro_classes
  show \<open>open (UNIV :: denotation set)\<close>
    apply (simp add: open_denotation_def)
    by (smt (verit, best) Abs_denotation_inverse UNIV_I apply_denotation imageE image_eqI openin_subopen
        openin_subtopology_self subsetI)
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

lemma hausdorff_bounded_clinear[iff]: \<open>Hausdorff_space (top_of_set (Collect bounded_clinear))\<close>
proof -
  note [transfer_rule] = rel_topology_bounded_linear_sot
  have [transfer_rule]: \<open>bi_unique cr_cblinfun\<close>
    by (metis bi_total_eq bi_unique_eq cblinfun.bi_unique cblinfun.pcr_cr_eq)
  show ?thesis
    using hausdorff_sot[where 'a='a and 'b='b]
    by (transfer, blast)
qed

instantiation denotation :: t2_space begin
instance
proof -
  define S :: \<open>(((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class \<Rightarrow> ((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class) set\<close>
    where \<open>S = Collect (is_cq_map qFst)\<close>
  have hausdorff_S: \<open>Hausdorff_space (top_of_set S)\<close>
  proof -
    have \<open>S \<subseteq> Collect bounded_clinear\<close>
      using apply_denotation
      by (auto intro!: kraus_map_bounded_clinear simp add: S_def is_cq_map_def)
    then have top_S: \<open>top_of_set S = subtopology (top_of_set (Collect bounded_clinear)) S\<close>
      by (metis (no_types, lifting) subtopology_subtopology topspace_euclidean_subtopology
          topspace_subtopology_subset)
    show \<open>Hausdorff_space (top_of_set S)\<close>
      using Hausdorff_space_subtopology top_S hausdorff_bounded_clinear by metis
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
    apply transfer
    by (auto intro!: ext simp: complex_vector.linear_0 is_cq_map_def complex_vector.linear_0 bounded_clinear.clinear kraus_map_bounded_clinear)
  show \<open>D * 0 = 0\<close>
    apply transfer
    by auto
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
  \<open>denotation_while_n e D n = (denotation_cases (\<lambda>m. if e m then D else 0))^n * denotation_cases (\<lambda>m. if e m then 0 else 1)\<close>

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

(* TODO move *)
lemma kf_filter_comp_singleton: \<open>kf_filter ((=) x) (kf_comp \<EE> \<FF>) = kf_comp (kf_filter ((=) (snd x)) \<EE>) (kf_filter ((=) (fst x)) \<FF>)\<close>
  apply (simp add: case_prod_unfold flip: kf_filter_comp)
  by (metis prod.expand)

(* TODO move *)
lemma kf_filter_comp_dependent_singleton: 
  assumes \<open>bdd_above ((kf_norm \<circ> \<EE>) ` kf_domain \<FF>)\<close>
  shows \<open>kf_filter ((=) x) (kf_comp_dependent \<EE> \<FF>) = kf_comp (kf_filter ((=) (snd x)) (\<EE> (fst x))) (kf_filter ((=) (fst x)) \<FF>)\<close>
proof -
  have \<open>kf_filter ((=) x) (kf_comp_dependent \<EE> \<FF>) = kf_comp_dependent (\<lambda>y. kf_filter ((=) (snd x)) (\<EE> y)) (kf_filter ((=) (fst x)) \<FF>)\<close>
    apply (subst kf_filter_comp_dependent[symmetric])
     apply (fact assms)
    apply (simp_all add: case_prod_unfold)
    by (metis prod.expand)
  also have \<open>\<dots> = kf_comp (kf_filter ((=) (snd x)) (\<EE> (fst x))) (kf_filter ((=) (fst x)) \<FF>)\<close>
    by (auto intro!: kf_comp_dependent_cong_left simp: kf_comp_def)
  finally show ?thesis
    by -
qed

(* TODO move *)
lemma kf_filter_kf_complete_measurement_singleton:
  assumes \<open>is_ortho_set B\<close> and \<open>x \<in> B\<close>
  shows \<open>kf_filter ((=) x) (kf_complete_measurement B) = kf_map_inj (\<lambda>_. x) (kf_of_op (selfbutter (sgn x)))\<close>
proof -
  have \<open>selfbutter (sgn x) \<noteq> 0\<close>
    by (smt (verit) assms(1,2) is_ortho_set_def mult_cancel_right1 norm_butterfly norm_sgn norm_zero)
  then show ?thesis
    apply (transfer' fixing: B x)
    by (auto simp add: assms)
qed

(* TODO move *)
lemma kf_filter_kf_complete_measurement_ket_singleton:
  \<open>kf_filter ((=) x) kf_complete_measurement_ket = kf_map_inj (\<lambda>_. x) (kf_of_op (selfbutter (ket x)))\<close>
proof -
  have neq0: \<open>selfbutter |x\<rangle> \<noteq> 0\<close>
    using butterfly_apply[of \<open>ket x\<close> \<open>ket x\<close> \<open>ket x\<close>]
    by force
  have \<open>kf_filter ((=) x) kf_complete_measurement_ket = kf_map_inj (inv ket) (kf_filter (\<lambda>xa. x = inv ket xa) (kf_complete_measurement (range ket)))\<close>
    by (simp add: kf_complete_measurement_ket_def kf_filter_map_inj)
  also have \<open>\<dots> = kf_map_inj (inv ket) (kf_filter ((=) (ket x)) (kf_complete_measurement (range ket)))\<close>
    apply (rule arg_cong[where f=\<open>kf_map_inj _\<close>])
    apply (rule kf_filter_cong_eq[OF refl])
    by auto
  also have \<open>\<dots> = kf_map_inj (inv ket) (kf_map_inj (\<lambda>_. ket x) (kf_of_op (selfbutter (ket x))))\<close>
    apply (rule arg_cong[where f=\<open>kf_map_inj _\<close>])
    apply (transfer' fixing: x )
    by (auto simp: image_iff neq0)
  also have \<open>\<dots> = kf_map_inj (\<lambda>_. x) (kf_of_op (selfbutter (ket x)))\<close>
    by (simp add: kf_map_inj_twice)
  finally show ?thesis
    by -
qed

(* TODO move *)
lemma separating_set_tensor_ell2: \<open>separating_set bounded_clinear ((\<lambda>(g,h). g \<otimes>\<^sub>s h) ` (UNIV \<times> UNIV))\<close>
  apply (rule separating_set_bounded_clinear_dense)
  apply (rewrite at \<open>ccspan \<hole>\<close> to \<open>{x. \<exists>a b. x = a \<otimes>\<^sub>s b}\<close> DEADID.rel_mono_strong)
  using tensor_ell2_dense'[of UNIV UNIV]
  by auto

(* TODO move *)
lemma separating_set_tensor_ell2_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c::complex_normed_vector) \<Rightarrow> _) A\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c) \<Rightarrow> _) ((\<lambda>(g,h). g \<otimes>\<^sub>s h) ` (A \<times> B))\<close>
  apply (rule separating_set_bounded_cbilinear_nested)
     apply (rule separating_set_tensor_ell2)
  using bounded_cbilinear_tensor_ell2 apply force
  using assms by simp_all

(* TODO move *)
lemma sandwich_tc_tensor_ell2_left: \<open>sandwich_tc (tensor_ell2_left h*) (tc_tensor t u) = (h \<bullet>\<^sub>C tc_apply t h) *\<^sub>C u\<close>
  apply (transfer' fixing: h)
  by (simp add: sandwich_tensor_ell2_left)

lemma tc_butterfly_apply[simp]: \<open>tc_apply (tc_butterfly g h) k = (h \<bullet>\<^sub>C k) *\<^sub>C g\<close>
  apply (transfer' fixing: g h k)
  by simp

(*
lemma circularity_of_trace:
  \<comment> \<open>TODO cite "mathoverflow-circ-trace2"\<close>
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> and b :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    \<comment> \<open>The proof from \<open>conway00operator\<close> only works for square operators, we generalize it\<close>
  assumes \<open>trace_class (a o\<^sub>C\<^sub>L b)\<close> and \<open>trace_class (b o\<^sub>C\<^sub>L a)\<close>
    \<comment> \<open>Only \<^term>\<open>trace_class (a o\<^sub>C\<^sub>L b)\<close> is not sufficient, see "mathoverflow-circ-trace1"}.\<close>
  shows \<open>trace (a o\<^sub>C\<^sub>L b) = trace (b o\<^sub>C\<^sub>L a)\<close>
proof -
  (* We first make a and b into square operators by padding them because for those the circularity of the trace is easier. *)
  define a' b' :: \<open>('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b)\<close> 
    where \<open>a' = cblinfun_right o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L cblinfun_left*\<close>
      and \<open>b' = cblinfun_left o\<^sub>C\<^sub>L b o\<^sub>C\<^sub>L cblinfun_right*\<close>
  have \<open>trace_class (cblinfun_right o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L b o\<^sub>C\<^sub>L cblinfun_right* :: ('a \<times> 'b) \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b))\<close>
    apply (rule trace_class_comp_left)
    apply (subst cblinfun_assoc_right)
    apply (rule trace_class_comp_right)
    by (fact assms)
  then have \<open>trace_class (a' o\<^sub>C\<^sub>L b')\<close>
    by (simp add: a'_def b'_def lift_cblinfun_comp[OF isometryD[OF isometry_cblinfun_left]] cblinfun_assoc_left)
  have \<open>trace_class ((cblinfun_left o\<^sub>C\<^sub>L b o\<^sub>C\<^sub>L a) o\<^sub>C\<^sub>L cblinfun_left* :: ('a \<times> 'b) \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b))\<close>
    apply (rule trace_class_comp_left)
    apply (subst cblinfun_assoc_right)
    apply (rule trace_class_comp_right)
    by (fact assms)
  then have \<open>trace_class (b' o\<^sub>C\<^sub>L a')\<close>
    by (simp add: a'_def b'_def lift_cblinfun_comp[OF isometryD[OF isometry_cblinfun_right]] cblinfun_assoc_left)
  define u p where \<open>u = polar_decomposition a'\<close> and \<open>p = abs_op a'\<close>
  have \<open>a' = u o\<^sub>C\<^sub>L p\<close>
    by (simp add: p_def polar_decomposition_correct u_def)
  have \<open>p o\<^sub>C\<^sub>L b' = u* o\<^sub>C\<^sub>L a' o\<^sub>C\<^sub>L b'\<close>
    by (simp add: p_def polar_decomposition_correct' u_def)
  also from \<open>trace_class (a' o\<^sub>C\<^sub>L b')\<close>
  have \<open>trace_class (u* o\<^sub>C\<^sub>L a' o\<^sub>C\<^sub>L b')\<close>
    by (simp add: cblinfun_assoc_right trace_class_comp_right)
  finally have \<open>trace_class (p o\<^sub>C\<^sub>L b')\<close>
    by -
  then have \<open>trace (u o\<^sub>C\<^sub>L p o\<^sub>C\<^sub>L b') = trace (p o\<^sub>C\<^sub>L b' o\<^sub>C\<^sub>L u)\<close>
    by (simp add: cblinfun_assoc_right flip: circularity_of_trace)
  moreover have \<open>trace (p o\<^sub>C\<^sub>L b' o\<^sub>C\<^sub>L u) = trace (b' o\<^sub>C\<^sub>L u o\<^sub>C\<^sub>L p)\<close>
  proof -
    define a b where \<open>a = p\<close> and \<open>b = b' o\<^sub>C\<^sub>L u\<close>

    thm eigenspace_is_reducing

(* 

pn = proj (SUP eigenspaces \<ge> 1/n)

pn invariant subspace \<Longrightarrow> pn a = pn a pn  (a comm. pn not needed)

But: pn a \<longrightarrow> a  not clear.



 *)

    define p where \<open>p n = (\<Sum>i<n. spectral_dec_proj_tc a i)\<close> for n
    have \<open>trace (a o\<^sub>C\<^sub>L b) = trace (b o\<^sub>C\<^sub>L a)\<close>
      by x
    then show ?thesis
      by (simp add: a_def b_def cblinfun_assoc_left)
  qed
  ultimately have circ': \<open>trace (a' o\<^sub>C\<^sub>L b') = trace (b' o\<^sub>C\<^sub>L a')\<close>
    using \<open>a' = u o\<^sub>C\<^sub>L p\<close>[symmetric]
    apply simp
    by (simp add: cblinfun_assoc_right)
  show ?thesis
  proof -
    have \<open>trace (a o\<^sub>C\<^sub>L b) = trace (cblinfun_right o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L b o\<^sub>C\<^sub>L cblinfun_right* :: ('a \<times> 'b) \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b))\<close>
      apply (subst (2) circularity_of_trace)
       apply (simp add: trace_class_comp_right assms cblinfun_assoc_right)
      by (simp add: lift_cblinfun_comp[OF isometryD[OF isometry_cblinfun_left]] cblinfun_assoc_left)
    also have \<open>\<dots> = trace (a' o\<^sub>C\<^sub>L b')\<close>
      by (simp add: a'_def b'_def lift_cblinfun_comp[OF isometryD[OF isometry_cblinfun_left]] cblinfun_assoc_left)
    also from circ' have \<open>\<dots> = trace (b' o\<^sub>C\<^sub>L a')\<close>
      by -
    also have \<open>\<dots> = trace (cblinfun_left o\<^sub>C\<^sub>L b o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L cblinfun_left* :: ('a \<times> 'b) \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b))\<close>
      by (simp add: a'_def b'_def lift_cblinfun_comp[OF isometryD[OF isometry_cblinfun_right]] cblinfun_assoc_left)
    also have \<open>\<dots> = trace (b o\<^sub>C\<^sub>L a)\<close>
      apply (subst circularity_of_trace)
       apply (simp add: trace_class_comp_right assms cblinfun_assoc_right)
      by (simp add: lift_cblinfun_comp[OF isometryD[OF isometry_cblinfun_left]] cblinfun_assoc_left)
    finally show ?thesis
      by -
  qed
qed
*)


lemma trace_sandwich_add_left:
  assumes \<open>e* o\<^sub>C\<^sub>L f = 0\<close>
  assumes [simp]: \<open>trace_class (e o\<^sub>C\<^sub>L t)\<close> \<open>trace_class (f o\<^sub>C\<^sub>L t)\<close>
  shows \<open>trace (sandwich (e + f) t) = trace (sandwich e t) + trace (sandwich f t)\<close>
proof -
  have [simp]: \<open>f* o\<^sub>C\<^sub>L e = 0\<close>
    by (metis adj_0 adj_cblinfun_compose assms(1) double_adj)
  have [simp]: \<open>trace_class ((e + f) o\<^sub>C\<^sub>L t)\<close>
    by (simp add: cblinfun_compose_add_left)
  have [simp]: \<open>trace_class (e* o\<^sub>C\<^sub>L e o\<^sub>C\<^sub>L t)\<close>
    by (simp add: cblinfun_compose_assoc trace_class_comp_right)
  have [simp]: \<open>trace_class (f* o\<^sub>C\<^sub>L f o\<^sub>C\<^sub>L t)\<close>
    by (simp add: cblinfun_compose_assoc trace_class_comp_right)

  have \<open>trace (sandwich (e + f) t) = trace (((e + f)* o\<^sub>C\<^sub>L (e + f)) o\<^sub>C\<^sub>L t)\<close>
    by (simp add: sandwich_apply circularity_of_trace flip: cblinfun_compose_assoc)
  also have \<open>\<dots> = trace (((e* o\<^sub>C\<^sub>L e) + (f* o\<^sub>C\<^sub>L f)) o\<^sub>C\<^sub>L t)\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>x. trace (x o\<^sub>C\<^sub>L _)\<close>])
    by (simp add: cblinfun_compose_add_right cblinfun_compose_add_left adj_plus assms)
  also have \<open>\<dots> = trace ((e* o\<^sub>C\<^sub>L e) o\<^sub>C\<^sub>L t) + trace ((f* o\<^sub>C\<^sub>L f) o\<^sub>C\<^sub>L t)\<close>
    by (simp add: cblinfun_compose_add_left trace_plus)
  also have \<open>\<dots> = trace (sandwich e t) + trace (sandwich f t)\<close>
    by (simp add: sandwich_apply circularity_of_trace flip: cblinfun_compose_assoc)
  finally show ?thesis
    by -
qed

(* TODO move *)
lemma trace_sandwich_diff_left:
  assumes \<open>e* o\<^sub>C\<^sub>L f = f* o\<^sub>C\<^sub>L f\<close>
  assumes [simp]: \<open>trace_class (e o\<^sub>C\<^sub>L t)\<close> \<open>trace_class (f o\<^sub>C\<^sub>L t)\<close>
  shows \<open>trace (sandwich (e - f) t) = trace (sandwich e t) - trace (sandwich f t)\<close>
  using trace_sandwich_add_left[of \<open>e - f\<close> f t] assms
  by (simp add: cblinfun_compose_minus_left adj_minus)

(* TODO move *)
lemma trace_sandwich_tc_add_left:
  assumes \<open>e* o\<^sub>C\<^sub>L f = 0\<close>
  shows \<open>trace_tc (sandwich_tc (e + f) t) = trace_tc (sandwich_tc e t) + trace_tc (sandwich_tc f t)\<close>
  apply (transfer fixing: e f)
  by (simp add: trace_sandwich_add_left trace_class_comp_right assms)

(* TODO move *)
lemma trace_sandwich_tc_diff_left:
  assumes \<open>e* o\<^sub>C\<^sub>L f = f* o\<^sub>C\<^sub>L f\<close>
  shows \<open>trace_tc (sandwich_tc (e - f) t) = trace_tc (sandwich_tc e t) - trace_tc (sandwich_tc f t)\<close>
  using trace_sandwich_tc_add_left[of \<open>e - f\<close> f t] assms
  by (simp add: cblinfun_compose_minus_left adj_minus)

(* TODO move *)
lemma hilbert_schmidt_sqrt_op:
  assumes \<open>trace_class t\<close>
  shows \<open>hilbert_schmidt (sqrt_op t)\<close>
  by (metis assms hilbert_schmidtI sqrt_op_def sqrt_op_unique trace_class_0 trace_class_comp_right)

(* lemma trace_sandwich_mono_left:
  assumes \<open>e* o\<^sub>C\<^sub>L e \<le> f* o\<^sub>C\<^sub>L f\<close>
  assumes \<open>t \<ge> 0\<close>
  assumes \<open>trace_class (sqrt_op t)\<close>
    \<comment> \<open>This is stronger than needed, but we'd need to weaken the condition \<^term>\<open>trace_class a\<close> in @{thm [source] circularity_of_trace} first (see there).\<close>
  shows \<open>trace (sandwich e t) \<le> trace (sandwich f t)\<close>
proof -
  have [simp]: \<open>trace_class t\<close>
    by (metis assms(2,3) sqrt_op_square trace_class_comp_right)
  have \<open>trace (sandwich e t) = trace (e* o\<^sub>C\<^sub>L e o\<^sub>C\<^sub>L t)\<close>
    by (simp add: sandwich_apply trace_class_comp_right circularity_of_trace assms cblinfun_assoc_left)
  also have \<open>\<dots> = trace (e* o\<^sub>C\<^sub>L e o\<^sub>C\<^sub>L sqrt_op t* o\<^sub>C\<^sub>L sqrt_op t)\<close>
    by (simp add: cblinfun_assoc_right sqrt_op_square assms sqrt_op_pos pos_selfadjoint selfadjoint_def[THEN iffD1])
  also have \<open>\<dots> = trace (sandwich (sqrt_op t) (e* o\<^sub>C\<^sub>L e))\<close>
    by (simp add: sandwich_apply trace_class_comp_right circularity_of_trace assms cblinfun_assoc_left)
  also have \<open>\<dots> \<le> trace (sandwich (sqrt_op t) (f* o\<^sub>C\<^sub>L f))\<close>
    by (metis assms(1,3) sandwich_apply sandwich_mono trace_cblinfun_mono trace_class_adj trace_class_comp_right)
  also have \<open>\<dots> = trace (f* o\<^sub>C\<^sub>L f o\<^sub>C\<^sub>L sqrt_op t* o\<^sub>C\<^sub>L sqrt_op t)\<close>
    by (simp add: sandwich_apply trace_class_comp_right circularity_of_trace assms cblinfun_assoc_left)
  also have \<open>\<dots> = trace (f* o\<^sub>C\<^sub>L f o\<^sub>C\<^sub>L t)\<close>
    by (simp add: cblinfun_assoc_right sqrt_op_square assms sqrt_op_pos pos_selfadjoint selfadjoint_def[THEN iffD1])
  also have \<open>\<dots> = trace (sandwich f t)\<close>
    by (simp add: sandwich_apply trace_class_comp_right circularity_of_trace assms cblinfun_assoc_left)
  finally show ?thesis
    by -
qed *)

lemma trace_sandwich_mono_left:
  assumes \<open>e \<le> f\<close>
  assumes \<open>t \<ge> 0\<close>
  assumes \<open>f* o\<^sub>C\<^sub>L e = e* o\<^sub>C\<^sub>L e\<close>
  assumes [simp]: \<open>trace_class (e o\<^sub>C\<^sub>L t)\<close> \<open>trace_class (f o\<^sub>C\<^sub>L t)\<close>
  shows \<open>trace (sandwich e t) \<le> trace (sandwich f t)\<close>
proof -
  have \<open>trace (sandwich e t) \<le> trace (sandwich (f - e) t) + trace (sandwich e t)\<close>
    by (simp add: assms(2) sandwich_pos trace_pos)
  also have \<open>\<dots> = trace (sandwich ((f-e) + e) t)\<close>
    apply (rule trace_sandwich_add_left[symmetric])
    by (simp_all add: cblinfun_compose_minus_left adj_minus assms cblinfun_compose_minus_left)
  also have \<open>\<dots> = trace (sandwich f t)\<close>
    by simp
  finally show ?thesis
    by -
qed


lemma trace_sandwich_tc_mono_left:
  assumes \<open>e \<le> f\<close>
  assumes \<open>t \<ge> 0\<close>
  assumes \<open>f* o\<^sub>C\<^sub>L e = e* o\<^sub>C\<^sub>L e\<close>
  shows \<open>trace_tc (sandwich_tc e t) \<le> trace_tc (sandwich_tc f t)\<close>
  using assms
  apply (transfer fixing: e f)
  by (auto intro!: trace_class_comp_right trace_sandwich_mono_left)


lemma is_Proj_pos:
  assumes \<open>is_Proj P\<close>
  shows \<open>P \<ge> 0\<close>
  by (metis assms is_Proj_algebraic positive_cblinfun_squareI)


lemma denotation_merge:
  assumes \<open>bdd_above (range (denotation_norm o E))\<close>
  assumes \<open>bdd_above (range (denotation_norm o D))\<close>
  assumes E_readonly: \<open>\<And>c \<rho>. let \<rho>' = apply_denotation (E c) (tc_tensor (tc_butterfly (ket c) (ket c)) \<rho>) in
                             sandwich_tc (selfbutter (ket c) \<otimes>\<^sub>o id_cblinfun) \<rho>' = \<rho>'\<close>
  shows \<open>denotation_cases E * denotation_cases D = denotation_cases (\<lambda>c. E c * D c)\<close>
proof (rule apply_denotation_inject[THEN iffD1])
  write kf_comp (infixl "\<bullet>" 70)
  write kf_comp_dependent (infixl "\<bullet>\<bullet>" 70)
  write kf_map (infixr "``" 75)
  define D' E' where \<open>D' x = apply_denotation (D x)\<close> and \<open>E' x = apply_denotation (E x)\<close> for x
  then have \<open>is_cq_map qFst (D' c)\<close> and \<open>is_cq_map qFst (E' c)\<close> for c
    using apply_denotation
    by simp_all
  then have [iff]: \<open>kraus_map (D' c)\<close>   \<open>kraus_map (E' c)\<close> for c
    by (simp_all add: is_cq_map_def)
  define \<DD> \<EE> where \<open>\<DD> c = km_some_kraus_family (D' c)\<close> and \<open>\<EE> c = km_some_kraus_family (E' c)\<close> for c
  define meas :: \<open>((cl \<times> qu) ell2, (cl \<times> qu) ell2, cl \<times> unit) kraus_family\<close>
    where \<open>meas = kf_tensor kf_complete_measurement_ket kf_id\<close>
  have apply\<DD>: \<open>kf_apply (\<DD> c) = D' c\<close> and apply\<EE>: \<open>kf_apply (\<EE> c) = E' c\<close> for c
    using \<DD>_def \<EE>_def by force+

  from assms
  have bdd\<DD>': \<open>bdd_above (range (km_norm \<circ> D'))\<close>
    by (simp add: D'_def denotation_norm.rep_eq)
  then have bdd\<DD>: \<open>bdd_above ((\<lambda>x. kf_norm (\<DD> (f x))) ` X)\<close> for f X
    apply (rule bdd_above_mono)
    by (auto simp: km_norm_kf_norm simp flip: apply\<DD>)
  from assms
  have bdd\<EE>': \<open>bdd_above (range (km_norm \<circ> E'))\<close>
    by (simp add: E'_def denotation_norm.rep_eq)
  then have bdd\<EE>: \<open>bdd_above ((\<lambda>x. kf_norm (\<EE> (g x))) ` X)\<close> for g X
    apply (rule bdd_above_mono)
    by (auto simp: km_norm_kf_norm simp flip: apply\<EE>)
  from bdd\<DD> bdd\<EE>
  have \<open>bdd_above ((\<lambda>x. kf_norm (\<DD> (g x)) * kf_norm (\<EE> (f x))) ` X)\<close> for f g X
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


  have \<open>apply_denotation (denotation_cases E * denotation_cases D)
    = kf_apply ((\<lambda>(c, _). \<DD> c) \<bullet>\<bullet> meas) \<circ> kf_apply ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)\<close>
    by (simp add: denotation_cases.rep_eq times_denotation.rep_eq meas_def \<DD>_def D'_def \<EE>_def E'_def)
  also have \<open>\<dots> = kf_apply (((\<lambda>(c, _). \<DD> c) \<bullet>\<bullet> meas) \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas))\<close>
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
  proof (intro ext kf_apply_eqI kf_comp_dependent_cong_weak kf_eq_weak_reflI kf_map_cong kf_eq_refl)
    show \<open>bdd_above ((kf_norm \<circ> \<DD>) ` kf_domain ((\<lambda>(_, c, _). c) `` (meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas))))\<close>
      by (auto intro!: bdd\<DD>)
    have \<open>c = d\<close> if \<open>(((c,()),()),(d,())) \<in> kf_domain (meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas))\<close> for c d
    proof (rule ccontr)
      assume \<open>c \<noteq> d\<close>
      have app_map: \<open>kf_apply (kf_map_inj (\<lambda>_::unit. d) E) = kf_apply E\<close> for d E
        by (auto intro!: ext kf_apply_map_inj inj_onI)
      from that
      have \<open>kf_apply_on (meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)) {(((c,()),()),(d,()))} \<noteq> 0\<close> (is \<open>?f \<noteq> 0\<close>)
        by (simp add: in_kf_domain_iff_apply_nonzero)
      moreover have \<open>clinear ?f\<close>
        by (intro bounded_clinear.clinear bounded_linear_intros)
      ultimately obtain \<rho> where \<open>(meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)) *\<^sub>k\<^sub>r @{(((c,()),()),(d,()))} \<rho> \<noteq> 0\<close> and \<open>\<rho> \<ge> 0\<close>
        using eq_from_separatingIx[OF separating_density_ops[of 1], of ?f 0]
        by (auto intro!: simp: zero_fun_def complex_vector.linear_zero)
      then have \<open>(kf_filter ((=) (d, ())) meas \<bullet> (\<EE> c \<bullet> kf_filter ((=) (c, ())) meas)) *\<^sub>k\<^sub>r \<rho> \<noteq> 0\<close>
        apply (simp add: kf_apply_on_def)
        apply (subst (asm) flip_eq_const)
        by (simp add: kf_apply_on_def kf_filter_comp_singleton kf_filter_comp_dependent_singleton
            flip_eq_const bdd\<EE> case_prod_unfold)
      then have \<open>km_tensor (sandwich_tc (selfbutter |d\<rangle>)) id (E' c (km_tensor (sandwich_tc (selfbutter |c\<rangle>)) id \<rho>)) \<noteq> 0\<close>
        by (simp add: meas_def kf_filter_tensor_singleton
            kf_filter_kf_complete_measurement_ket_singleton kf_comp_apply kf_id_apply[abs_def]
            app_map kf_of_op_apply[abs_def] apply\<EE>
            flip: km_tensor_kf_tensor id_def)
      then have neq0: \<open>sandwich_tc (selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun) (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>)) \<noteq> 0\<close>
        by (simp add: sandwich_tc_id_cblinfun[abs_def] id_def flip: km_tensor_sandwich_tc)
      moreover have \<open>sandwich_tc (selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun) (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>)) = 0\<close>
      proof -
        have *: \<open>sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho> = tc_tensor (tc_butterfly |c\<rangle> |c\<rangle>) (sandwich_tc (tensor_ell2_left |c\<rangle>*) \<rho>)\<close>
          apply (rule eq_from_separatingI2x[where x=\<rho>])
             apply (rule separating_set_bounded_clinear_tc_tensor_nested)
              apply (rule separating_set_tc_butterfly_nested)
               apply (rule separating_set_ket)
              apply (rule separating_set_ket)
             apply (rule separating_set_UNIV)
            apply (intro bounded_linear_intros)
           apply (intro bounded_linear_intros)
          by (auto simp add: sandwich_tc_tensor sandwich_tc_butterfly sandwich_tc_tensor_ell2_left cinner_ket)
        have \<open>norm (sandwich_tc (selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun) (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>)))
             = trace_tc (sandwich_tc (selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun) (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>)))\<close>
          apply (auto intro!: norm_tc_pos sandwich_tc_pos kraus_map_pos[of \<open>E' c\<close>] \<open>\<rho> \<ge> 0\<close>)
          by -
        also 
        have \<open>\<dots> \<le> trace_tc (sandwich_tc (id_cblinfun - (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun)) (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>)))\<close>
        proof (rule trace_sandwich_tc_mono_left)
          from \<open>c \<noteq> d\<close>
          have \<open>is_Proj (id_cblinfun - selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun - selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun)\<close>
            by (simp add: is_Proj_algebraic tensor_op_adjoint comp_tensor_op adj_minus cblinfun_compose_minus_left
                cblinfun_compose_minus_right orthogonal_ket[THEN iffD2])
          then show \<open>selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun \<le> id_cblinfun - selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun\<close>
            apply (rule_tac diff_ge_0_iff_ge[THEN iffD1])
            by (rule is_Proj_pos)
          show \<open>0 \<le> E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>)\<close>
            by (auto intro!: kraus_map_pos[of \<open>E' c\<close>] sandwich_tc_pos \<open>\<rho> \<ge> 0\<close>)
          from \<open>c \<noteq> d\<close>
          show \<open>(id_cblinfun - selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun)* o\<^sub>C\<^sub>L selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun = (selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun)* o\<^sub>C\<^sub>L selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun\<close>
            by (auto simp: tensor_op_adjoint comp_tensor_op adj_minus cblinfun_compose_minus_left orthogonal_ket[THEN iffD2])
        qed
        also have \<open>\<dots> = trace_tc (sandwich_tc id_cblinfun (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>)))
         - trace_tc (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>)))\<close>
          apply (rule trace_sandwich_tc_diff_left)
          by (simp add: tensor_op_adjoint comp_tensor_op adj_minus cblinfun_compose_minus_left)
        also have \<open>\<dots> = trace_tc (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>))
         - trace_tc (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>))\<close>
          apply (rule arg_cong2[where f=minus])
           apply force 
          using E_readonly[of c]
          by (simp add: E'_def[symmetric] Let_def * )
        also have \<open>\<dots> = 0\<close>
          by simp
        finally show ?thesis
          by (metis complex_of_real_mono_iff norm_le_zero_iff of_real_0)
      qed
(* OLD PROOF *)
(*       proof (rule eq_from_separatingIx[where x=\<rho>, OF separating_density_ops])
        show \<open>0 < (1::real)\<close>
          by simp
        show \<open>clinear (\<lambda>a. sandwich_tc (selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun) (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) a)))\<close>
          by (intro bounded_clinear.clinear bounded_linear_intros kraus_map_bounded_clinear[OF \<open>kraus_map (E' c)\<close>, THEN comp_bounded_clinear, unfolded o_def])
        show \<open>clinear (\<lambda>a. 0)\<close>
          using complex_vector.linear_zero by blast
        fix \<rho> :: \<open>((cl \<times> qu) ell2, (cl \<times> qu) ell2) trace_class\<close>
        assume \<rho>pos: \<open>\<rho> \<in> {t. 0 \<le> t \<and> norm t \<le> 1}\<close>
        have *: \<open>sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho> = tc_tensor (tc_butterfly |c\<rangle> |c\<rangle>) (sandwich_tc (tensor_ell2_left |c\<rangle>* ) \<rho>)\<close>
          apply (rule eq_from_separatingI2x[where x=\<rho>])
             apply (rule separating_set_bounded_clinear_tc_tensor_nested)
              apply (rule separating_set_tc_butterfly_nested)
               apply (rule separating_set_ket)
              apply (rule separating_set_ket)
             apply (rule separating_set_UNIV)
            apply (intro bounded_linear_intros)
           apply (intro bounded_linear_intros)
          by (auto simp add: sandwich_tc_tensor sandwich_tc_butterfly sandwich_tc_tensor_ell2_left cinner_ket)
        have \<open>E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>) \<ge>
              sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>))
            + sandwich_tc (selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun) (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>))\<close> (is \<open>_ \<ge> \<dots>\<close>)
          by -
        moreover have \<open>\<dots> = E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>) + sandwich_tc (selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun) (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>))\<close>
          apply (rule arg_cong[where f=\<open>\<lambda>x. x + _\<close>])
          using E_readonly[of c]
          by (simp add: E'_def[symmetric] Let_def * )
        ultimately have \<open>sandwich_tc (selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun) (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>)) \<le> 0\<close>
          by fastforce
        moreover have \<open>sandwich_tc (selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun) (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>)) \<ge> 0\<close>
          using \<rho>pos
          by (auto intro!: sandwich_tc_pos kraus_map_pos[OF \<open>kraus_map (E' c)\<close>] simp: )
        ultimately show \<open>sandwich_tc (selfbutter |d\<rangle> \<otimes>\<^sub>o id_cblinfun) (E' c (sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) \<rho>)) = 0\<close>
          by order
      qed *)
      with neq0
      show \<open>False\<close>
        by blast
    qed
    then show \<open>(case cd of (_, (d, _)) \<Rightarrow> d) =
       (case cd of (cuu, du) \<Rightarrow> (case cuu of (cu, u) \<Rightarrow> (case cu of (c, _) \<Rightarrow> \<lambda>_ _. c) u) du)\<close>
      if \<open>cd \<in> kf_domain (meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas))\<close> for cd
      using that by (auto split!: prod.split)
  qed
  also have \<open>\<dots> = kf_apply (\<DD> \<bullet>\<bullet> (\<lambda>(((c,_),_),_). c) `` (\<lambda>(x,_). (x,())) `` (meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)))\<close>
    apply (rule sym)
    by (auto intro!: ext kf_apply_eqI kf_comp_dependent_cong_weak kf_map_twice[THEN kf_eq_trans] 
        simp: bdd\<DD> o_def case_prod_unfold)
  also have \<open>\<dots> = kf_apply (\<DD> \<bullet>\<bullet> (\<lambda>(((c,_),_),_). c) `` (kf_flatten meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)))\<close>
    apply (rule sym)
    by (auto intro!: ext kf_apply_eqI kf_comp_dependent_cong_weak kf_map_cong kf_comp_map_left[THEN kf_eq_trans]
        simp: bdd\<DD>)
  also have \<open>\<dots> = kf_apply (\<DD> \<bullet>\<bullet> (\<lambda>(((c,_),_),_). c) `` (\<lambda>x. (x,())) `` ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas))\<close>
  proof (intro ext kf_apply_eqI kf_comp_dependent_cong_weak kf_map_cong refl kf_eq_weak_reflI kf_eqI_from_filter_eq_weak)
    show \<open>bdd_above ((kf_norm \<circ> \<DD>) ` kf_domain ((\<lambda>(((c, _), _), _). c) `` (kf_flatten meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas))))\<close>
      by (simp add: bdd\<DD>)
    fix tuple :: \<open>((cl \<times> unit) \<times> unit) \<times> unit\<close>
    obtain c where [simp]: \<open>tuple = ((c,()),())\<close>
      by (auto simp: prod_eq_iff)
    from cq_map_id_left[OF \<open>is_cq_map qFst (E' _)\<close>]
    have \<open>km_tensor km_complete_measurement_ket id \<circ> E' d = E' d\<close> for d
      by (simp add: cq_id_qFst)
    then have \<open>kf_apply meas o kf_apply (\<EE> d) = kf_apply (\<EE> d)\<close> for d
      by (simp add: apply\<EE> is_cq_map_def cq_id_qFst meas_def kf_id_apply[abs_def] flip: km_tensor_kf_tensor km_complete_measurement_ket_kf_complete_measurement_ket id_def)
    then have \<open>kf_flatten meas \<bullet> (\<EE> (fst c) \<bullet> kf_filter ((=) c) meas) =\<^sub>k\<^sub>r (\<lambda>x. (x, ())) `` (\<EE> (fst c) \<bullet> kf_filter ((=) c) meas)\<close>
      apply (rule_tac kf_eq_weakI)
      apply (auto simp add: kf_comp_apply o_def)
      by metis
    then show \<open>kf_filter ((=) tuple) (kf_flatten meas \<bullet> ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas)) =\<^sub>k\<^sub>r kf_filter ((=) tuple) ((\<lambda>x. (x, ())) `` ((\<lambda>(c, _). \<EE> c) \<bullet>\<bullet> meas))\<close>
      by (simp add: kf_filter_comp kf_filter_comp_dependent_singleton kf_filter_comp_singleton
          case_prod_unfold bdd\<EE> kf_filter_map)
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
  also have \<open>\<dots> = kf_apply ((\<lambda>(c, _). km_some_kraus_family (D' c \<circ> E' c)) \<bullet>\<bullet> meas)\<close>
    apply (intro ext kf_apply_eqI kf_comp_dependent_cong_weak kf_eq_refl)
    by (simp_all add: apply\<DD> apply\<EE> kf_comp_apply kf_eq_weak_def kraus_map_comp case_prod_unfold bdd\<DD>\<EE>)
  also have \<open>\<dots> = apply_denotation (denotation_cases (\<lambda>c. E c * D c))\<close>
    by (simp add: denotation_cases.rep_eq D'_def E'_def times_denotation.rep_eq meas_def \<DD>_def D'_def \<EE>_def E'_def meas_def)
  finally show \<open>apply_denotation (denotation_cases E * denotation_cases D) = apply_denotation (denotation_cases (\<lambda>c. E c * D c))\<close>
    by -
qed

lemma denotation_while_n_sum:
  \<open>(\<Sum>n\<le>M. denotation_while_n e D n) = (denotation_cases (\<lambda>m. if e m then D else 1))^M * denotation_cases (\<lambda>m. if e m then 0 else 1)\<close>
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
  have c_fst_c: \<open>sandwich_tc (selfbutter |c\<rangle> \<otimes>\<^sub>o id_cblinfun) (cq_id qFst (tc_tensor (tc_butterfly |c\<rangle> |c\<rangle>) \<rho>)) =
           cq_id \<lbrakk>#1\<rbrakk>\<^sub>q (tc_tensor (tc_butterfly |c\<rangle> |c\<rangle>) \<rho>)\<close> for c \<rho>
    apply (simp add: classical_on_def[THEN iffD1])
    apply (transfer' fixing: c)
    by (simp add: sandwich_apply comp_tensor_op tensor_op_adjoint)
  have note_idem: \<open>note * note = note\<close>
    unfolding note_def
    apply (subst denotation_merge)
    by (auto intro!: arg_cong[where f=denotation_cases] bdd_cases
        simp: Let_def one_denotation.rep_eq c_fst_c)
  have eD_note: \<open>note * eD = 0\<close>
    unfolding note_def eD_def
    apply (subst denotation_merge)
       apply (auto intro!: arg_cong[where f=denotation_cases] bdd_cases
        simp: Let_def one_denotation.rep_eq c_fst_c)[3]
    apply (rewrite at \<open>denotation_cases (\<lambda>c. \<hole>)\<close> to 0 DEADID.rel_mono_strong)
    by (auto simp flip: zero_fun_def)
  have \<open>eD1^(Suc M) * note = eD1^M * eD1 * note\<close>
    by (metis power_Suc2)
  also have \<open>\<dots> = eD1^M * (eD + note) * note\<close>
    using eD1_decomp by fastforce
  also have \<open>\<dots> = eD1^M * eD * note + eD1^M * note * note\<close>
    by (simp add: distrib_left distrib_right mult.assoc)
  also have \<open>\<dots> = eD1^M * eD * note + eD1^M * note\<close>
    using note_idem
    by (metis (no_types, lifting) apply_denotation_inject fun.map_comp times_denotation.rep_eq)
  also have \<open>\<dots> = eD1^M * eD * note + (\<Sum>n\<le>M. denotation_while_n e D n)\<close>
    using Suc.IH eD1_def note_def by argo
  also have \<open>\<dots> = denotation_while_n e D (Suc M) + (\<Sum>n\<le>M. denotation_while_n e D n)\<close>
  proof (rule arg_cong[where f=\<open>\<lambda>x. x + _\<close>], induction M)
    case 0
    show ?case
      by (simp add: denotation_while_n_def eD_def note_def)
  next
    case (Suc M)
    have \<open>eD1^(Suc M) * eD * note = eD1 * denotation_while_n e D (Suc M)\<close>
      by (simp add: mult.assoc power_commutes flip: Suc.IH)
    also have \<open>\<dots> = ((eD + note) * eD) * denotation_while_n e D M\<close>
      apply (simp add: denotation_while_n_def flip: eD1_def eD_def eD1_decomp)
      by (metis Groups.mult_ac(1) power_commutes)
    also have \<open>\<dots> = (eD * eD) * denotation_while_n e D M\<close>
      by (simp add: distrib_left distrib_right eD_note flip: mult.assoc)
    also have \<open>\<dots> = denotation_while_n e D (Suc (Suc M))\<close>
      by (simp add: denotation_while_n_def flip: eD_def mult.assoc)
    finally show ?case
      by -
  qed
  also have \<open>\<dots> = (\<Sum>n\<le>Suc M. denotation_while_n e D n)\<close>
    by (simp add: add.commute)
  finally show \<open>\<dots> = eD1^(Suc M) * note\<close>
    by simp
qed


definition denotation_while :: \<open>(cl \<Rightarrow> bool) \<Rightarrow> denotation \<Rightarrow> denotation\<close> where 
  \<open>denotation_while e D = (\<Sum>\<^sub>\<infinity>n. denotation_while_n e D n)\<close>


lemma continuous_on_apply_denotation[continuous_intros]:
  assumes \<open>continuous_on X f\<close>
  shows \<open>continuous_on X (\<lambda>x. apply_denotation (f x))\<close>
proof (rule continuous_on_compose2[OF _ assms])
  show \<open>f ` X \<subseteq> UNIV\<close>
    by simp
  define S where \<open>S = range apply_denotation\<close>
  have S_def': \<open>S = Collect (is_cq_map qFst)\<close>
    using S_def type_definition.Rep_range type_definition_denotation by blast
  have \<open>openin (top_of_set UNIV) (UNIV \<inter> apply_denotation -` U) \<longleftrightarrow> openin (top_of_set S) U\<close> if \<open>U \<subseteq> S\<close> for U
  proof -
    define RU where \<open>RU = apply_denotation -` U\<close>
    have U_def: \<open>U = apply_denotation ` RU\<close>
      using RU_def S_def that type_definition.Rep_range type_definition_denotation by fastforce
    have \<open>openin (top_of_set UNIV) (UNIV \<inter> RU) = open RU\<close>
      by (simp add: openin_subtopology)
    also have \<open>\<dots> = (\<exists>T. open T \<and> U = T \<inter> S)\<close>
      by (simp add: open_denotation_def openin_subtopology S_def' U_def)
    also have \<open>\<dots> = openin (top_of_set S) U\<close>
      by (simp add: openin_subtopology)
    finally show ?thesis
      by (simp add: RU_def)
  qed
  then show \<open>continuous_on UNIV apply_denotation\<close>
    apply (rule_tac quotient_map_imp_continuous_open[where T=S])
    using apply_denotation by (auto simp: S_def)
qed

instance denotation :: pospace
proof (rule pospaceI)
  have \<open>{(x :: denotation, y). y \<le> x} = {(x, y). \<forall>\<rho>\<ge>0. apply_denotation x \<rho> \<le> apply_denotation y \<rho>}\<close>
    by (simp add: less_eq_denotation_def)
  also have \<open>\<dots> = (\<Inter>\<rho>\<in>{0..}. {xy. apply_denotation (fst xy) \<rho> \<le> apply_denotation (snd xy) \<rho>})\<close>
    by auto
  also have \<open>closed \<dots>\<close>
    by (auto intro!: closed_Inter ballI closed_Collect_le continuous_intros intro: continuous_on_product_then_coordinatewise)
  finally show \<open>closed {(x :: denotation, y). y \<le> x}\<close>
    by -
qed

lemma apply_denotation_sum: \<open>apply_denotation (\<Sum>x\<in>A. \<EE> x) = (\<Sum>x\<in>A. apply_denotation (\<EE> x))\<close>
proof (induction A rule:infinite_finite_induct)
  case (infinite A)
  then show ?case
    by simp
next
  case empty
  then show ?case
    by simp
next
  case (insert x F)
  have \<open>apply_denotation (\<Sum>x\<in>insert x F. \<EE> x) = apply_denotation (\<EE> x + (\<Sum>x\<in>F. \<EE> x))\<close>
    by (simp add: insert.hyps)
  also have \<open>\<dots> = apply_denotation (\<EE> x) + apply_denotation (\<Sum>x\<in>F. \<EE> x)\<close>
    by (auto simp: plus_denotation.rep_eq)
  also have \<open>\<dots> = apply_denotation (\<EE> x) + (\<Sum>x\<in>F. apply_denotation (\<EE> x))\<close>
    by (simp add: insert)
  also have \<open>\<dots> = (\<Sum>x\<in>insert x F. apply_denotation (\<EE> x))\<close>
    using insert.hyps by fastforce
  finally show ?case
    by -
qed

lemma tendsto_denotation_apply_denotation:
  \<open>(g \<longlongrightarrow> t) F \<longleftrightarrow> ((\<lambda>x. apply_denotation (g x)) \<longlongrightarrow> apply_denotation t) F\<close>
proof -
  define s f where \<open>s = apply_denotation t\<close> and \<open>f x = apply_denotation (g x)\<close> for x
  define T :: \<open>(((cl \<times> qu) ell2, _) trace_class \<Rightarrow> _) topology\<close>
    where \<open>T = top_of_set (Collect (is_cq_map qFst))\<close>

  have [simp]: \<open>apply_denotation x \<in> apply_denotation ` U \<longleftrightarrow> x \<in> U\<close> for x U
    using apply_denotation_inject by fastforce
  have [iff]: \<open>apply_denotation t \<in> topspace T\<close>
    using T_def apply_denotation by force
  have app_den_cq_map: \<open>V \<in> range (image apply_denotation) \<longleftrightarrow> V \<subseteq> Collect (is_cq_map qFst)\<close> for V
    apply (simp add: in_range_image_iff flip: Ball_Collect)
    by (smt (verit, ccfv_threshold) Abs_denotation_inverse apply_denotation imageE mem_Collect_eq rangeI subsetI
        subset_image_iff)
  have \<open>(g \<longlongrightarrow> t) F \<longleftrightarrow> (\<forall>U. open U \<longrightarrow> t \<in> U \<longrightarrow> (\<forall>\<^sub>F x in F. g x \<in> U))\<close>
    by (simp add: limitin_def flip: limitin_canonical_iff)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>U. openin T (apply_denotation ` U) \<longrightarrow> t \<in> U \<longrightarrow> (\<forall>\<^sub>F x in F. g x \<in> U))\<close>
    using T_def open_denotation.rep_eq by presburger
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>U. openin T (apply_denotation ` U) \<longrightarrow> s \<in> apply_denotation ` U \<longrightarrow> (\<forall>\<^sub>F x in F. f x \<in> apply_denotation ` U))\<close>
    by (simp add: f_def s_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>V\<in>range (image apply_denotation). openin T V \<longrightarrow> s \<in> V \<longrightarrow> (\<forall>\<^sub>F x in F. f x \<in> V))\<close>
    by blast
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>V\<subseteq>Collect (is_cq_map qFst). openin T V \<longrightarrow> s \<in> V \<longrightarrow> (\<forall>\<^sub>F x in F. f x \<in> V))\<close>
    by (simp add: app_den_cq_map Ball_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>V. openin T V \<longrightarrow> s \<in> V \<longrightarrow> (\<forall>\<^sub>F x in F. f x \<in> V))\<close>
    apply (rule all_cong1)
    by (auto simp: T_def openin_open)
  also have \<open>\<dots> \<longleftrightarrow> limitin T f s F\<close>
    by (simp add: limitin_def s_def)
  also have \<open>\<dots> \<longleftrightarrow> (f \<longlongrightarrow> s) F\<close>
    using apply_denotation by (simp add: T_def limitin_subtopology s_def f_def)
  finally show \<open>(g \<longlongrightarrow> t) F \<longleftrightarrow> (f \<longlongrightarrow> s) F\<close>
    by -
qed

lemma tendsto_denotation_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>(((=) ===> cr_denotation) ===> cr_denotation ===> (=) ===> (\<longleftrightarrow>))
           tendsto tendsto\<close>
proof (intro rel_funI, rename_tac f g s t F G)
  fix g :: \<open>'c \<Rightarrow> denotation\<close> and f s t and F G :: \<open>'c filter\<close>
  assume \<open>((=) ===> cr_denotation) f g\<close> and st: \<open>cr_denotation s t\<close> and [symmetric, simp]: \<open>F = G\<close>
  then have fg: \<open>cr_denotation (f x) (g x)\<close> for x
    by (simp add: rel_fun_def)
  from st have st': \<open>s = apply_denotation t\<close>
    by (meson cr_denotation_def)
  from fg have fg': \<open>f x = apply_denotation (g x)\<close> for x
    by (simp add: cr_denotation_def)
  show \<open>(f \<longlongrightarrow> s) F \<longleftrightarrow> (g \<longlongrightarrow> t) G\<close>
    by (simp add: st' fg'[abs_def] tendsto_denotation_apply_denotation)
qed

lemma has_sum_denotation_apply_denotation:
  \<open>(g has_sum t) A \<longleftrightarrow> ((\<lambda>x. apply_denotation (g x)) has_sum apply_denotation t) A\<close>
proof -
  have \<open>(g has_sum t) A \<longleftrightarrow> (sum g \<longlongrightarrow> t) (finite_subsets_at_top A)\<close>
    by (simp add: has_sum_def)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>F. apply_denotation (\<Sum>x\<in>F. g x)) \<longlongrightarrow> apply_denotation t) (finite_subsets_at_top A)\<close>
    by (simp add: tendsto_denotation_apply_denotation)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>F. \<Sum>x\<in>F. apply_denotation (g x)) \<longlongrightarrow> apply_denotation t) (finite_subsets_at_top A)\<close>
    by (simp add: apply_denotation_sum)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>x. apply_denotation (g x)) has_sum apply_denotation t) A\<close>
    by (simp add: has_sum_def)
  finally show ?thesis
    by -
qed

lemma has_sum_denotation_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>(((=) ===> cr_denotation) ===> (=) ===> cr_denotation ===> (\<longleftrightarrow>)) HAS_SUM HAS_SUM\<close>
proof (intro rel_funI, rename_tac f g A B s t)
  fix g :: \<open>'a \<Rightarrow> denotation\<close> and f s t and A B :: \<open>'a set\<close>
  assume \<open>((=) ===> cr_denotation) f g\<close> and st: \<open>cr_denotation s t\<close> and [symmetric, simp]: \<open>A = B\<close>
  then have fg: \<open>cr_denotation (f x) (g x)\<close> for x
    by (simp add: rel_fun_def)
  from st have st': \<open>s = apply_denotation t\<close>
    by (meson cr_denotation_def)
  from fg have fg': \<open>f x = apply_denotation (g x)\<close> for x
    by (simp add: cr_denotation_def)
  show \<open>(f has_sum s) A \<longleftrightarrow> (g has_sum t) B\<close>
    by (simp add: st' fg'[abs_def] has_sum_denotation_apply_denotation)
qed

lemma summable_on_denotation_apply_denotation:
  \<open>g summable_on A \<longleftrightarrow> km_summable (\<lambda>x. apply_denotation (g x)) A\<close>
proof (rule iffI)
  assume \<open>g summable_on A\<close>
  then obtain s where \<open>(g has_sum s) A\<close>
    using summable_on_def by blast
  define g' s' where \<open>g' x = apply_denotation (g x)\<close> and \<open>s' = apply_denotation s\<close> for x
  from \<open>(g has_sum s) A\<close>
  have \<open>(g' has_sum s') A\<close>
    by (simp add: has_sum_denotation_apply_denotation g'_def[abs_def] s'_def)
  moreover have \<open>kraus_map s'\<close>
    using apply_denotation is_cq_map_def s'_def by blast
  ultimately show \<open>km_summable g' A\<close>
    by (metis g'_def apply_denotation has_sum_coordinatewise is_cq_map_def km_summable_iff_sums_to_kraus_map
        mem_Collect_eq)
next
  define g' where \<open>g' x = apply_denotation (g x)\<close> for x
  then have km_g': \<open>kraus_map (g' x)\<close> for x
    using apply_denotation is_cq_map_def by force
  assume asm: \<open>km_summable g' A\<close>
  then obtain s' where \<open>((\<lambda>x. g' x t) has_sum s' t) A\<close> and \<open>kraus_map s'\<close> for t
    apply (subst (asm) km_summable_iff_sums_to_kraus_map[OF km_g'])
    by fastforce
  then have sum_s: \<open>(g' has_sum s') A\<close>
    by (simp add: has_sum_coordinatewise)
  then obtain s' where sum_s: \<open>(g' has_sum s') A\<close>
    using summable_on_def by blast
  then have \<open>is_cq_map qFst s'\<close>
    apply (rule is_cq_map_has_sum[rotated 2])
    using apply_denotation asm g'_def[abs_def] asm by auto
  then obtain s where \<open>s' = apply_denotation s\<close>
    using apply_denotation_cases by blast
  with sum_s have \<open>(g' has_sum apply_denotation s) A\<close>
    by simp
  then have \<open>(g has_sum s) A\<close>
    by (simp add: g'_def[abs_def] has_sum_denotation_apply_denotation)
  then show \<open>g summable_on A\<close>
    by (simp add: has_sum_imp_summable)
qed


lemma summable_on_denotation_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>(((=) ===> cr_denotation) ===> (=) ===> (\<longleftrightarrow>)) (\<lambda>g A. km_summable g A) Infinite_Sum.summable_on\<close>
  apply (simp add: summable_on_denotation_apply_denotation[abs_def])
  by transfer_prover

lemma
  assumes \<open>denotation_norm D \<le> 1\<close>
  shows denotation_while_bounded[iff]: \<open>denotation_norm (denotation_while e D) \<le> 1\<close>
    and denotation_while_has_sum: \<open>(denotation_while_n e D has_sum denotation_while e D) UNIV\<close>
proof -
  define W where \<open>W = denotation_while_n e D\<close>
  have rewrite_Wsum: \<open>(\<Sum>n\<le>M. W n) = (denotation_cases (\<lambda>m. if e m then D else 1))^M * (denotation_cases (\<lambda>m. if e m then 0 else 1))\<close> for M
    by (simp add: W_def denotation_while_n_sum)
  have finsum: \<open>(\<Sum>n\<in>F. km_bound (apply_denotation (W n))) \<le> id_cblinfun\<close> if \<open>finite F\<close> for F
  proof -
    define N where \<open>N = Max F\<close>
    have \<open>(\<Sum>n\<in>F. km_bound (apply_denotation (W n))) \<le> (\<Sum>n\<le>N. km_bound (apply_denotation (W n)))\<close>
      using that by (auto intro!: sum_mono2 simp: N_def)
    also have \<open>\<dots> = km_bound (\<Sum>n\<le>N. apply_denotation (W n))\<close>
      apply (rule km_bound_sum[symmetric])
      using apply_denotation is_cq_map_def by blast
    also have \<open>\<dots> = km_bound (apply_denotation (\<Sum>n\<le>N. W n))\<close>
      by (simp add: apply_denotation_sum)
    also have \<open>\<dots> = km_bound (apply_denotation (denotation_cases (\<lambda>m. if e m then D else 1) ^ N * denotation_cases (\<lambda>m. if e m then 0 else 1)))\<close>
      by (simp add: rewrite_Wsum)
    also have \<open>\<dots> \<le> denotation_norm (denotation_cases (\<lambda>m. if e m then D else 1) ^ N * denotation_cases (\<lambda>m. if e m then 0 else 1)) *\<^sub>R id_cblinfun\<close>
      by (simp add: denotation_norm.rep_eq km_bound_leq_km_norm_id)
    also have \<open>\<dots> \<le> 1 *\<^sub>R id_cblinfun\<close> (is \<open>denotation_norm (?x^N * ?y) *\<^sub>R id_cblinfun \<le> _\<close>)
      apply (rule scaleR_right_mono)
      by (auto intro!: times_denotation_bounded[THEN order_trans] mult_le_one power_le_one
          power_denotation_bounded[THEN order_trans] denotation_cases_bounded assms)
    also have \<open>\<dots> = id_cblinfun\<close>
      by simp
    finally show ?thesis
      by -
  qed
  then have \<open>summable_on_in cweak_operator_topology (\<lambda>n. km_bound (apply_denotation (W n))) UNIV\<close>
    apply (rule summable_wot_boundedI)
    by auto
  then have km_summable: \<open>km_summable (\<lambda>n. apply_denotation (W n)) UNIV\<close>
    by (simp add: km_summable_def)
  then have \<open>kraus_map (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>n. apply_denotation (W n) \<rho>)\<close>
    apply (rule kraus_map_infsum[rotated])
    using apply_denotation is_cq_map_def by blast
  have \<open>infsum_in cweak_operator_topology (\<lambda>n. km_bound (apply_denotation (W n))) UNIV \<le> id_cblinfun\<close>
    by (simp add: finsum infsum_wot_boundedI)
  then have km_bound: \<open>km_bound (\<lambda>\<rho>. \<Sum>\<^sub>\<infinity>n. apply_denotation (W n) \<rho>) \<le> id_cblinfun\<close>
    apply (subst km_bound_infsum)
    using apply_denotation km_summable by (auto intro!: simp: is_cq_map_def)
  have \<open>W summable_on UNIV\<close>
    by (simp add: summable_on_denotation_apply_denotation km_summable flip: W_def)
  then show \<open>(W has_sum denotation_while e D) UNIV\<close>
    by (simp add: denotation_while_def W_def)
  then have \<open>((\<lambda>n. apply_denotation (W n) \<rho>) has_sum apply_denotation (denotation_while e D) \<rho>) UNIV\<close> for \<rho>
    by (simp add: has_sum_denotation_apply_denotation has_sum_coordinatewise)
  then have while_infsum: \<open>apply_denotation (denotation_while e D) \<rho> = (\<Sum>\<^sub>\<infinity>n. apply_denotation (W n) \<rho>)\<close> for \<rho>
    by (metis infsumI)
  show \<open>denotation_norm (denotation_while e D) \<le> 1\<close>
    using norm_cblinfun_mono[OF _ km_bound]
    by (simp_all add: denotation_norm.rep_eq km_norm_def while_infsum[abs_def])
qed

definition denotation_from_quantum :: \<open>(cl \<Rightarrow> (qu ell2, qu ell2) trace_class \<Rightarrow> (qu ell2, qu ell2) trace_class) \<Rightarrow> denotation\<close> where
  \<open>denotation_from_quantum q = denotation_cases (\<lambda>c. Abs_denotation (km_tensor km_complete_measurement_ket (q c)))\<close>

lemma denotation_from_quantum_bounded[iff]:
  assumes \<open>\<And>c. kraus_map (q c)\<close>
  assumes \<open>\<And>c. km_norm (q c) \<le> 1\<close>
  shows \<open>denotation_norm (denotation_from_quantum q) \<le> 1\<close>
  unfolding denotation_from_quantum_def
  apply (rule denotation_cases_bounded)
  by (simp add: eq_onp_def is_cq_map_qFst assms denotation_norm.abs_eq km_norm_tensor)

lift_definition denotation_from_classical :: \<open>(cl \<Rightarrow> cl) \<Rightarrow> denotation\<close> is
  \<open>\<lambda>f. cq_map_from_kraus_family qFst qSnd (\<lambda>c. kf_map_inj (\<lambda>_. f c) kf_id)\<close>
  by (rule cq_map_from_kraus_family_is_cq_map)

lemma denotation_from_classical_eq_sample: \<open>denotation_from_classical f = denotation_sample (\<lambda>c. point_distr (f c))\<close>
proof  -
  have 1: \<open>(id_cblinfun, d) \<in> range (\<lambda>x. (sqrt (of_bool (x = d)) *\<^sub>R id_cblinfun, x))\<close> for d :: cl
  by auto
  have 2: \<open>(\<lambda>m. of_bool (m = d)) summable_on UNIV\<close> for d :: cl
    apply (subst summable_on_cong_neutral[OF _ _ refl, where T=\<open>{d}\<close>])
    by auto
  have 3: \<open>kf_map_inj (\<lambda>_. d) kf_id = kf_sample (prob (point_distr d))\<close> for d :: cl
    apply (simp add: kf_id_def del: kf_of_op_id)
    apply (transfer' fixing: d)
    by (auto intro!: simp: 1 2)
  show ?thesis
    apply (transfer' fixing: f)
    by (simp add: 3)
qed

end
