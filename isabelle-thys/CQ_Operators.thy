theory CQ_Operators
  imports Kraus_Maps.Kraus_Maps Registers2.Missing_Bounded_Operators Registers2.Quantum_Registers
    Registers2.Registers_Unsorted Registers.Laws_Complement_Classical
    Kraus_Registers
begin

unbundle kraus_map_syntax

definition cq_id :: \<open>('c,'a) qregister \<Rightarrow> (('a ell2, 'a ell2) trace_class \<Rightarrow> ('a ell2, 'a ell2) trace_class)\<close> where
  \<open>cq_id C = km_apply_qregister C (km_complete_measurement (range ket))\<close>

definition classical_on :: \<open>('c,'a) qregister \<Rightarrow> ('a ell2, 'a ell2) trace_class \<Rightarrow> bool\<close> where
  \<open>classical_on C \<rho> \<longleftrightarrow> cq_id C \<rho> = \<rho>\<close>

definition cq_operator_reconstruct :: \<open>('c\<times>'q, 'r) qregister \<Rightarrow> ('c \<Rightarrow> ('q ell2, 'q ell2) trace_class) \<Rightarrow> ('r ell2, 'r ell2) trace_class\<close> where
  \<open>cq_operator_reconstruct Q \<rho> = (\<Sum>\<^sub>\<infinity>c. apply_qregister_tc Q (tc_tensor (tc_butterfly (ket c) (ket c)) (\<rho> c)))\<close>

definition cq_operator_at :: \<open>('c\<times>'q, 'r) qregister \<Rightarrow> ('r ell2, 'r ell2) trace_class \<Rightarrow> 'c \<Rightarrow> ('q ell2, 'q ell2) trace_class\<close> where
  \<open>cq_operator_at Q \<rho> c = sandwich_tc (tensor_ell2_left (ket c)*) (apply_qregister_tc (qregister_inv Q) \<rho>)\<close>

lemma cq_operator_at_summable:
  fixes \<rho> :: \<open>(('c\<times>'q) ell2, ('c\<times>'q) ell2) trace_class\<close> and c :: 'c
  shows \<open>cq_operator_at Q \<rho> abs_summable_on UNIV\<close>
  using partial_trace_abs_summable'[of \<open>sandwich_tc swap_ell2 (apply_qregister_tc (qregister_inv Q) \<rho>)\<close>]
  by (simp add: cq_operator_at_def sandwich_tc_compose[symmetric, unfolded o_def, THEN fun_cong])

lemma cq_operator_at_bounded_clinear[bounded_clinear]:
  assumes \<open>iso_qregister Q\<close>
  shows \<open>bounded_clinear (\<lambda>\<rho>. cq_operator_at Q \<rho> c)\<close>
proof -
  have 1: \<open>cq_operator_at Q (\<rho> + y) c = cq_operator_at Q \<rho> c + cq_operator_at Q y c\<close> for \<rho> y :: \<open>('c ell2, 'c ell2) trace_class\<close>
    by (simp add: sandwich_tc_plus cq_operator_at_def apply_qregister_tc_plus)
  have 2: \<open>cq_operator_at Q (r *\<^sub>C \<rho>) c = r *\<^sub>C cq_operator_at Q \<rho> c\<close> for \<rho> :: \<open>('c ell2, 'c ell2) trace_class\<close> and r
    by (simp add: cq_operator_at_def sandwich_tc_scaleC_right apply_qregister_tc_scale)
  have 3: \<open>norm (cq_operator_at Q \<rho> c) \<le> norm \<rho> * 1\<close> for \<rho> :: \<open>('c ell2, 'c ell2) trace_class\<close>
    using norm_sandwich_tc[of \<open>tensor_ell2_left (ket c)*\<close> \<open>apply_qregister_tc (qregister_inv Q) \<rho>\<close>]
    by (simp add: cq_operator_at_def apply_iso_qregister_tc_norm assms iso_qregister_inv_iso)
  from 1 2 3
  show ?thesis
    by (rule bounded_clinearI)
qed


lemma cq_operator_reconstruct_inv:
  fixes \<rho> :: \<open>'c \<Rightarrow> ('q ell2, 'q ell2) trace_class\<close>
  assumes sum_\<rho>: \<open>\<rho> abs_summable_on UNIV\<close>
  assumes \<open>iso_qregister Q\<close>
  shows \<open>cq_operator_at Q (cq_operator_reconstruct Q \<rho>) = \<rho>\<close>
proof (rule ext)
  fix c :: 'c
  define q q1 where \<open>q = apply_qregister_tc Q\<close> and \<open>q1 = apply_qregister_tc (qregister_inv Q)\<close>
  have [simp]: \<open>q1 (q t) = t\<close> for t
    unfolding q1_def q_def 
    apply (subst qregister_chain_apply_tc[symmetric, unfolded o_def, THEN fun_cong])
    using assms by (auto simp add: iso_qregister_inv_iso iso_qregister_inv_chain) 
  have \<open>bounded_linear q\<close>
    by (simp add: q_def assms bounded_clinear.bounded_linear bounded_clinear_apply_qregister_tc)

  have *: \<open>cq_operator_at Q (q (tc_tensor (tc_butterfly (ket d) (ket d)) (\<rho> d))) c = of_bool (c=d) *\<^sub>C \<rho> d\<close> for d
    apply (rule from_trace_class_inject[THEN iffD1])
    by (simp add: cq_operator_at_def from_trace_class_sandwich_tc tc_tensor.rep_eq tc_butterfly.rep_eq sandwich_tensor_ell2_left
        flip: q1_def)
  have summable1: \<open>(\<lambda>c. tc_tensor (tc_butterfly (ket c) (ket c)) (\<rho> c)) summable_on UNIV\<close>
    by (simp add: abs_summable_summable assms norm_tc_butterfly norm_tc_tensor)
  then have summable2: \<open>(\<lambda>d. q (tc_tensor (tc_butterfly (ket d) (ket d)) (\<rho> d))) summable_on UNIV\<close>
    by (simp add: abs_summable_summable apply_iso_qregister_tc_norm assms(1,2) norm_tc_butterfly norm_tc_tensor q_def)
  have \<open>cq_operator_at Q (cq_operator_reconstruct Q \<rho>) c
     = cq_operator_at Q (\<Sum>\<^sub>\<infinity>c. q (tc_tensor (tc_butterfly (ket c) (ket c)) (\<rho> c))) c\<close>
    by (simp add: cq_operator_reconstruct_def q_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. cq_operator_at Q (q (tc_tensor (tc_butterfly (ket d) (ket d)) (\<rho> d))) c)\<close>
    apply (subst infsum_bounded_linear[where h=\<open>\<lambda>\<rho>. cq_operator_at Q \<rho> c\<close>])
      apply (simp add: bounded_clinear.bounded_linear cq_operator_at_bounded_clinear assms) 
     apply (rule summable2)
    by simp
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d::'c. of_bool (c = d) *\<^sub>C \<rho> d)\<close>
    by (simp add: * )
  also have \<open>\<dots> = \<rho> c\<close>
    apply (subst infsum_single[where i=c])
    by auto
  finally show \<open>cq_operator_at Q (cq_operator_reconstruct Q \<rho>) c = \<rho> c\<close>
    by -
qed

lemma cq_operator_reconstruct:
  fixes \<rho> :: \<open>('r ell2, 'r ell2) trace_class\<close>
    and C :: \<open>('c, 'r) qregister\<close>
    and Q :: \<open>('q, 'r) qregister\<close>
  assumes \<open>qcomplements C Q\<close>
  assumes cq: \<open>classical_on C \<rho>\<close>
  defines \<open>CQ \<equiv> \<lbrakk>C,Q\<rbrakk>\<^sub>q\<close>
  shows \<open>cq_operator_reconstruct CQ (cq_operator_at CQ \<rho>) = \<rho>\<close>
proof -
  have [iff]: \<open>iso_qregister CQ\<close>
    using assms(1,3) qcomplements_def' by blast
  then have [iff]: \<open>qregister CQ\<close>
    using iso_qregister_def' by blast
  define cq cq1 where \<open>cq = apply_qregister_tc CQ\<close> and \<open>cq1 = apply_qregister_tc (qregister_inv CQ)\<close>
  have [simp]: \<open>cq1 (cq t) = t\<close> for t
    unfolding cq1_def cq_def 
    apply (subst qregister_chain_apply_tc[symmetric, unfolded o_def, THEN fun_cong])
    by (auto simp add: iso_qregister_inv_iso iso_qregister_inv_chain) 
  have [iff]: \<open>bounded_linear cq\<close>
    by (simp add: cq_def bounded_clinear.bounded_linear bounded_clinear_apply_qregister_tc)
  have [iff]: \<open>bounded_linear cq1\<close>
    by (simp add: cq1_def bounded_clinear.bounded_linear bounded_clinear_apply_qregister_tc iso_qregister_inv_iso)
  define f :: \<open>('c \<times> 'q) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'q) ell2 \<Rightarrow> 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close>
    where \<open>f = inv (\<lambda>E. E \<otimes>\<^sub>o id_cblinfun)\<close>
  have [simp]: \<open>f (E \<otimes>\<^sub>o id_cblinfun) = E\<close> for E :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close>
    unfolding f_def
    apply (subst inv_f_f)
    by (auto intro!: inj_tensor_left)
  have \<open>cq_operator_reconstruct CQ (cq_operator_at CQ \<rho>)
        = (\<Sum>\<^sub>\<infinity>c. cq (tc_tensor (tc_butterfly (ket c) (ket c)) (sandwich_tc (tensor_ell2_left (ket c)*) (cq1 \<rho>))))\<close>
    by (simp add: cq_def cq1_def cq_operator_reconstruct_def cq_operator_at_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>c. cq (sandwich_tc (selfbutter (ket c) \<otimes>\<^sub>o id_cblinfun) (cq1 \<rho>)))\<close>
    (is \<open>(\<Sum>\<^sub>\<infinity>c. ?lhs c) = (\<Sum>\<^sub>\<infinity>c. ?rhs c)\<close>)
  proof (rule infsum_cong)
    fix c
    show \<open>?lhs c = ?rhs c\<close>
    proof -
      have *: \<open>sandwich_tc (selfbutter (ket c) \<otimes>\<^sub>o id_cblinfun) (tc_tensor x (tc_butterfly a b)) =
       tc_tensor (tc_butterfly (ket c) (ket c)) (sandwich_tc (tensor_ell2_left (ket c)*) (tc_tensor x (tc_butterfly a b)))\<close>
        for x :: \<open>('c ell2, 'c ell2) trace_class\<close> and a b :: \<open>'e ell2\<close>
        apply (rule from_trace_class_inject[THEN iffD1])
        apply (simp add: from_trace_class_sandwich_tc tc_tensor.rep_eq tc_butterfly.rep_eq sandwich_tensor_ell2_left)
        by (simp add: sandwich_apply tensor_op_adjoint comp_tensor_op butterfly_comp_cblinfun cinner_adj_left tensor_op_cbilinear.scaleC_left tensor_op_cbilinear.scaleC_right)
      have \<open>sandwich_tc (selfbutter (ket c) \<otimes>\<^sub>o id_cblinfun) = (\<lambda>\<rho>. tc_tensor (tc_butterfly (ket c) (ket c)) (sandwich_tc (tensor_ell2_left (ket c)*) \<rho>))\<close>
        apply (rule eq_from_separatingI2)
           apply (rule separating_set_bounded_clinear_tc_tensor_nested)
            apply (rule separating_set_UNIV)
           apply (rule separating_set_tc_butterfly)
        using bounded_clinear_sandwich_tc apply blast
        using bounded_clinear_compose bounded_clinear_sandwich_tc bounded_clinear_tc_tensor_right apply blast 
        using * by auto
      then show ?thesis
        by metis
    qed
  qed
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>range (\<lambda>x::'c. ((selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun), ket x)). cq (sandwich_tc (fst E) (cq1 \<rho>)))\<close>
    apply (subst infsum_reindex)
    by (simp_all add: inj_def o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((E, x), F, y)\<in>range (\<lambda>x. (selfbutter (ket x), ket x)) \<times> {(id_cblinfun, ())}. cq (sandwich_tc (E \<otimes>\<^sub>o F) (cq1 \<rho>)))\<close>
    apply (subst infsum_reindex_bij_betw[where A=\<open>range (\<lambda>x. (selfbutter (ket x), ket x)) \<times> {(id_cblinfun, ())}\<close>
          and g=\<open>\<lambda>((E,x),(F,y)). (E \<otimes>\<^sub>o F, x)\<close>, symmetric])
     apply (rule bij_betw_byWitness[where f'=\<open>\<lambda>(Eid,x). ((f Eid,x),(id_cblinfun,()))\<close>])
        apply auto[4]
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> = cq (\<Sum>\<^sub>\<infinity>((E, x), F, y)\<in>range (\<lambda>x. (selfbutter (ket x), ket x)) \<times> {(id_cblinfun, ())}. sandwich_tc (E \<otimes>\<^sub>o F) (cq1 \<rho>))\<close>
    apply (subst infsum_bounded_linear_invertible[where h=cq and h'=cq1, symmetric])
    by (auto simp: case_prod_unfold)
  also have \<open>\<dots> = cq (kf_tensor (kf_complete_measurement (range ket)) kf_id *\<^sub>k\<^sub>r (cq1 \<rho>))\<close>
    apply (simp only: kf_apply_tensor_as_infsum kf_id_def kf_of_op.rep_eq kf_complete_measurement.rep_eq)
    by (simp add: image_image)
  also have \<open>\<dots> = kf_apply_qregister CQ (kf_tensor (kf_complete_measurement (range ket)) kf_id) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kf_apply_qregister_iso_qregister_explicit cq_def cq1_def)
  also have \<open>\<dots> = kf_apply_qregister C (kf_complete_measurement (range ket)) *\<^sub>k\<^sub>r \<rho>\<close>
    using \<open>qregister CQ\<close> by (auto intro!: kf_apply_eqI kf_apply_qregister_pair_tensor_id_weak simp: CQ_def)
  also have \<open>\<dots> = km_apply_qregister C (km_complete_measurement (range ket)) \<rho>\<close>
    by (metis (no_types, lifting) ext CQ_def Missing_Bounded_Operators.is_ortho_set_ket \<open>iso_qregister CQ\<close> distinct_qvarsL
      iso_qregister_def' kf_complete_measurement_apply km_apply_qregister_kf_apply km_complete_measurement_def) 
  also have \<open>\<dots> = \<rho>\<close>
    using cq unfolding classical_on_def cq_id_def by blast
  finally show ?thesis
    by -
qed

definition is_cq_map :: \<open>('c, 'r) qregister \<Rightarrow> (('r ell2, 'r ell2) trace_class \<Rightarrow> ('r ell2, 'r ell2) trace_class) \<Rightarrow> bool\<close> where
  \<open>is_cq_map C \<EE> \<longleftrightarrow> kraus_map \<EE> \<and> cq_id C o \<EE> o cq_id C = \<EE>\<close>

lemma cq_id_invalid[simp]: \<open>cq_id non_qregister = 0\<close>
  by (simp add: cq_id_def km_apply_qregister_invalid_Q)

(* (* TODO same for km_ *)
lemma kf_bound_apply_qregister:
  \<comment> \<open>I believe this is an equality. But the proof is not obvious.\<close>
   \<open>kf_bound (kf_apply_qregister Q \<EE>) \<le> apply_qregister Q (kf_bound \<EE>)\<close>
proof -
  wlog [iff]: \<open>qregister Q\<close>
    using negation
    by (simp add: non_qregister)
  have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> apply_qregister Q (kf_bound \<EE>)\<close>
    if \<open>finite F\<close> and \<open>F \<subseteq> Rep_kraus_family (kf_apply_qregister Q \<EE>)\<close> for F
  proof -
    from that
    obtain G where FG: \<open>F = (\<lambda>(E, y). (apply_qregister Q E, y)) ` G\<close> and \<open>finite G\<close> and \<open>G \<subseteq> Rep_kraus_family \<EE>\<close>
      apply (simp add: kf_apply_qregister.rep_eq)
      by (meson finite_subset_image)
    have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) = (\<Sum>(E, x)\<in>(\<lambda>(E, y). (apply_qregister Q E, y)) ` G. E* o\<^sub>C\<^sub>L E)\<close>
      using FG by force
    also have \<open>\<dots> = (\<Sum>(E, x)\<in>G. apply_qregister Q (E* o\<^sub>C\<^sub>L E))\<close>
      apply (subst sum.reindex)
      by (auto intro!: inj_onI simp: case_prod_unfold qregister_compose apply_qregister_adj apply_qregister_inject')
    also have \<open>\<dots> = apply_qregister Q (\<Sum>(E, x)\<in>G. E* o\<^sub>C\<^sub>L E)\<close>
      apply (subst complex_vector.linear_sum[where f=\<open>apply_qregister Q\<close>]) 
      by (simp_all add: case_prod_beta)
    also have \<open>\<dots> \<le> apply_qregister Q (kf_bound \<EE>)\<close>
      using \<open>qregister Q\<close> apply (rule apply_qregister_mono[THEN iffD2])
      using \<open>G \<subseteq> Rep_kraus_family \<EE>\<close> by (rule kf_bound_geq_sum)
    finally show ?thesis
      by -
  qed
  then show \<open>kf_bound (kf_apply_qregister Q \<EE>) \<le> apply_qregister Q (kf_bound \<EE>)\<close>
    using kf_bound_leqI by blast
qed *)


lemma cq_id_idem[simp]: \<open>cq_id C (cq_id C t) = cq_id C t\<close>
proof -
  wlog \<open>qregister C\<close>
    using negation by (simp add: cq_id_invalid non_qregister)
  have \<open>cq_id C (cq_id C t) = km_apply_qregister C (km_complete_measurement (range ket) \<circ> km_complete_measurement (range ket)) t\<close>
    by (simp add: cq_id_def km_apply_qregister_comp kraus_map_complete_measurement)
  also have \<open>\<dots> = km_apply_qregister C (km_complete_measurement (range ket)) t\<close>
    by (simp add: comp_def)
  also have \<open>\<dots> = cq_id C t\<close>
    by (simp add: cq_id_def)
  finally show ?thesis
    by -
qed


lemma kraus_map_cq_id[iff]: \<open>kraus_map (cq_id C)\<close>
  apply (cases \<open>qregister C\<close>)
   apply (simp add: cq_id_def km_apply_qregister_def) 
  by (simp add: cq_id_invalid non_qregister)

lemma is_cq_map_id[iff]: \<open>is_cq_map C (cq_id C)\<close>
  by (auto simp: is_cq_map_def)

lemma cq_id_0[simp]: \<open>cq_id Q 0 = 0\<close>
  by (intro complex_vector.linear_0 bounded_clinear.clinear kraus_map_bounded_clinear kraus_map_cq_id)

lemma is_cq_map_0[iff]: \<open>is_cq_map Q 0\<close>
  by (auto intro!: ext simp add: is_cq_map_def o_def)


lemma bounded_clinear_cq_id[bounded_clinear, iff]: \<open>bounded_clinear (cq_id C)\<close>
  by (simp add: kraus_map_bounded_clinear)

definition cq_prob :: \<open>('c,'r) qregister \<Rightarrow> ('r ell2, 'r ell2) trace_class \<Rightarrow> 'c \<Rightarrow> real\<close> where
  \<open>cq_prob C \<rho> c = norm (sandwich_tc (apply_qregister C (selfbutter (ket c))) \<rho>)\<close>

lemma km_bound_cq_id[simp]:
  assumes \<open>qregister C\<close>
  shows \<open>km_bound (cq_id C) = id_cblinfun\<close>
  by (simp add: cq_id_def km_bound_apply_qregister assms kraus_map_complete_measurement)


lemma km_norm_cq_id[simp]:
  assumes \<open>qregister C\<close>
  shows \<open>km_norm (cq_id C) = 1\<close>
  by (simp add: km_norm_def assms)

no_notation bottom (\<open>\<bottom>\<index>\<close>)

(* lemma one_dim_swap_ell2_id[simp]: \<open>(swap_ell2 :: (('a :: CARD_1) \<times> 'a) ell2 \<Rightarrow>\<^sub>C\<^sub>L _) = id_cblinfun\<close>
  apply (rule equal_ket)
  by fastforce *)



thm ACTUAL_QREGISTER_bot

(* lemma unitary_norm_leq1:
  assumes \<open>unitary U\<close>
  shows \<open>norm U \<le> 1\<close>
  using assms norm_partial_isometry unitary_partial_isometry by fastforce *)



(* 
definition km_local_register :: 
  \<open>'a QREGISTER \<Rightarrow> ('a ell2, 'a ell2) trace_class \<Rightarrow> (('a ell2, 'a ell2) trace_class \<Rightarrow> ('a ell2, 'a ell2) trace_class) \<Rightarrow> (('a ell2, 'a ell2) trace_class \<Rightarrow> ('a ell2, 'a ell2) trace_class)\<close> where
  \<open>km_local_register Q \<rho> \<EE> = kf_apply (kf_local_register Q \<rho> (km_some_kraus_family \<EE>))\<close> *)

lemma cq_map_id_right:
  assumes \<open>is_cq_map C \<EE>\<close>
  shows \<open>\<EE> o cq_id C = \<EE>\<close>
  apply (subst (2) assms[unfolded is_cq_map_def, THEN conjunct2, symmetric])
  apply (subst assms[unfolded is_cq_map_def, THEN conjunct2, symmetric])
  by auto

lemma cq_map_id_left:
  assumes \<open>is_cq_map C \<EE>\<close>
  shows \<open>cq_id C o \<EE> = \<EE>\<close>
  apply (subst (2) assms[unfolded is_cq_map_def, THEN conjunct2, symmetric])
  apply (subst assms[unfolded is_cq_map_def, THEN conjunct2, symmetric])
  by auto

lemma km_operators_in_cq_id:
  shows \<open>km_operators_in (cq_id C) (apply_qregister C ` span (selfbutter ` range ket))\<close>
  apply (rule_tac km_operators_in_mono[rotated])
  unfolding cq_id_def
   apply (rule km_operators_in_km_apply_qregister)
   apply (rule km_operators_complete_measurement)
  by simp_all

lemma is_cq_map_km_local_register_quantum:
  assumes \<open>Qqcompatible Q C\<close>
  assumes \<open>ACTUAL_QREGISTER Q\<close>
  assumes \<open>\<rho> \<ge> 0\<close>
  assumes \<open>is_cq_map C \<EE>\<close>
  shows \<open>is_cq_map C (km_local_register Q \<rho> \<EE>)\<close>
proof (intro is_cq_map_def[THEN iffD2] conjI)
  have [iff]: \<open>kraus_map \<EE>\<close>
    using assms(4) is_cq_map_def by blast
  then show km: \<open>kraus_map (km_local_register Q \<rho> \<EE>)\<close>
    using assms(3) by fastforce

  have lifto: \<open>f o g = h \<Longrightarrow> l o f o g = l o h\<close> for f g h l
    by auto

  have 1: \<open>cq_id C o partial_trace = partial_trace o (km_tensor (cq_id C) id)\<close>
    by (auto simp: partial_trace_ignores_kraus_map)
  have comm: \<open>swap_QREGISTER Q o\<^sub>C\<^sub>L apply_qregister C a \<otimes>\<^sub>o id_cblinfun =
         apply_qregister C a \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L swap_QREGISTER Q\<close> for a
  proof -
    define QQ CC where \<open>QQ = Rep_QREGISTER Q\<close> and \<open>CC = range (apply_qregister C)\<close>
    have swap_QQ: \<open>swap_QREGISTER Q \<in> QQ \<otimes>\<^sub>v\<^sub>N QQ\<close>
      using is_swap_on_qupdate_set_swap_QREGISTER[OF \<open>ACTUAL_QREGISTER Q\<close>]
      by (simp add: is_swap_on_qupdate_set_def QQ_def)
    have [iff]: \<open>von_neumann_algebra QQ\<close>
      using QQ_def Rep_QREGISTER valid_qregister_range_def by auto
    have \<open>apply_qregister C a \<in> commutant QQ\<close>
      using \<open>Qqcompatible Q C\<close>
      by (simp add: QQ_def Qqcompatible.rep_eq commutant_memberI)
    then have \<open>apply_qregister C a \<otimes>\<^sub>o id_cblinfun \<in> commutant QQ \<otimes>\<^sub>v\<^sub>N commutant QQ\<close>
      apply (rule tensor_op_in_tensor_vn)
      using commutant_UNIV by blast
    also have \<open>commutant QQ \<otimes>\<^sub>v\<^sub>N commutant QQ \<subseteq> commutant (QQ \<otimes>\<^sub>v\<^sub>N QQ)\<close>
      apply (rule commutant_tensor_vn_subset)
      by auto
    finally show ?thesis
      by (simp add: swap_QQ commutant_def)
  qed
  have 2: \<open>km_tensor (cq_id C) id \<circ> sandwich_tc (swap_QREGISTER Q) = sandwich_tc (swap_QREGISTER Q) o km_tensor (cq_id C) id\<close>
    apply (rule km_commute)
      apply (rule km_operators_in_sandwich)
     apply (rule km_operators_in_tensor)
      apply (rule km_operators_in_cq_id)
     apply (rule km_operators_in_id)
    unfolding commutant_span
    by (auto simp: comm commutant_def)
  have 3: \<open>km_tensor (cq_id C) (id :: ('x ell2,'x ell2) trace_class \<Rightarrow> _) \<circ> km_tensor \<EE> id = km_tensor \<EE> id\<close>
    by (simp add: km_tensor_kraus_map_exists cq_map_id_left assms flip: km_tensor_compose_distrib)
  have 4: \<open>(\<lambda>\<sigma>. tc_tensor \<sigma> \<rho>) \<circ> cq_id C = km_tensor (cq_id C) id o (\<lambda>\<sigma>. tc_tensor \<sigma> \<rho>)\<close>
    by (auto intro!: ext simp: km_tensor_apply km_tensor_kraus_map_exists)
  have 5: \<open>km_tensor \<EE> id \<circ> km_tensor (cq_id C) (id :: ('x ell2,'x ell2) trace_class \<Rightarrow> _) = km_tensor \<EE> id\<close>
    by (simp add: km_tensor_kraus_map_exists cq_map_id_right assms flip: km_tensor_compose_distrib)

  show \<open>cq_id C \<circ> km_local_register Q \<rho> \<EE> \<circ> cq_id C = km_local_register Q \<rho> \<EE>\<close>
    apply (simp add: km_local_register_def km_map_with_auxiliary_state_def o_assoc flip: id_def)
    apply (simp add: o_assoc 1 lifto[OF 2] lifto[OF 3] lifto[OF 4])
    by (simp add: o_assoc lifto[OF 2[symmetric]] lifto[OF 5])
qed







lemma classical_on_cq_id_idem_general:
  fixes \<EE> :: \<open>('a::chilbert_space,'a) trace_class \<Rightarrow> ('b ell2, 'b ell2) trace_class\<close>
  assumes \<open>separating_set (kraus_map :: (_ \<Rightarrow> ('b ell2,'b ell2) trace_class) \<Rightarrow> _) S\<close>
  assumes \<open>kraus_map \<EE>\<close>
  assumes \<open>\<And>\<rho>. \<rho> \<in> S \<Longrightarrow> classical_on C (\<EE> \<rho>)\<close>
  shows \<open>cq_id C o \<EE> = \<EE>\<close>
proof -
  have \<open>cq_id C (\<EE> \<rho>) = \<EE> \<rho>\<close> if \<open>\<rho> \<in> S\<close> for \<rho>
    using assms(3) classical_on_def that by blast
  then show ?thesis
    by (smt (verit, del_insts) assms(1,2) eq_from_separatingI kraus_map_comp kraus_map_cq_id o_def)
qed

lemma classical_on_cq_id_idem:
  assumes \<open>kraus_map \<EE>\<close>
  assumes \<open>\<And>\<rho>. \<rho> \<ge> 0 \<Longrightarrow> norm \<rho> \<le> 1 \<Longrightarrow> classical_on C (\<EE> \<rho>)\<close>
  shows \<open>cq_id C o \<EE> = \<EE>\<close>
  apply (intro classical_on_cq_id_idem_general separating_kraus_map_bounded_clinear separating_bounded_clinear_clinear)
  apply (rule separating_density_ops[where B=1])
  using assms by auto

lemma classical_on_partial_trace:
  assumes \<open>classical_on (qregister_chain qFst C) \<rho>\<close>
  shows \<open>classical_on C (partial_trace \<rho>)\<close>
  using assms
  by (simp add: classical_on_def cq_id_def km_apply_qregister_partial_trace)

lemma is_cq_map_non_qregister[simp]: \<open>is_cq_map non_qregister \<EE> \<longleftrightarrow> \<EE> = 0\<close>
  by (auto simp: is_cq_map_def zero_fun_def)

(*
lemma is_cq_map_km_local_register_classical:
  assumes \<open>is_cq_map C \<EE>\<close>
  (* assumes \<open>classical_on C \<rho>\<close> *)
  assumes \<open>\<rho> \<ge> 0\<close>
  assumes \<open>ACTUAL_CREGISTER X\<close>
  shows \<open>is_cq_map C (km_local_register (QREGISTER_chain C (QREGISTER_of_CREGISTER X)) \<rho> \<EE> o cq_id C)\<close> (is ?goal)
proof -
  wlog [iff]: \<open>qregister C\<close>
  proof -
    have \<open>\<EE> 0 = 0\<close>
      by (metis assms(1) cq_id_invalid cq_map_id_left func_zero non_qregister o_def that)
    moreover have \<open>kraus_map \<EE>\<close>
      using assms(1) is_cq_map_def by blast
    ultimately show ?thesis
      using negation
      by (simp add: non_qregister o_def km_local_register_bot flip: zero_fun_def)
  qed
  show ?thesis
  proof (intro is_cq_map_def[THEN iffD2] conjI)
    define CX where \<open>CX = QREGISTER_chain C (QREGISTER_of_CREGISTER X)\<close>
    have [iff]: \<open>kraus_map \<EE>\<close>
      using assms(1) is_cq_map_def by blast
    then show km: \<open>kraus_map (km_local_register CX \<rho> \<EE> o cq_id C)\<close>
      apply (rule_tac kraus_map_comp)
       apply (rule kraus_map_km_local_register)
      using assms by auto

    have \<open>cq_id C \<circ> (km_local_register CX \<rho> \<EE> \<circ> cq_id C) \<circ> cq_id C = cq_id C \<circ> (km_local_register CX \<rho> \<EE> \<circ> cq_id C)\<close>
      by fastforce
    also
    from ACTUAL_CREGISTER_ex_register[OF \<open>ACTUAL_CREGISTER X\<close>]
    have \<open>let 'l::type = ACTUAL_CREGISTER_content X in
        cq_id C \<circ> (km_local_register CX \<rho> \<EE> \<circ> cq_id C) = km_local_register CX \<rho> \<EE> \<circ> cq_id C\<close>
    proof (rule with_type_mp)
      assume \<open>\<exists>X' :: ('l, 'a) cregister. cregister X' \<and> CREGISTER_of X' = X\<close>
      then obtain X' :: \<open>('l, 'a) cregister\<close> where \<open>cregister X'\<close> and \<open>CREGISTER_of X' = X\<close>
        by auto

      from ccomplement_exists[OF \<open>cregister X'\<close>]
      have \<open>let 'm::type = ccomplement_domain X' in
          cq_id C \<circ> (km_local_register CX \<rho> \<EE> \<circ> cq_id C) = km_local_register CX \<rho> \<EE> \<circ> cq_id C\<close>
      proof (rule with_type_mp)
        assume \<open>\<exists>Y :: ('m, 'a) cregister. ccomplements X' Y\<close>
        then obtain Y :: \<open>('m, 'a) cregister\<close> where \<open>ccomplements X' Y\<close>
          by auto

        show \<open>cq_id C \<circ> (km_local_register CX \<rho> \<EE> \<circ> cq_id C) = km_local_register CX \<rho> \<EE> \<circ> cq_id C\<close>
        proof (rule classical_on_cq_id_idem)
          show \<open>kraus_map (km_local_register CX \<rho> \<EE> \<circ> cq_id C)\<close>
            using km by force

          fix \<sigma> :: \<open>('b ell2, 'b ell2) trace_class\<close>
          assume \<open>\<sigma> \<ge> 0\<close>
          define C1 :: \<open>(_, 'b\<times>'b) qregister\<close> where \<open>C1 = qregister_chain qFst C\<close>
          define CX' where \<open>CX' = qregister_chain C (qregister_of_cregister X')\<close>
          define CY where \<open>CY = qregister_chain C (qregister_of_cregister Y)\<close>
          define CX1 :: \<open>(_, 'b\<times>'b) qregister\<close> where \<open>CX1 = qregister_chain qFst CX'\<close>
          define CX2 :: \<open>(_, 'b\<times>'b) qregister\<close> where \<open>CX2 = qregister_chain qSnd CX'\<close>
          define CY1 :: \<open>(_, 'b\<times>'b) qregister\<close> where \<open>CY1 = qregister_chain qFst CY\<close>
          define CXY1 where \<open>CXY1 = qregister_pair CX1 CY1\<close>

          from \<open>ccomplements X' Y\<close>
          have [iff]: \<open>cregister \<lbrakk>X', Y\<rbrakk>\<^sub>c\<close>
            by -
          have [iff]: \<open>qregister \<lbrakk>CX1, CY1\<rbrakk>\<^sub>q\<close>
            by (auto intro!: qcompatible_chain simp: CX1_def CY1_def CX'_def CY_def)

          have \<open>classical_on C (cq_id C \<sigma>)\<close> (is \<open>classical_on _ ?\<sigma>\<^sub>2\<close>)
            by x
          then have \<open>classical_on C1 (tc_tensor ?\<sigma>\<^sub>2 \<rho>)\<close> (is \<open>classical_on _ ?\<sigma>\<^sub>3\<close>)
            by x
          have 3: \<open>classical_on CX1 ?\<sigma>\<^sub>3\<close>
            by x
          have 4: \<open>classical_on CY1 ?\<sigma>\<^sub>3\<close> (* Not used? *)
            by x
          have 5: \<open>classical_on CX2 (sandwich_tc (swap_QREGISTER CX) ?\<sigma>\<^sub>3)\<close>  (is \<open>classical_on _ ?\<sigma>\<^sub>4\<close>)
            by x
          have 6: \<open>classical_on CY1 ?\<sigma>\<^sub>4\<close> (* Not used? *)
            by x
          have 7: \<open>classical_on CXY1 (km_tensor \<EE> (( *\<^sub>V) id_cblinfun) ?\<sigma>\<^sub>4)\<close>  (is \<open>classical_on _ ?\<sigma>\<^sub>5\<close>)
            by x
          have  \<open>classical_on CX2 ?\<sigma>\<^sub>5\<close>
            by x
          have \<open>classical_on CX1 ?\<sigma>\<^sub>5\<close> (* Not used? *)
            by x
          have \<open>classical_on CY1 ?\<sigma>\<^sub>5\<close>
            by x
          have \<sigma>\<^sub>6_CX1: \<open>classical_on CX1 (sandwich_tc (swap_QREGISTER CX) ?\<sigma>\<^sub>5)\<close>  (is \<open>classical_on _ ?\<sigma>\<^sub>6\<close>)
            by x
          have \<sigma>\<^sub>6_CY1: \<open>classical_on CY1 ?\<sigma>\<^sub>6\<close>
            by x
          have \<open>classical_on CXY1 ?\<sigma>\<^sub>6\<close>
            using \<sigma>\<^sub>6_CX1 \<sigma>\<^sub>6_CY1
            by (auto intro!: simp: CXY1_def classical_on_pair)
          have \<open>classical_on C1 ?\<sigma>\<^sub>6\<close>
            by x
          then have \<open>classical_on C (partial_trace ?\<sigma>\<^sub>6)\<close>
            by (simp add: C1_def classical_on_partial_trace)
          then show \<open>classical_on C ((km_local_register CX \<rho> \<EE> \<circ> cq_id C) \<sigma>)\<close>
            by (simp add: km_local_register_def km_map_with_auxiliary_state_def id_def)
        qed
      qed
      from this[cancel_with_type]
      show \<open>cq_id C \<circ> (km_local_register CX \<rho> \<EE> \<circ> cq_id C) = km_local_register CX \<rho> \<EE> \<circ> cq_id C\<close>
        by -
    qed
    from this[cancel_with_type]
    have \<open>cq_id C \<circ> (km_local_register CX \<rho> \<EE> \<circ> cq_id C) = km_local_register CX \<rho> \<EE> \<circ> cq_id C\<close>
      by -
    finally show \<open>cq_id C \<circ> (km_local_register CX \<rho> \<EE> \<circ> cq_id C) \<circ> cq_id C = km_local_register CX \<rho> \<EE> \<circ> cq_id C\<close>
      by -
  qed
qed *)

definition cq_map_from_kraus_family :: \<open>('cl,'m) qregister \<Rightarrow> ('qu,'m) qregister \<Rightarrow> ('cl \<Rightarrow> ('qu ell2, 'qu ell2, 'cl) kraus_family) \<Rightarrow> (('m ell2, 'm ell2) trace_class \<Rightarrow> ('m ell2, 'm ell2) trace_class)\<close> where
  \<open>cq_map_from_kraus_family C Q \<EE> = 
      kf_apply
      (kf_comp_dependent (\<lambda>(_,c::'cl). kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c))))
      (kf_comp_dependent (\<lambda>c. kf_apply_qregister Q (\<EE> c)) 
      (kf_apply_qregister C (kf_complete_measurement_ket))))\<close>

(* TODO move *)
definition qregister_partial_trace :: \<open>('a,'m) qregister => ('m ell2, 'm ell2) trace_class => ('a ell2, 'a ell2) trace_class\<close> where
  \<open>qregister_partial_trace Q \<rho> = (SOME \<sigma>. \<forall>a. trace_tc (compose_tcr a \<sigma>) = trace_tc (compose_tcr (apply_qregister Q a) \<rho>))\<close>

(* TODO move *)
lemma trace_compose_eq_then_eq:
  fixes t u :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>\<And>a. trace (cblinfun_compose a t) = trace (cblinfun_compose a u)\<close>
  shows \<open>t = u\<close>
proof (rule cblinfun_eqI, rule cinner_extensionality, rename_tac h g)
  fix g :: 'b and h :: 'a
  from assms
  have \<open>trace (cblinfun_compose (butterfly h g) t) = trace (cblinfun_compose (butterfly h g) u)\<close>
    by simp
  then show \<open>g \<bullet>\<^sub>C (t *\<^sub>V h) = g \<bullet>\<^sub>C (u *\<^sub>V h)\<close>
    by (metis trace_butterfly_comp)
qed


lemma qregister_partial_trace_unique:
  assumes \<open>\<And>a. trace_tc (compose_tcr a \<sigma>) = trace_tc (compose_tcr (apply_qregister Q a) \<rho>)\<close>
  shows \<open>qregister_partial_trace Q \<rho> = \<sigma>\<close>
proof -
  define \<sigma>' where \<open>\<sigma>' = qregister_partial_trace Q \<rho>\<close>
  have \<open>trace_tc (compose_tcr a \<sigma>') = trace_tc (compose_tcr (apply_qregister Q a) \<rho>)\<close> for a
    unfolding \<sigma>'_def qregister_partial_trace_def
    apply (rule someI2_ex) 
    using assms apply blast
    by simp
  with assms have \<open>trace_tc (compose_tcr a \<sigma>') = trace_tc (compose_tcr a \<sigma>)\<close> for a
    by simp
  then show \<open>\<sigma>' = \<sigma>\<close>
    apply transfer
    apply (rule trace_compose_eq_then_eq)
    by auto
qed

lemma qregister_partial_trace_via_complement:
  assumes \<open>qcomplements Q R\<close>
  shows \<open>qregister_partial_trace Q \<rho> = partial_trace (apply_qregister_tc (qregister_inv \<lbrakk>Q,R\<rbrakk>\<^sub>q) \<rho>)\<close>
  by x

lemma separating_set_bounded_clinear_iso_qregister_nested:
  fixes Q :: \<open>('a,'b) qregister\<close> and S :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) set\<close>
  assumes \<open>iso_qregister Q\<close>
  assumes \<open>separating_set (bounded_clinear :: (_\<Rightarrow>'c::complex_normed_vector) \<Rightarrow> _) S\<close>
  shows \<open>separating_set (bounded_clinear :: (_\<Rightarrow>'c::complex_normed_vector) \<Rightarrow> _) (apply_qregister Q ` S)\<close>
try0
sledgehammer [dont_slice]
proof (intro separating_setI)
  fix f g :: \<open>('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> 'c\<close>
  assume \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close>
  assume fg_QS: \<open>f u = g u\<close> if \<open>u \<in> apply_qregister Q ` S\<close> for u
  define f' g' where \<open>f' t = f (apply_qregister Q t)\<close> and \<open>g' t = g (apply_qregister Q t)\<close> for t
  have [iff]: \<open>bounded_clinear f'\<close>  \<open>bounded_clinear g'\<close>
    by (auto intro!: 
        comp_bounded_clinear[OF \<open>bounded_clinear f\<close>, unfolded o_def]
        comp_bounded_clinear[OF \<open>bounded_clinear g\<close>, unfolded o_def] 
        bounded_clinear_apply_qregister_tc assms
        simp: f'_def[abs_def] g'_def[abs_def])
  have \<open>f' t = g' t\<close> if \<open>t \<in> S\<close> for t
    by (simp add: f'_def fg_QS g'_def that)
  then have \<open>f' = g'\<close>
    apply (rule_tac eq_from_separatingI[OF assms(2)])
    by auto
  show \<open>f = g\<close>
  proof (rule ext)
    fix t :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    from assms have surj_Q: \<open>surj (apply_qregister Q)\<close>
      by (meson bij_def bij_iso_qregister)
    then obtain u where u: \<open>t = apply_qregister Q u\<close>
      by fast
    with \<open>f' = g'\<close>
    have \<open>f' u = g' u\<close>
      by simp
    then show \<open>f t = g t\<close>
      by (simp add: f'_def g'_def u)
  qed
qed



lemma qregister_partial_trace_exists:
  \<open>trace_tc (compose_tcr a (qregister_partial_trace Q \<rho>)) = trace_tc (compose_tcr (apply_qregister Q a) \<rho>)\<close>
proof -
  wlog \<open>qregister Q\<close>
    by x
  define \<sigma> where \<open>\<sigma> = qregister_partial_trace Q \<rho>\<close>
  from qcomplement_exists[OF \<open>qregister Q\<close>]
  have \<open>let 'g::type = qregister_decomposition_basis Q in
        trace_tc (compose_tcr a \<sigma>) = trace_tc (compose_tcr (apply_qregister Q a) \<rho>)\<close>
  proof with_type_mp
    with_type_case
    then obtain R :: \<open>('g, 'b) qregister\<close> where \<open>qcomplements Q R\<close>
      by auto
    then have \<sigma>_pt: \<open>\<sigma> = partial_trace (apply_qregister_tc (qregister_inv \<lbrakk>Q,R\<rbrakk>\<^sub>q) \<rho>)\<close>
      unfolding \<sigma>_def
      by (rule qregister_partial_trace_via_complement)
    define \<rho>' where \<open>\<rho>' = apply_qregister_tc (qregister_inv \<lbrakk>Q,R\<rbrakk>\<^sub>q) \<rho>\<close>

    have 1: \<open>trace_tc (compose_tcr a (partial_trace \<rho>')) = trace_tc (compose_tcr (a \<otimes>\<^sub>o id_cblinfun) \<rho>')\<close> for a
      by -

    have \<open>trace_tc (compose_tcr (apply_qregister Q a) \<rho>)
     = trace_tc (compose_tcr (apply_qregister \<lbrakk>Q,R\<rbrakk>\<^sub>q (a \<otimes>\<^sub>o id_cblinfun)) (apply_qregister_tc \<lbrakk>Q,R\<rbrakk>\<^sub>q \<rho>'))\<close>
      apply (rule arg_cong2[where f=\<open>\<lambda>x y. trace_tc (compose_tcr x y)\<close>])
      using \<open>qcomplements Q R\<close> apply_qregister_extend_pair_right iso_qregister_def' qcomplements_def'
       apply blast 
      by (metis \<open>qcomplements Q R\<close> \<rho>'_def apply_qregister_tc_inv_inverse iso_qregister_inv_iso
          qcomplements_def')
    also have \<open>\<dots> = trace_tc (apply_qregister_tc \<lbrakk>Q,R\<rbrakk>\<^sub>q (compose_tcr (a \<otimes>\<^sub>o id_cblinfun) \<rho>'))\<close>
      apply (rule arg_cong[where f=trace_tc])
      by -
    also have \<open>\<dots> = trace_tc (compose_tcr (a \<otimes>\<^sub>o id_cblinfun) \<rho>')\<close>
      by -
    also have \<open>\<dots> = trace_tc (compose_tcr a (partial_trace \<rho>'))\<close>
      using "1" by presburger
    also have \<open>\<dots> = trace_tc (compose_tcr a \<sigma>)\<close>
      using \<rho>'_def \<sigma>_pt by fastforce
    finally show \<open>trace_tc (compose_tcr a \<sigma>) = trace_tc (compose_tcr (apply_qregister Q a) \<rho>)\<close>
      by simp
  qed
  from this[cancel_with_type]
  show ?thesis
    by (simp add: \<sigma>_def)
qed


definition kraus_family_from_cq_map :: \<open>('cl,'m) qregister \<Rightarrow> ('qu,'m) qregister \<Rightarrow> 
         (('m ell2, 'm ell2) trace_class \<Rightarrow> ('m ell2, 'm ell2) trace_class) \<Rightarrow> 
         ('cl \<Rightarrow> ('qu ell2, 'qu ell2, 'cl) kraus_family)\<close> where
  \<open>kraus_family_from_cq_map C Q \<EE> c = 
      kf_map_inj snd
      (kf_comp kf_partial_trace_left
      (kf_comp (km_some_kraus_family (km_apply_qregister (qregister_inv \<lbrakk>C,Q\<rbrakk>\<^sub>q) \<EE>))
      (kf_tensor_left (tc_butterfly (ket c) (ket c)))))\<close>

lemma cq_map_from_kraus_family_invalid1[simp]: \<open>cq_map_from_kraus_family non_qregister Q \<EE> = 0\<close>
  by (simp add: cq_map_from_kraus_family_def[abs_def])

lemma cq_map_from_kraus_family_invalid2[simp]: \<open>cq_map_from_kraus_family C non_qregister \<EE> = 0\<close>
  by (simp add: cq_map_from_kraus_family_def[abs_def])

(* TODO move *)
lemma bdd_above_const_image[iff]: \<open>bdd_above ((\<lambda>_. x) ` Y)\<close>
  by fast

(* Inspiration from lift_definition denotation_cases :: \<open>(cl \<Rightarrow> denotation) \<Rightarrow> denotation\<close> ? *)
lemma cq_map_from_kraus_family_is_cq_map: \<open>is_cq_map C (cq_map_from_kraus_family C Q \<EE>)\<close>
proof -
  wlog qregC: \<open>qregister C\<close>
    using negation
    by (simp add: non_qregister)
  wlog qregQ: \<open>qregister Q\<close> keeping qregC
    using negation
    by (simp add: non_qregister)
  wlog bdd0: \<open>bdd_above (range (\<lambda>x. kf_norm (\<EE> x)))\<close> keeping qregC qregQ
  proof -
    from negation
    have \<open>\<not> bdd_above
        ((kf_norm \<circ> (\<lambda>c. kf_apply_qregister Q (\<EE> c))) `
         kf_domain (kf_apply_qregister C kf_complete_measurement_ket))\<close>
      by (simp add: o_def kf_norm_apply_qregister qregQ kf_domain_apply_qregister qregC)
    then have \<open>cq_map_from_kraus_family C Q \<EE> = 0\<close>
      by (simp add: cq_map_from_kraus_family_def kf_comp_dependent_invalid)
    then show ?thesis
      unfolding is_cq_map_def
      by (simp add: cq_map_id_left cq_map_id_right)
  qed
  note [simp] = qregC qregQ
  from bdd0 have bdd: \<open>bdd_above ((\<lambda>x. kf_norm (\<EE> (f x))) ` X)\<close> for X f
    apply (rule bdd_above_mono)
    by auto
  have km: \<open>kraus_map (cq_map_from_kraus_family C Q \<EE>)\<close>
    by (simp add: cq_map_from_kraus_family_def)
  define kf_cq_id where \<open>kf_cq_id = kf_apply_qregister C kf_complete_measurement_ket\<close>
  define kf_cq_map where \<open>kf_cq_map = kf_comp_dependent 
      (\<lambda>(_,c). kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c))))
      (kf_comp_dependent (\<lambda>c. kf_apply_qregister Q (\<EE> c)) 
      (kf_apply_qregister C kf_complete_measurement_ket))\<close>
  have kf_apply_id: \<open>kf_apply kf_cq_id = cq_id C\<close>
    by (simp add: kf_cq_id_def kf_eq_weak_def cq_id_def cq_map_from_kraus_family_def
        flip: km_apply_qregister_kf_apply km_complete_measurement_ket_kf_complete_measurement_ket)
  have kf_apply_map: \<open>kf_apply kf_cq_map = cq_map_from_kraus_family C Q \<EE>\<close>
    by (simp add: kf_cq_map_def kf_eq_weak_def kf_comp_apply kf_apply_id cq_map_from_kraus_family_def
        flip: km_apply_qregister_kf_apply km_complete_measurement_ket_kf_complete_measurement_ket)
  have 1: \<open>kf_comp kf_cq_id kf_cq_map =\<^sub>k\<^sub>r kf_cq_map\<close>
  proof -
    have \<open>kf_comp kf_cq_id kf_cq_map =\<^sub>k\<^sub>r 
     kf_comp_dependent (\<lambda>(_, c). (kf_comp kf_cq_id (kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c))))))
       (kf_comp_dependent (\<lambda>c. kf_apply_qregister Q (\<EE> c)) (kf_apply_qregister C kf_complete_measurement_ket))\<close>
      apply (simp add: kf_cq_id_def kf_cq_map_def)
      apply (rule kf_comp_dependent_comp_assoc_weak[THEN kf_eq_weak_sym, THEN kf_eq_weak_trans])
       apply (force simp: case_prod_unfold kf_norm_apply_qregister kf_norm_constant norm_tc_butterfly qregC)
      by (simp add: case_prod_unfold)
    also have \<open>\<dots> =
     kf_comp_dependent (\<lambda>(_, c). (kf_apply_qregister C (kf_comp kf_complete_measurement_ket (kf_constant (tc_butterfly (ket c) (ket c))))))
       (kf_comp_dependent (\<lambda>c. kf_apply_qregister Q (\<EE> c)) (kf_apply_qregister C kf_complete_measurement_ket))\<close>
      by (simp add: kf_apply_qregister kf_cq_id_def)
    also have \<open>\<dots> =\<^sub>k\<^sub>r 
     kf_comp_dependent (\<lambda>(_, c). (kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c)))))
       (kf_comp_dependent (\<lambda>c. kf_apply_qregister Q (\<EE> c)) (kf_apply_qregister C kf_complete_measurement_ket))\<close>
    proof -
      have bdd1: \<open>bdd_above
       ((kf_norm \<circ> (\<lambda>(_, c). kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c))))) `
        kf_domain (kf_comp_dependent (\<lambda>c. kf_apply_qregister Q (\<EE> c)) (kf_apply_qregister C kf_complete_measurement_ket)))\<close>
        by (force simp add: case_prod_unfold kf_norm_constant norm_tc_butterfly)
      have \<open>tc_butterfly (ket c) (ket c) = kf_complete_measurement_ket *\<^sub>k\<^sub>r tc_butterfly (ket c) (ket c)\<close> for c::'a
        by (simp add: kf_complete_measurement_ket_apply_butterfly)
      then have \<open>kf_constant (tc_butterfly (ket c) (ket c)) =\<^sub>k\<^sub>r kf_constant (kf_complete_measurement_ket *\<^sub>k\<^sub>r tc_butterfly (ket c) (ket c))\<close> for c :: 'a
        by fastforce
      also have \<open>\<dots>c =\<^sub>k\<^sub>r kf_comp kf_complete_measurement_ket (kf_constant (tc_butterfly (ket c) (ket c)))\<close> for c :: 'a
        apply (rule kf_eq_weak_sym)
        apply (rule kf_comp_constant_right_weak)
        by simp
      finally show ?thesis
        apply (rule_tac kf_eq_weak_sym)
        by (auto intro!: kf_comp_dependent_cong_weak bdd1 kf_apply_qregister_cong_weak)
    qed
    also have \<open>\<dots> = kf_cq_map\<close>
      using kf_cq_map_def by fastforce
    finally show ?thesis
      by -
  qed
  have 2: \<open>kf_comp kf_cq_map kf_cq_id =\<^sub>k\<^sub>r kf_cq_map\<close>
  proof -
    have \<open>kf_comp kf_cq_map kf_cq_id =\<^sub>k\<^sub>r 
     kf_comp_dependent (\<lambda>(_,_,c). kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c))))
     (kf_comp (kf_comp_dependent (\<lambda>c. kf_apply_qregister Q (\<EE> c)) kf_cq_id) kf_cq_id)\<close>
      apply (simp add: kf_cq_map_def kf_cq_id_def)
      apply (rule kf_comp_comp_dependent_assoc_weak)
      by (simp add: case_prod_unfold kf_norm_constant norm_tc_butterfly qregC)
    also have \<open>\<dots> =\<^sub>k\<^sub>r 
     kf_comp_dependent (\<lambda>(_,_,c). kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c))))
     (kf_map (\<lambda>((a,b),c). (a,b,c)) (kf_comp_dependent (\<lambda>(_,c). kf_apply_qregister Q (\<EE> c)) (kf_comp kf_cq_id kf_cq_id)))\<close>
      apply (rule kf_comp_dependent_cong_weak)
        apply (force simp add: case_prod_unfold kf_norm_constant norm_tc_butterfly qregC)
       apply simp
      apply (simp add: kf_comp_def)
      apply (rule kf_comp_dependent_assoc[THEN kf_eq_trans])
        apply (simp add: kf_norm_apply_qregister qregQ bdd case_prod_unfold)
       apply simp
      by simp
    also have \<open>\<dots> =\<^sub>k\<^sub>r 
     kf_comp_dependent (\<lambda>(_,_,c). kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c))))
     (kf_map (\<lambda>((a,b),c). (a,b,c)) (kf_comp_dependent (\<lambda>(_,c). kf_apply_qregister Q (\<EE> c)) (kf_map (\<lambda>c. (c,c)) kf_cq_id)))\<close>
    proof -
      have *: \<open>kf_comp kf_cq_id kf_cq_id \<equiv>\<^sub>k\<^sub>r kf_map (\<lambda>c. (c, c)) kf_cq_id\<close>
        by (auto intro!: kf_apply_qregister_cong kf_complete_measurement_ket_idem
            simp: kf_cq_id_def
            simp flip: kf_apply_qregister kf_apply_qregister_kf_map)
      show ?thesis
        apply (rule kf_comp_dependent_cong_weak)
          apply (auto intro: bdd_aboveI simp add: case_prod_unfold kf_norm_apply_qregister
            \<open>qregister C\<close> kf_norm_constant norm_tc_butterfly)[1]
         apply (rule kf_eq_weak_reflI)
        apply (rule kf_map_cong, rule refl)
        apply (rule kf_comp_dependent_cong)
          apply (auto intro: bdd_aboveI bdd simp add: case_prod_unfold kf_norm_apply_qregister 
            \<open>qregister C\<close> kf_norm_constant norm_tc_butterfly image_image)[1]
         apply simp
        by (fact *)
    qed
    also have \<open>\<dots> =\<^sub>k\<^sub>r 
     kf_comp_dependent (\<lambda>(_,_,c). kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c))))
     (kf_map (\<lambda>((a,b),c). (a,b,c)) (kf_comp_dependent (\<lambda>(_,c). kf_apply_qregister Q (\<EE> c)) (kf_map_inj (\<lambda>c. (c,c)) kf_cq_id)))\<close>
    proof -
      have *: \<open>kf_map (\<lambda>c. (c, c)) kf_cq_id \<equiv>\<^sub>k\<^sub>r kf_map_inj (\<lambda>c. (c, c)) kf_cq_id\<close>
        apply (rule kf_eq_sym)
        apply (rule kf_map_inj_eq_kf_map)
        by (auto intro!: inj_onI)
      show ?thesis
        apply (rule kf_comp_dependent_cong_weak)
          apply (auto intro: bdd_aboveI simp add: case_prod_unfold kf_norm_apply_qregister
            \<open>qregister C\<close> kf_norm_constant norm_tc_butterfly)[1]
         apply (rule kf_eq_weak_reflI)
        apply (rule kf_map_cong, rule refl)
        apply (rule kf_comp_dependent_cong)
          apply (auto intro: bdd_aboveI bdd simp add: case_prod_unfold kf_norm_apply_qregister 
            \<open>qregister C\<close> kf_norm_constant norm_tc_butterfly image_image)[1]
         apply simp
        by (fact *)
    qed
    also have \<open>\<dots> =
     kf_comp_dependent (\<lambda>(_,_,c). kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c))))
     (kf_map (\<lambda>((a,b),c). (a,b,c)) (kf_map_inj (\<lambda>(c,x). ((c,c),x)) (kf_comp_dependent (\<lambda>c. kf_apply_qregister Q (\<EE> c)) kf_cq_id)))\<close>
      apply (subst kf_comp_dependent_map_inj_right)
      by (auto intro!: inj_onI)
    also have \<open>\<dots> =
     kf_comp_dependent (\<lambda>(_,_,c). kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c))))
     (kf_map (\<lambda>(a,c). (a,a,c)) (kf_comp_dependent (\<lambda>c. kf_apply_qregister Q (\<EE> c)) kf_cq_id))\<close>
      apply (subst kf_map_kf_map_inj_comp)
      by (auto intro!: inj_onI simp: o_def case_prod_unfold)
    also have \<open>\<dots> =\<^sub>k\<^sub>r kf_comp_dependent (\<lambda>(_, c). kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c))))
                                       (kf_comp_dependent (\<lambda>c. kf_apply_qregister Q (\<EE> c)) kf_cq_id)\<close>
      apply (rule kf_comp_dependent_map_right_weak[THEN kf_eq_weak_trans])
      by (simp add: case_prod_unfold)
    also have \<open>\<dots> =\<^sub>k\<^sub>r kf_cq_map\<close>
      by (simp add: kf_cq_map_def flip: kf_cq_id_def)
    finally show ?thesis
      by -
  qed
  from 1 2
  have cq: \<open>cq_id C \<circ> cq_map_from_kraus_family C Q \<EE> \<circ> cq_id C = cq_map_from_kraus_family C Q \<EE>\<close>
    by (simp add: kf_eq_weak_def kf_comp_apply kf_apply_id kf_apply_map)
  from km cq show ?thesis
    using is_cq_map_def by blast
qed

lemma cq_map_from_kraus_family_norm:
  assumes \<open>\<And>x. kf_norm (\<EE> x) \<le> B\<close>
  shows \<open>km_norm (cq_map_from_kraus_family C Q \<EE>) \<le> B\<close>
proof -
  have Bpos: \<open>B \<ge> 0\<close>
    apply (rule order_trans)
     apply (rule kf_norm_geq0)
    by (rule assms)
  wlog qregQ: \<open>qregister Q\<close> keeping Bpos
    using negation
    by (simp add: non_qregister Bpos)
  wlog qregC: \<open>qregister C\<close> keeping qregQ Bpos
    using negation
    by (simp add: non_qregister Bpos)
  have 1: \<open>kf_norm (kf_apply_qregister Q (\<EE> c)) \<le> B\<close> for c
    by (simp add: assms qregQ)
  have 2: \<open>kf_norm (kf_apply_qregister C kf_complete_measurement_ket) \<le> 1\<close>
    by (simp add: qregC)
  from 1 2
  have 3: \<open>kf_norm (kf_comp_dependent (\<lambda>c. kf_apply_qregister Q (\<EE> c)) (kf_apply_qregister C kf_complete_measurement_ket)) \<le> B\<close>
    apply (rule_tac order_trans[of _ \<open>B * _\<close>])
     apply (rule kf_comp_dependent_norm_leq)
    by (auto simp: Bpos qregC)
  have 4: \<open>kf_norm (kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c)))) \<le> 1\<close> for c
    by (simp add: kf_norm_constant norm_tc_butterfly qregC)
  from 3 4
  have 5: \<open>kf_norm
     (kf_comp_dependent (\<lambda>(_, c). kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c))))
       (kf_comp_dependent (\<lambda>c. kf_apply_qregister Q (\<EE> c)) (kf_apply_qregister C kf_complete_measurement_ket)))
    \<le> B\<close>
    by (smt (verit, ccfv_threshold) kf_comp_dependent_norm_leq mult_cancel_right1 split_def)
  from 5 show ?thesis
    by (simp add: cq_map_from_kraus_family_def km_norm_kf_norm)
qed


lemma cq_map_from_kraus_family_as_qFstqSnd:
  assumes \<open>qcomplements C Q\<close>
  shows \<open>km_apply_qregister (qregister_inv \<lbrakk>C, Q\<rbrakk>\<^sub>q) (cq_map_from_kraus_family C Q \<EE>)
      = cq_map_from_kraus_family qFst qSnd \<EE>\<close>
  by x

(* TODO move *)
lemma kf_comp_dependent_raw_kf_filter_move:
  assumes \<open>bdd_above ((kf_norm o \<EE>) ` Set.filter P (kf_domain \<FF>))\<close>
  shows \<open>kf_comp_dependent_raw \<EE> (kf_filter P \<FF>) = kf_comp_dependent_raw (\<lambda>c. if P c then \<EE> c else 0) \<FF>\<close>
proof (rule Rep_kraus_family_inject[THEN iffD1])
  from assms have bdd1: \<open>bdd_above ((kf_norm \<circ> \<EE>) ` kf_domain (kf_filter P \<FF>))\<close>
    by (simp add: kf_domain_filter)
  then obtain B where B: \<open>kf_norm (\<EE> x) \<le> B\<close> if \<open>x \<in> kf_domain (kf_filter P \<FF>)\<close> for x
    by (force simp: bdd_above_def)
  have bdd2: \<open>bdd_above ((kf_norm \<circ> (\<lambda>c. if P c then \<EE> c else 0)) ` kf_domain \<FF>)\<close>
    apply (rule bdd_aboveI2[where M=\<open>max 0 B\<close>])
    using B by force

  have \<open>Rep_kraus_family (kf_comp_dependent_raw \<EE> (kf_filter P \<FF>))
       = Set.filter (\<lambda>(EF, _). EF \<noteq> 0) ((\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, x)) ` 
           (SIGMA (F, y):Set.filter (\<lambda>(F, y). P y) (Rep_kraus_family \<FF>). Rep_kraus_family (\<EE> y)))\<close>
    using bdd1
    by (simp add: kf_comp_dependent_raw.rep_eq case_prod_unfold kf_filter.rep_eq)
  also have \<open>\<dots> = Set.filter (\<lambda>(EF, F, E, y, x). EF \<noteq> 0 \<and> P y) ((\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, x)) ` 
           (SIGMA (F, y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y)))\<close>
    by force
  also have \<open>\<dots> = Set.filter (\<lambda>(EF, _). EF \<noteq> 0) ((\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, x)) `
      (SIGMA (F, y):Rep_kraus_family \<FF>. if P y then Rep_kraus_family (\<EE> y) else {}))\<close> (is \<open>?lhs = ?rhs\<close>)
  proof (rule Set.set_eqI, rename_tac tuple)
    fix tuple :: \<open>'e \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'e \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'b \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'a \<times> 'd\<close>
    obtain EF F E y x where tuple: \<open>tuple = (EF,F,E,y,x)\<close>
      apply atomize_elim
      by (auto simp: prod_eq_iff)
    show \<open>tuple \<in> ?lhs \<longleftrightarrow> tuple \<in> ?rhs\<close>
      apply (cases \<open>P y\<close>)
      apply (auto intro!: bexI[of _ \<open>(F, y)\<close>] bexI[of _ \<open>(E, x)\<close>] simp: tuple image_iff)[1]
      by (auto intro!: bexI[of _ \<open>(F, y)\<close>] simp: tuple image_iff)
  qed
  also have \<open>\<dots> = Set.filter (\<lambda>(EF, _). EF \<noteq> 0) ((\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, x)) `
      (SIGMA (F, y):Rep_kraus_family \<FF>. Rep_kraus_family (if P y then \<EE> y else 0)))\<close>
    by (metis (mono_tags, lifting) zero_kraus_family.rep_eq)
  also have \<open>\<dots> = Rep_kraus_family (kf_comp_dependent_raw (\<lambda>c. if P c then \<EE> c else 0) \<FF>)\<close>
    using bdd2 by (simp add: kf_comp_dependent_raw.rep_eq)
  finally show \<open>Rep_kraus_family (kf_comp_dependent_raw \<EE> (kf_filter P \<FF>)) = Rep_kraus_family (kf_comp_dependent_raw (\<lambda>c. if P c then \<EE> c else 0) \<FF>)\<close>
    by -
qed

(* TODO move *)
lemma kf_comp_dependent_kf_filter_move: 
  assumes \<open>bdd_above ((kf_norm \<circ> \<EE>) ` Set.filter P (kf_domain \<FF>))\<close>
  shows \<open>kf_comp_dependent \<EE> (kf_filter P \<FF>) = kf_comp_dependent (\<lambda>c. if P c then \<EE> c else 0) \<FF>\<close>
  (* apply (rule Rep_kraus_family_inject[THEN iffD1]) *)
  unfolding kf_comp_dependent_def
  apply (rule arg_cong[where f=\<open>kf_map _\<close>])
  using assms by (rule kf_comp_dependent_raw_kf_filter_move)

(* TODO move *)
lemma swap_tensor_tc_sandwich[simp]: \<open>sandwich_tc swap_ell2 (tc_tensor a b) = tc_tensor b a\<close>
  apply transfer'
  by simp


lemma cq_map_from_kraus_family_qFstqSnd_apply:
\<open>sandwich_tc (tensor_ell2_left (ket d)*)
(cq_map_from_kraus_family qFst qSnd \<EE> (tc_tensor (tc_butterfly (ket c) (ket c)) \<rho>))
= \<EE> c *\<^sub>k\<^sub>r @{d} \<rho>\<close>
proof -
  have bdd1: \<open>bdd_above
     ((\<lambda>x. kf_norm (case x of (_, c) \<Rightarrow> kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q (kf_constant (tc_butterfly (ket c) (ket c))))) `
      X)\<close> for X
by -

  have \<open>sandwich_tc (tensor_ell2_left (ket d)*)
          (cq_map_from_kraus_family qFst qSnd \<EE> (tc_tensor (tc_butterfly (ket c) (ket c)) \<rho>))
    = kf_of_op (tensor_ell2_left (ket d)*) *\<^sub>k\<^sub>r (kf_comp_dependent (\<lambda>(_, c). kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q (kf_constant (tc_butterfly (ket c) (ket c))))
       (kf_comp_dependent (\<lambda>c. kf_apply_qregister \<lbrakk>#2.\<rbrakk>\<^sub>q (\<EE> c)) (kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q kf_complete_measurement_ket)) *\<^sub>k\<^sub>r
      tc_tensor (tc_butterfly (ket c) (ket c)) \<rho>)\<close>
    by (simp add: cq_map_from_kraus_family_def kf_of_op_apply)
  also have \<open>\<dots> = (kf_comp_dependent (\<lambda>(_, c). kf_comp (kf_of_op (tensor_ell2_left (ket d)*)) (kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q (kf_constant (tc_butterfly (ket c) (ket c)))))
       (kf_comp_dependent (\<lambda>c. kf_apply_qregister \<lbrakk>#2.\<rbrakk>\<^sub>q (\<EE> c)) (kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q kf_complete_measurement_ket)) *\<^sub>k\<^sub>r
      tc_tensor (tc_butterfly (ket c) (ket c)) \<rho>)\<close>
    apply (subst kf_comp_apply[unfolded o_def, THEN fun_cong, symmetric])
    apply (rule kf_apply_eqI)
    apply (rule kf_comp_dependent_comp_assoc_weak[symmetric, THEN kf_eq_weak_trans])
     apply (simp add: bdd1)
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> = (kf_comp_dependent (\<lambda>(_, c). if c=d then kf_partial_trace_left else 0)
       (kf_comp_dependent (\<lambda>c. kf_apply_qregister \<lbrakk>#2.\<rbrakk>\<^sub>q (\<EE> c)) (kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q kf_complete_measurement_ket)) *\<^sub>k\<^sub>r
      tc_tensor (tc_butterfly (ket c) (ket c)) \<rho>)\<close>
(* We might use something else than kf_partial_trace_left here if it's easier *)
  proof -
    have *: \<open>kf_comp (kf_of_op (tensor_ell2_left (ket d)*)) (kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q (kf_constant (tc_butterfly (ket c) (ket c))))
                =\<^sub>k\<^sub>r (if c=d then kf_partial_trace_left else 0)\<close>
      by x
    show ?thesis
      apply (rule kf_apply_eqI)
      apply (rule kf_comp_dependent_cong_weak)
      subgoal by x
      using *
      by -
  qed
  also have \<open>\<dots> = kf_comp_dependent (\<lambda>_. kf_partial_trace_left)
     (kf_filter (\<lambda>(_,c). c = d \<and> True) (kf_comp_dependent (\<lambda>c. kf_apply_qregister qSnd (\<EE> c)) (kf_apply_qregister qFst kf_complete_measurement_ket))) *\<^sub>k\<^sub>r
    tc_tensor (tc_butterfly (ket c) (ket c)) \<rho>\<close>
    unfolding case_prod_unfold
    apply (subst kf_comp_dependent_kf_filter_move[symmetric])
    subgoal by x
    by simp
  also have \<open>\<dots> = kf_comp_dependent (\<lambda>_. kf_partial_trace_left)
     (kf_comp_dependent (\<lambda>e. kf_apply_qregister \<lbrakk>#2.\<rbrakk>\<^sub>q (kf_filter ((=)d) (\<EE> e))) (kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q kf_complete_measurement_ket)) *\<^sub>k\<^sub>r
    tc_tensor (tc_butterfly (ket c) (ket c)) \<rho>\<close>
    apply (subst kf_filter_comp_dependent)
    subgoal by x
    apply (subst flip_eq_const)
    by (simp add: kf_filter_kf_apply_qregister flip_eq_const)
  also have \<open>\<dots> = kf_partial_trace_left *\<^sub>k\<^sub>r
     (kf_comp_dependent (\<lambda>e. kf_apply_qregister \<lbrakk>#2.\<rbrakk>\<^sub>q (kf_filter ((=)d) (\<EE> e))) (kf_apply_qregister \<lbrakk>#1\<rbrakk>\<^sub>q kf_complete_measurement_ket)) *\<^sub>k\<^sub>r
    tc_tensor (tc_butterfly (ket c) (ket c)) \<rho>\<close>
    by (simp add: kf_comp_apply o_def flip: kf_comp_def )
  also have \<open>\<dots> = kf_partial_trace_left *\<^sub>k\<^sub>r
    kf_apply_qregister \<lbrakk>#2.\<rbrakk>\<^sub>q (kf_filter ((=)d) (\<EE> c)) *\<^sub>k\<^sub>r tc_tensor (tc_butterfly (ket c) (ket c)) \<rho>\<close>
    by x
  also have \<open>\<dots> = kf_partial_trace_left *\<^sub>k\<^sub>r
    tc_tensor (tc_butterfly (ket c) (ket c)) (kf_filter ((=)d) (\<EE> c) *\<^sub>k\<^sub>r \<rho>)\<close>
    by -
  also have \<open>\<dots> = kf_partial_trace_left *\<^sub>k\<^sub>r tc_tensor (tc_butterfly (ket c) (ket c)) (\<EE> c *\<^sub>k\<^sub>r @{d} \<rho>)\<close>
    by (metis (mono_tags, lifting) kf_apply_on_def kf_filter_cong_eq singletonD singletonI)
  also have \<open>\<dots> = \<EE> c *\<^sub>k\<^sub>r @{d} \<rho>\<close>
    apply (simp add: kf_partial_trace_left_def)
    apply (subst kf_apply_map_inj)
    subgoal by x
    by (simp add: kf_comp_apply kf_of_op_apply partial_trace_tensor trace_tc_butterfly flip: partial_trace_is_kf_partial_trace)
  finally show ?thesis
    by -
qed


lemma
  assumes \<open>qcomplements C Q\<close>
shows \<open>kraus_family_from_cq_map C Q (cq_map_from_kraus_family C Q \<EE>) c \<equiv>\<^sub>k\<^sub>r \<EE> c\<close>
proof (rule kf_eqI)
  fix x :: 'a and \<rho> :: \<open>('c ell2, 'c ell2) trace_class\<close>
  assume \<open>\<rho> \<ge> 0\<close>
  have inj_snd: \<open>inj_on snd X\<close> for X :: \<open>((unit \<times> unit) \<times> 'a) set\<close>
    by (auto intro!: inj_onI)
  have snd_x: \<open>(\<lambda>w. snd w = x) = (\<lambda>(e, f). f=x \<and> True)\<close>
    by auto

  have \<open>kraus_family_from_cq_map C Q (cq_map_from_kraus_family C Q \<EE>) c *\<^sub>k\<^sub>r @{x} \<rho> = 
kf_filter (\<lambda>w. snd w = x)
     (kf_comp kf_partial_trace_left
       (kf_comp
         (km_some_kraus_family (km_apply_qregister (qregister_inv \<lbrakk>C, Q\<rbrakk>\<^sub>q) (cq_map_from_kraus_family C Q \<EE>)))
         (kf_tensor_left (tc_butterfly (ket c) (ket c))))) *\<^sub>k\<^sub>r \<rho>\<close>
    by (simp add: kraus_family_from_cq_map_def kf_apply_on_def kf_filter_map_inj kf_apply_map_inj inj_snd)
  also have \<open>\<dots> = kf_partial_trace_left *\<^sub>k\<^sub>r @{x}
    km_some_kraus_family (km_apply_qregister (qregister_inv \<lbrakk>C, Q\<rbrakk>\<^sub>q) (cq_map_from_kraus_family C Q \<EE>)) *\<^sub>k\<^sub>r
    tc_tensor (tc_butterfly (ket c) (ket c)) \<rho>\<close>
    apply (subst snd_x)
    apply (subst kf_filter_comp)
    by (simp add: kf_comp_apply kf_apply_on_def)
  also have \<open>\<dots> = xxx\<close>
    apply (subst kf_apply_km_some_kraus_family)
subgoal by -
     apply (subst cq_map_from_kraus_family_as_qFstqSnd)
  apply (simp add: assms)


apply (subst kf_apply_map_inj)
apply (simp add: )
    by x
  show \<open>kraus_family_from_cq_map C Q (cq_map_from_kraus_family C Q \<EE>) c *\<^sub>k\<^sub>r @{x} \<rho> = \<EE> c *\<^sub>k\<^sub>r @{x} \<rho>\<close>

  apply (rule eq_from_separatingI2x) back
apply (rule )

  apply (rule ext)

  apply (auto intro!: ext 
simp add: kraus_family_from_cq_map_def[abs_def] cq_map_from_kraus_family_def)
  by x

lemma
  assumes \<open>is_cq_map C \<EE>\<close>
  shows \<open>cq_map_from_kraus_family C Q (kraus_family_from_cq_map C Q \<EE>) = \<EE>\<close>
  by x


lemma is_cq_map_plus:
  assumes \<open>is_cq_map C \<EE>\<close>
  assumes \<open>is_cq_map C \<FF>\<close>
  shows \<open>is_cq_map C (\<lambda>\<rho>. \<EE> \<rho> + \<FF> \<rho>)\<close>
proof -
  wlog \<open>qregister C\<close>
    using negation assms
    by (simp add: non_qregister zero_fun_def)
  from assms have \<open>kraus_map \<EE>\<close> and \<open>kraus_map \<FF>\<close>
    using is_cq_map_def by auto
  then have km: \<open>kraus_map (\<lambda>\<rho>. \<EE> \<rho> + \<FF> \<rho>)\<close>
    by blast
  from assms have cqE: \<open>cq_id C o \<EE> o cq_id C = \<EE>\<close> and cqF: \<open>cq_id C o \<FF> o cq_id C = \<FF>\<close>
    using is_cq_map_def by auto
  have cq: \<open>cq_id C o (\<lambda>\<rho>. \<EE> \<rho> + \<FF> \<rho>) o cq_id C = (\<lambda>\<rho>. \<EE> \<rho> + \<FF> \<rho>)\<close>
    using cqE[THEN fun_cong] cqF[THEN fun_cong]
    by (simp add: o_def complex_vector.linear_add bounded_clinear.clinear)
  from km cq show ?thesis
    by (simp add: is_cq_map_def)
qed

definition cq_map_local_c :: \<open>'cl CREGISTER \<Rightarrow> 'cl \<Rightarrow> 
        ((('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) trace_class \<Rightarrow> (('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) trace_class) \<Rightarrow> 
        ((('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) trace_class \<Rightarrow> (('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) trace_class)\<close> where
  \<open>cq_map_local_c F init \<EE> = cq_id qFst o km_local_register (QREGISTER_chain qFst (QREGISTER_of_CREGISTER F))
               (tc_butterfly (ket (init,undefined)) (ket (init,undefined))) \<EE> o cq_id qFst\<close>

lemma is_cq_map_cq_map_local_c[intro]:
  assumes \<open>kraus_map \<EE>\<close>
  shows \<open>is_cq_map qFst (cq_map_local_c F init \<EE>)\<close>
  using assms
  by (auto intro!: kraus_map_comp simp add: cq_map_local_c_def is_cq_map_def)

lemma kf_norm_cq_map_local_c: 
  assumes \<open>kraus_map \<EE>\<close>
  shows \<open>km_norm (cq_map_local_c F init \<EE>) \<le> km_norm \<EE>\<close>
  by (auto intro!: km_comp_norm_leq[THEN order.trans] kraus_map_comp assms
      km_norm_local_register[THEN order.trans]
      simp: cq_map_local_c_def norm_tc_butterfly)

definition cq_map_local_q :: \<open>'qu QREGISTER \<Rightarrow> ('qu ell2, 'qu ell2) trace_class \<Rightarrow> 
        ((('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) trace_class \<Rightarrow> (('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) trace_class) \<Rightarrow> 
        ((('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) trace_class \<Rightarrow> (('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) trace_class)\<close> where
  \<open>cq_map_local_q Q \<rho> \<EE> = km_local_register (QREGISTER_chain qSnd Q)
               (tc_tensor (tc_butterfly (ket undefined) (ket undefined)) \<rho>) \<EE>\<close>

lemma cq_id_qFst: \<open>cq_id qFst = km_tensor km_complete_measurement_ket id\<close>
  by (simp add: cq_id_def km_apply_qregister_qFst kraus_map_complete_measurement)

lemma is_cq_map_kf_comp_dependent:
  assumes cq\<FF>: \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> is_cq_map Q (kf_apply_on \<FF> {x})\<close>
  assumes cq\<EE>: \<open>\<And>x. x \<in> kf_domain \<FF> \<Longrightarrow> is_cq_map Q (kf_apply (\<EE> x))\<close>
  shows \<open>is_cq_map Q (kf_apply (kf_comp_dependent \<EE> \<FF>))\<close>
proof -
  wlog bdd\<EE>0: \<open>bdd_above ((kf_norm o \<EE>) ` kf_domain \<FF>)\<close>
    using negation
    by (simp add: kf_comp_dependent_invalid)
  wlog qreg: \<open>qregister Q\<close> keeping bdd\<EE>0
  proof -
    from cq\<EE> negation
    have \<open>\<EE> x =\<^sub>k\<^sub>r 0\<close> if \<open>x \<in> kf_domain \<FF>\<close> for x
      by (simp add: non_qregister kf_eq_weak_def that)
    then have \<open>kf_comp_dependent \<EE> \<FF> =\<^sub>k\<^sub>r 0\<close>
      apply (rule kf_comp_dependent_cong_weak[THEN kf_eq_weak_trans, rotated])
      using bdd\<EE>0 by auto
    then show ?thesis
      by (simp add: kf_eq_weak_def)
  qed
  from bdd\<EE>0 have bdd\<EE>: \<open>bdd_above ((\<lambda>x. kf_norm (\<EE> (f x))) ` X)\<close> if \<open>f ` X \<subseteq> kf_domain \<FF>\<close> for X f
    apply (rule bdd_above_mono)
    using that by force
  then have bdd': \<open>bdd_above ((\<lambda>x. kf_norm (kf_comp (kf_apply_qregister Q (kf_complete_measurement (range ket))) (\<EE> x))) ` X)\<close>
    if \<open>X \<subseteq> kf_domain \<FF>\<close> for X
    apply (rule bdd_above_mono2[OF _ order_refl])
    using that apply auto[1]
    apply (rule kf_comp_norm_leq[THEN order_trans])
    by (auto simp add: kf_norm_apply_qregister qreg)

  have \<open>kf_apply (kf_comp_dependent \<EE> \<FF>) o cq_id Q = kf_apply (kf_comp_dependent \<EE> \<FF>)\<close>
  proof -
    have dom_compD: \<open>(x, y) \<in> kf_domain (kf_comp A B) \<Longrightarrow> x \<in> kf_domain B \<and> y \<in> kf_domain A\<close> for A B x y
      using kf_domain_comp_subset[of A B] by blast

    have \<open>kf_apply (kf_comp_dependent \<EE> \<FF>) o cq_id Q
        = kf_apply (kf_comp (kf_comp_dependent \<EE> \<FF>) (kf_apply_qregister Q (kf_complete_measurement (range ket))))\<close>
      by (simp add: cq_id_def km_complete_measurement_kf_complete_measurement km_apply_qregister_kf_apply qreg kf_comp_apply)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (\<lambda>(_, f). \<EE> f) (kf_comp \<FF> (kf_apply_qregister Q (kf_complete_measurement (range ket)))))\<close>
      by (auto intro!: ext kf_apply_eqI kf_comp_comp_dependent_assoc_weak bdd\<EE> simp: o_def)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (\<lambda>(_, f). \<EE> f) (kf_map (\<lambda>(_,y). ((),y)) (kf_comp \<FF> (kf_apply_qregister Q (kf_complete_measurement (range ket))))))\<close>
      apply (rule sym)
      by (auto intro!: ext kf_apply_eqI kf_comp_dependent_map_right_weak[THEN kf_eq_weak_trans]
          simp: case_prod_unfold)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (\<lambda>(_, f). \<EE> f) (kf_comp (kf_map id \<FF>) (kf_map (\<lambda>_.()) (kf_apply_qregister Q (kf_complete_measurement (range ket))))))\<close>
      apply (rule sym)
      by (auto intro!: ext kf_apply_eqI kf_comp_dependent_cong_weak kf_comp_map_both[THEN kf_eq_trans] bdd\<EE>
          dest!: dom_compD
          simp: case_prod_unfold)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (\<lambda>(_, f). \<EE> f) (kf_comp \<FF> (kf_map (\<lambda>_.()) (kf_apply_qregister Q (kf_complete_measurement (range ket))))))\<close>
      by (auto intro!: ext kf_apply_eqI kf_comp_dependent_cong_weak kf_comp_cong kf_map_id bdd\<EE>
          dest!: dom_compD
          simp: case_prod_unfold)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (\<lambda>(_, f). \<EE> f) (kf_map (\<lambda>y. ((),y)) \<FF>))\<close>
    proof -
      have aux1: \<open>((=) x) = (\<lambda>(a,b). snd x = b)\<close> for x :: \<open>unit \<times> 'z\<close>
        apply (cases x) by auto
      have aux2: \<open>((=) x) = (\<lambda>y. y\<in>{x})\<close> for x
        by auto
      have aux3: \<open>((=) ()) = (\<lambda>_. True)\<close>
        by auto
      have \<open>kf_apply_on \<FF> {x} o cq_id Q = kf_apply_on \<FF> {x}\<close> for x
        using cq\<FF>[of x]
        by (metis cq_map_id_right in_kf_domain_iff_apply_nonzero is_cq_map_0)
      then have \<open>kf_comp (kf_filter ((=)x) \<FF>) (kf_filter ((=)()) (kf_flatten (kf_apply_qregister Q (kf_complete_measurement (range ket))))) =\<^sub>k\<^sub>r kf_map (Pair ()) (kf_filter ((=)x) \<FF>)\<close> for x
        apply (rule_tac kf_eq_weakI)
        by (simp add: kf_comp_apply aux2[of x] aux3 qreg cq_id_def del: insert_iff
            flip: kf_apply_on_def km_apply_qregister_kf_apply km_complete_measurement_kf_complete_measurement)
      then have \<open>kf_comp \<FF> (kf_flatten (kf_apply_qregister Q (kf_complete_measurement (range ket)))) \<equiv>\<^sub>k\<^sub>r kf_map (Pair ()) \<FF>\<close>
        apply (rule_tac kf_eqI_from_filter_eq_weak)
        apply (subst (asm) kf_filter_comp[symmetric])
        by (simp add: aux1 kf_filter_map)
      then show ?thesis
        by (auto intro!: ext kf_apply_eqI kf_comp_dependent_cong_weak bdd\<EE>
            dest!: dom_compD
            simp: case_prod_unfold)
    qed
    also have \<open>\<dots> = kf_apply (kf_comp_dependent \<EE>  \<FF>)\<close>
      by (metis (no_types, lifting) ext kf_comp_dependent_map_right_weak kf_eq_weak_def split_conv)
    finally show ?thesis
      by -
  qed
  moreover have \<open>cq_id Q o kf_apply (kf_comp_dependent \<EE> \<FF>) = kf_apply (kf_comp_dependent \<EE> \<FF>)\<close>
  proof -
    have \<open>cq_id Q o kf_apply (kf_comp_dependent \<EE> \<FF>) = kf_apply (kf_comp (kf_apply_qregister Q (kf_complete_measurement (range ket))) (kf_comp_dependent \<EE> \<FF>))\<close>
      by (simp add: cq_id_def km_complete_measurement_kf_complete_measurement km_apply_qregister_kf_apply qreg kf_comp_apply)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent (\<lambda>g. kf_comp (kf_apply_qregister Q (kf_complete_measurement (range ket))) (\<EE> g)) \<FF>)\<close>
      apply (rule sym)
      by (auto intro!: ext kf_apply_eqI kf_comp_dependent_comp_assoc_weak bdd\<EE>)
    also have \<open>\<dots> = kf_apply (kf_comp_dependent \<EE> \<FF>)\<close>
    proof -
      have \<open>cq_id Q o kf_apply (\<EE> x) = kf_apply (\<EE> x)\<close> if \<open>x \<in> kf_domain \<FF>\<close> for x
        using cq\<EE>[OF that]
        by (simp add: cq_map_id_left)
      then have \<open>kf_comp (kf_apply_qregister Q (kf_complete_measurement (range ket))) (\<EE> x) =\<^sub>k\<^sub>r \<EE> x\<close>
        if \<open>x \<in> kf_domain \<FF>\<close> for x
        apply (rule_tac kf_eq_weakI)
        using that by (simp add: kf_comp_apply qreg cq_id_def del: insert_iff
            flip: kf_apply_on_def km_apply_qregister_kf_apply km_complete_measurement_kf_complete_measurement)
      then show ?thesis
        by (auto intro!: ext kf_apply_eqI kf_comp_dependent_cong_weak bdd')
    qed
    finally show ?thesis
      by -
  qed
  ultimately show ?thesis
    by (simp add: is_cq_map_def)
qed

lemma classical_on_chain: 
  assumes \<open>classical_on Q t\<close>
  assumes \<open>iso_qregister \<lbrakk>R,S\<rbrakk>\<^sub>q\<close>
  shows \<open>classical_on (qregister_chain R Q) (apply_qregister_tc \<lbrakk>R,S\<rbrakk>\<^sub>q (tc_tensor t u))\<close>
proof (rule classical_on_def[THEN iffD2])
  have [iff]: \<open>qcompatible R S\<close>
    using assms(2) iso_qregister_def' by blast
  then have [iff]: \<open>qregister S\<close>
    using qcompatible_def by blast

  have \<open>cq_id (qregister_chain R Q) (apply_qregister_tc \<lbrakk>R, S\<rbrakk>\<^sub>q (tc_tensor t u))
        = km_apply_qregister (qregister_chain R Q) km_complete_measurement_ket (apply_qregister_tc \<lbrakk>R, S\<rbrakk>\<^sub>q (tc_tensor t u))\<close>
    by (simp add: cq_id_def)
  also have \<open>\<dots> = km_apply_qregister R (km_apply_qregister Q km_complete_measurement_ket) (apply_qregister_tc \<lbrakk>R, S\<rbrakk>\<^sub>q (tc_tensor t u))\<close>
    by (simp add: km_apply_qregister_chain)
  also have \<open>\<dots> = km_apply_qregister \<lbrakk>R,S\<rbrakk>\<^sub>q (km_tensor (km_apply_qregister Q km_complete_measurement_ket) id) (apply_qregister_tc \<lbrakk>R, S\<rbrakk>\<^sub>q (tc_tensor t u))\<close>
    by (simp add: km_apply_qregister_pair_tensor assms)
  also have \<open>\<dots> = apply_qregister_tc \<lbrakk>R,S\<rbrakk>\<^sub>q (km_tensor (km_apply_qregister Q km_complete_measurement_ket) id (tc_tensor t u))\<close>
    by (simp add: km_apply_qregister_apply_qregister_tc km_tensor_kraus_map assms)
  also have \<open>\<dots> = apply_qregister_tc \<lbrakk>R,S\<rbrakk>\<^sub>q (tc_tensor (km_apply_qregister Q km_complete_measurement_ket t) u)\<close>
    by (simp add: km_tensor_apply km_tensor_kraus_map_exists)
  also have \<open>\<dots> = apply_qregister_tc \<lbrakk>R,S\<rbrakk>\<^sub>q (tc_tensor (cq_id Q t) u)\<close>
    by (simp add: cq_id_def)
  also have \<open>\<dots> = apply_qregister_tc \<lbrakk>R,S\<rbrakk>\<^sub>q (tc_tensor t u)\<close>
    by (metis assms classical_on_def)
  finally show \<open>cq_id (qregister_chain R Q) (apply_qregister_tc \<lbrakk>R, S\<rbrakk>\<^sub>q (tc_tensor t u)) = apply_qregister_tc \<lbrakk>R, S\<rbrakk>\<^sub>q (tc_tensor t u)\<close>
    by -
qed


lemma classical_butterfly: \<open>classical_on qregister_id (tc_butterfly (ket c) (ket c))\<close>
  by (simp add: classical_on_def cq_id_def)


lemma classical_on_qFst_butterket[simp]: \<open>classical_on qFst (tc_tensor (tc_butterfly (ket c) (ket c)) \<rho>)\<close>
  using classical_on_chain[where u=\<rho> and R=qFst and S=qSnd, OF classical_butterfly[of c]]
  by simp


lemma is_cq_map_tendsto:
  assumes cq: \<open>\<forall>\<^sub>F x in F. is_cq_map Q (\<EE> x)\<close>
  assumes nontrivial: \<open>F \<noteq> \<bottom>\<close>
  assumes \<EE>lim: \<open>(\<EE> \<longlongrightarrow> \<FF>) F\<close>
  assumes kraus: \<open>kraus_map \<FF>\<close>
  shows \<open>is_cq_map Q \<FF>\<close>
proof -
  have \<open>(cq_id Q o \<FF> o cq_id Q) = \<FF>\<close>
  proof (rule ext)
    fix t :: \<open>('c ell2, 'c ell2) trace_class\<close>
    have cont: \<open>continuous_on UNIV (\<lambda>a. cq_id Q \<circ> a \<circ> cq_id Q)\<close>
      by (auto intro!: continuous_intros)
    from \<open>(\<EE> \<longlongrightarrow> \<FF>) F\<close>
    have \<open>((\<lambda>x. cq_id Q o (\<EE> x) o cq_id Q) \<longlongrightarrow> cq_id Q o \<FF> o cq_id Q) F\<close>
      apply (rule tendsto_compose_at_within[unfolded o_def, where S=UNIV])
      using cont
      by (auto simp: o_def continuous_on_def)
    then have \<open>(\<EE> \<longlongrightarrow> cq_id Q o \<FF> o cq_id Q) F\<close>
      apply (rule tendsto_cong[THEN iffD1, rotated])
      using cq unfolding is_cq_map_def
      apply (rule eventually_mono)
      by simp
    then have 1: \<open>((\<lambda>x. \<EE> x t) \<longlongrightarrow> (cq_id Q o \<FF> o cq_id Q) t) F\<close>
      by (simp add: tendsto_coordinatewise)
    from \<open>(\<EE> \<longlongrightarrow> \<FF>) F\<close>
    have 2: \<open>((\<lambda>x. \<EE> x t) \<longlongrightarrow> \<FF> t) F\<close>
      by (simp add: tendsto_coordinatewise)
    from nontrivial 1 2 show \<open>(cq_id Q o \<FF> o cq_id Q) t = \<FF> t\<close>
      by (rule tendsto_unique)
  qed
  with kraus
  show \<open>is_cq_map Q \<FF>\<close>
    using is_cq_map_def by blast
qed

lemma is_cq_map_sum:
  assumes cq: \<open>\<And>x. x \<in> A \<Longrightarrow> is_cq_map Q (\<EE> x)\<close>
  shows \<open>is_cq_map Q (\<Sum>x\<in>A. \<EE> x)\<close>
  using cq apply (induction A rule:infinite_finite_induct)
  by (auto simp: is_cq_map_0 func_plus is_cq_map_plus simp flip: zero_fun_apply)

lemma is_cq_map_has_sum:
  assumes cq: \<open>\<And>x. x \<in> A \<Longrightarrow> is_cq_map Q (\<EE> x)\<close>
  assumes \<EE>summable: \<open>km_summable \<EE> A\<close>
  assumes \<EE>sum: \<open>(\<EE> has_sum \<FF>) A\<close>
  shows \<open>is_cq_map Q \<FF>\<close>
proof -
  from \<EE>summable \<EE>sum
  have \<open>kraus_map \<FF>\<close>
    apply (rule kraus_map_has_sum[rotated])
    using cq is_cq_map_def by blast
  from \<EE>sum
  have \<open>(sum \<EE> \<longlongrightarrow> \<FF>) (finite_subsets_at_top A)\<close>
    by (simp add: has_sum_def)
  then show \<open>is_cq_map Q \<FF>\<close>
    apply (rule is_cq_map_tendsto[rotated 2])
    using \<open>kraus_map \<FF>\<close> assms
    by (auto intro!: eventually_finite_subsets_at_top_weakI is_cq_map_sum)
qed

lemma cq_id_qregister_pair:
  assumes \<open>qcompatible Q R\<close>
  shows \<open>cq_id \<lbrakk>Q,R\<rbrakk>\<^sub>q = cq_id Q o cq_id R\<close>
  unfolding cq_id_def
  apply (subst km_complete_measurement_ket_tensor[symmetric])
  apply (subst km_apply_qregister_pair_tensor)
  using assms by auto


lemma cq_id_qregister_chain:
  \<open>cq_id (qregister_chain Q R) = km_apply_qregister Q (cq_id R)\<close>
  by (simp add: cq_id_def km_apply_qregister_chain)


lemma cq_id_qregister_tensor: 
  \<open>cq_id (qregister_tensor Q R) = km_tensor (cq_id Q) (cq_id R)\<close>
proof -
  wlog [iff]: \<open>qregister Q\<close> \<open>qregister R\<close>
    using negation
    by (auto simp: cq_id_invalid non_qregister)
  show ?thesis
    apply (rule_tac eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
      apply simp 
     apply (simp add: km_tensor_kraus_map kraus_map_bounded_clinear) 
    by (simp add: qregister_tensor_pair cq_id_qregister_pair cq_id_qregister_chain
        km_apply_qregister_pair_tensor km_apply_qregister_qFst km_apply_qregister_qSnd km_tensor_apply
        km_tensor_kraus_map_exists)
qed

lemma is_cq_map_qregister_tensor:
  assumes \<open>is_cq_map Q \<EE>\<close>
  assumes \<open>is_cq_map R \<FF>\<close>
  shows \<open>is_cq_map (qregister_tensor Q R) (km_tensor \<EE> \<FF>)\<close>
proof (intro is_cq_map_def[THEN iffD2] conjI)
  from assms have [iff]: \<open>kraus_map \<EE>\<close>  \<open>kraus_map \<FF>\<close>
    using is_cq_map_def by auto
  then show \<open>kraus_map (km_tensor \<EE> \<FF>)\<close>
    by (meson km_tensor_kraus_map)
  have \<open>cq_id (qregister_tensor Q R) \<circ> km_tensor \<EE> \<FF> \<circ> cq_id (qregister_tensor Q R)
    = km_tensor (cq_id Q) (cq_id R) o km_tensor \<EE> \<FF> o km_tensor (cq_id Q) (cq_id R)\<close>
    by (simp add: cq_id_qregister_tensor)
  also have \<open>\<dots> = km_tensor (cq_id Q o \<EE> o cq_id Q) (cq_id R o \<FF> o cq_id R)\<close>
    by (simp add: km_tensor_compose_distrib km_tensor_kraus_map_exists kraus_map_comp)
  also have \<open>\<dots> = km_tensor \<EE> \<FF>\<close>
    by (metis assms(1,2) is_cq_map_def)
  finally show \<open>cq_id (qregister_tensor Q R) \<circ> km_tensor \<EE> \<FF> \<circ> cq_id (qregister_tensor Q R) = km_tensor \<EE> \<FF>\<close>
    by -
qed


lemma cq_id_empty_qregister[simp]: \<open>cq_id empty_qregister = id\<close>
  by (auto intro!: ext simp add: cq_id_def)


lemma is_cq_map_empty_qregister[simp]: \<open>is_cq_map empty_qregister \<EE> \<longleftrightarrow> kraus_map \<EE>\<close>
  by (simp add: is_cq_map_def)

lemma is_cq_map_qFst_chain:
  assumes [iff]: \<open>is_cq_map Q \<EE>\<close>
  assumes [iff]: \<open>kraus_map \<FF>\<close>
  shows \<open>is_cq_map (qregister_chain qFst Q) (km_tensor \<EE> \<FF>)\<close>
proof (intro is_cq_map_def[THEN iffD2] conjI)
  from assms have [iff]: \<open>kraus_map \<EE>\<close>
    using is_cq_map_def by auto
  with assms show \<open>kraus_map (km_tensor \<EE> \<FF>)\<close>
    by (meson km_tensor_kraus_map)
  have \<open>cq_id (qregister_chain qFst Q) \<circ> km_tensor \<EE> \<FF> \<circ> cq_id (qregister_chain qFst Q)
    = km_tensor (cq_id Q) id \<circ> km_tensor \<EE> \<FF> \<circ> km_tensor (cq_id Q) id\<close>
    by (simp add: cq_id_qregister_chain km_apply_qregister_qFst)
  also have \<open>\<dots> = km_tensor (cq_id Q o \<EE> o cq_id Q) \<FF>\<close>
    by (simp add: km_tensor_kraus_map_exists kraus_map_comp flip: km_tensor_compose_distrib)
  also have \<open>\<dots> = km_tensor \<EE> \<FF>\<close>
    by (metis assms(1,2) is_cq_map_def)
  finally show \<open>cq_id (qregister_chain qFst Q) \<circ> km_tensor \<EE> \<FF> \<circ> cq_id (qregister_chain qFst Q) = km_tensor \<EE> \<FF>\<close>
    by -
qed

lemma is_cq_map_qFst[intro!]:
  assumes \<open>is_cq_map qregister_id \<EE>\<close>
  assumes \<open>kraus_map \<FF>\<close>
  shows \<open>is_cq_map qFst (km_tensor \<EE> \<FF>)\<close>
  using is_cq_map_qFst_chain[OF assms]
  by simp

lemma is_cq_map_complete_measurement[iff]: 
  \<open>is_cq_map qregister_id km_complete_measurement_ket\<close>
  by (simp add: is_cq_map_def cq_id_def comp_def)


lemma cq_map_local_c_bot[simp]:
  assumes \<open>is_cq_map qFst E\<close>
  shows \<open>cq_map_local_c \<bottom> m E = E\<close>
proof (rule ext)
  fix \<rho>
  have [iff]: \<open>kraus_map E\<close>
    using assms is_cq_map_def by blast

  have \<open>cq_map_local_c \<bottom> m E \<rho> = cq_id \<lbrakk>#1\<rbrakk>\<^sub>q (E (cq_id \<lbrakk>#1\<rbrakk>\<^sub>q \<rho>))\<close>
    by (simp add: cq_map_local_c_def km_local_register_bot trace_tc_butterfly)
  also have \<open>\<dots> = E \<rho>\<close>
    using assms
    apply (simp add: is_cq_map_def o_def)
    by metis
  finally show \<open>cq_map_local_c \<bottom> m E \<rho> = E \<rho>\<close>
    by -
qed


lemma cq_map_local_q_bot:
  fixes E :: \<open>(('c\<times>'q) ell2, ('c\<times>'q) ell2) trace_class \<Rightarrow> (('c\<times>'q) ell2, ('c\<times>'q) ell2) trace_class\<close>
    and \<rho> :: \<open>('q ell2,'q ell2) trace_class\<close> and \<rho>' :: \<open>(('c\<times>'q) ell2, ('c\<times>'q) ell2) trace_class\<close>
  assumes \<open>kraus_map E\<close>
  shows \<open>cq_map_local_q \<bottom> \<rho> E \<rho>' = trace_tc \<rho> *\<^sub>C E \<rho>'\<close>
  by (simp add: cq_map_local_q_def km_local_register_bot assms trace_tc_tensor trace_tc_butterfly)

lemma cq_map_local_q_bot':
  assumes \<open>kraus_map E\<close>
  assumes \<open>trace_tc \<rho> = 1\<close>
  shows \<open>cq_map_local_q \<bottom> \<rho> E = E\<close>
  by (auto intro!: ext simp: cq_map_local_q_bot assms)

end

