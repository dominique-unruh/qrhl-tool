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

lemma bounded_clinear_cq_id[bounded_clinear, iff]: \<open>bounded_clinear (cq_id C)\<close>
  by (simp add: kraus_map_bounded_clinear)

lemma is_cq_map_0[iff]: \<open>is_cq_map Q 0\<close>
  apply (auto intro!: ext simp add: is_cq_map_def o_def)
  by (metis bounded_clinear_CBlinfun_apply bounded_clinear_cq_id cblinfun.real.zero_right)

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

lemma cq_map_from_kraus_family_invalid1[simp]: \<open>cq_map_from_kraus_family non_qregister Q \<EE> = 0\<close>
  by (simp add: cq_map_from_kraus_family_def[abs_def])

lemma cq_map_from_kraus_family_invalid2[simp]: \<open>cq_map_from_kraus_family C non_qregister \<EE> = 0\<close>
  by (simp add: cq_map_from_kraus_family_def[abs_def])

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
       apply (simp add: case_prod_unfold kf_norm_apply_qregister kf_norm_constant norm_tc_butterfly qregC)
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
        apply (simp add: kf_norm_apply_qregister qregQ bdd)
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
      by (auto intro!: injI)
    also have \<open>\<dots> =
     kf_comp_dependent (\<lambda>(_,_,c). kf_apply_qregister C (kf_constant (tc_butterfly (ket c) (ket c))))
     (kf_map (\<lambda>(a,c). (a,a,c)) (kf_comp_dependent (\<lambda>c. kf_apply_qregister Q (\<EE> c)) kf_cq_id))\<close>
      apply (subst kf_map_kf_map_inj_comp)
      by (auto intro!: injI simp: o_def case_prod_unfold)
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

end

