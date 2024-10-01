theory CQ_Operators
  imports Kraus_Maps Registers2.Missing_Bounded_Operators Registers2.Quantum_Registers
    Registers2.Registers_Unsorted
begin


lift_definition apply_qregister_kraus_map :: \<open>('a,'b) qregister \<Rightarrow> ('a ell2, 'a ell2, 'x) kraus_family \<Rightarrow> ('b ell2, 'b ell2, 'x) kraus_family\<close> is
  \<open>\<lambda>(Q :: ('a,'b) qregister). image (\<lambda>(E,x). (apply_qregister Q E, x))\<close>
proof (rule CollectI, erule CollectE, rename_tac Q E)
  fix Q :: \<open>('a,'b) qregister\<close> and E :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2 \<times> 'x) set\<close>
  assume \<open>kraus_family E\<close>
  show \<open>kraus_family ((\<lambda>(E, y). (apply_qregister Q E, y)) ` E)\<close>
  proof -
    wlog [simp]: \<open>qregister Q\<close> goal \<open>kraus_family ((\<lambda>(E, y). (apply_qregister Q E, y)) ` E)\<close>
      using negation
      by (auto intro!: kraus_familyI_0 simp: non_qregister)
    from \<open>kraus_family E\<close> obtain B where B: \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>finite F\<close> and \<open>F \<subseteq> E\<close> for F
      by (auto simp: kraus_family_def bdd_above_def)
    have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> apply_qregister Q B\<close>
      if \<open>finite F\<close> and \<open>F \<subseteq> (\<lambda>(E, y). (apply_qregister Q E, y)) ` E\<close> for F
    proof -
      from that
      obtain G where FG: \<open>F = (\<lambda>(E, y). (apply_qregister Q E, y)) ` G\<close> and \<open>finite G\<close> and \<open>G \<subseteq> E\<close>
        by (meson finite_subset_image)
      have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) = (\<Sum>(E, x)\<in>(\<lambda>(E, y). (apply_qregister Q E, y)) ` G. E* o\<^sub>C\<^sub>L E)\<close>
        using FG by force
      also have \<open>\<dots> = (\<Sum>(E, x)\<in>G. apply_qregister Q (E* o\<^sub>C\<^sub>L E))\<close>
        apply (subst sum.reindex)
        by (auto intro!: inj_onI simp: case_prod_unfold qregister_compose apply_qregister_adj apply_qregister_inject')
      also have \<open>\<dots> = apply_qregister Q (\<Sum>(E, x)\<in>G. E* o\<^sub>C\<^sub>L E)\<close>
        apply (subst complex_vector.linear_sum[where f=\<open>apply_qregister Q\<close>]) 
        by (simp_all add: case_prod_beta)
      also have \<open>\<dots> \<le> apply_qregister Q B\<close>
        using \<open>qregister Q\<close> apply (rule apply_qregister_mono[THEN iffD2])
        using \<open>finite G\<close> and \<open>G \<subseteq> E\<close> by (rule B)
      finally show ?thesis
        by -
    qed
    then show ?thesis
      by (auto intro!: bdd_aboveI simp: kraus_family_def)
  qed
qed

definition classical_on :: \<open>('c,'a) qregister \<Rightarrow> ('a ell2, 'a ell2) trace_class \<Rightarrow> bool\<close> where
  \<open>classical_on C \<rho> \<longleftrightarrow> \<rho> = kraus_family_map (apply_qregister_kraus_map C (complete_measurement (range ket))) \<rho>\<close>

lift_definition cq_operator_at :: \<open>('c,'a) qregister \<Rightarrow> ('q,'a) qregister \<Rightarrow> ('a ell2, 'a ell2) trace_class \<Rightarrow> 'c \<Rightarrow> ('q ell2, 'q ell2) trace_class\<close> is
  \<open>\<lambda>C Q \<rho> c. sandwich (tensor_ell2_left (ket c)*) (apply_qregister (qregister_inv (qregister_pair C Q)) \<rho>)\<close>
proof (rule CollectI, erule CollectE, rename_tac C Q \<rho> c)
  fix C :: \<open>('c, 'a) qregister\<close> and Q :: \<open>('q, 'a) qregister\<close> and \<rho> :: \<open> 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and c :: 'c
  assume [iff]: \<open>trace_class \<rho>\<close>
  show \<open>trace_class (sandwich (tensor_ell2_left (ket c)*) *\<^sub>V apply_qregister (qregister_inv (qregister_pair C Q)) \<rho>)\<close>
  proof -
    wlog \<open>iso_qregister (qregister_pair C Q)\<close>
      using negation
      by (simp add: qregister_inv_non_iso_qregister)
    then have \<open>qregister_co_dim (qregister_inv (qregister_pair C Q)) = 1\<close>
      by (simp add: iso_qregister_co_dim iso_qregister_inv_iso)
    then have \<open>trace_class (apply_qregister (qregister_inv (qregister_pair C Q)) \<rho>)\<close>
      by (auto intro!: apply_qregister_trace_class iso_qregister_inv_iso)
    then show \<open>trace_class (sandwich (tensor_ell2_left (ket c)*) *\<^sub>V apply_qregister (qregister_inv (qregister_pair C Q)) \<rho>)\<close>
      by (rule trace_class_sandwich)
  qed
qed

lemma cq_operator_at_non_partition:
  assumes \<open>\<not> iso_qregister (qregister_pair C Q)\<close>
  shows \<open>cq_operator_at C Q \<rho> c = 0\<close>
  apply (transfer fixing: C Q)
  using assms
  by (simp add: qregister_inv_non_iso_qregister)


definition cq_operator_reconstruct :: \<open>('c,'a) qregister \<Rightarrow> ('q,'a) qregister \<Rightarrow> ('c \<Rightarrow> ('q ell2, 'q ell2) trace_class) \<Rightarrow> ('a ell2, 'a ell2) trace_class\<close> where
  \<open>cq_operator_reconstruct C Q \<rho> = (\<Sum>\<^sub>\<infinity>c. Abs_trace_class (apply_qregister (qregister_pair C Q) (selfbutter (ket c) \<otimes>\<^sub>o from_trace_class (\<rho> c))))\<close>

lemma cq_operator_at_summable:
  fixes C :: \<open>('c, 'a) qregister\<close> and Q :: \<open>('q, 'a) qregister\<close> and \<rho> :: \<open>('a ell2, 'a ell2) trace_class\<close> and c :: 'c
  shows \<open>cq_operator_at C Q \<rho> abs_summable_on UNIV\<close>
proof (transfer fixing: C Q, erule CollectE)
  fix \<rho> :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  define CQi \<rho>' where \<open>CQi = qregister_inv (qregister_pair C Q)\<close> and \<open>\<rho>' = Abs_trace_class (apply_qregister CQi \<rho>)\<close>
  assume \<open>trace_class \<rho>\<close>
  show \<open>(\<lambda>x. trace_norm (sandwich (tensor_ell2_left (ket x)*) *\<^sub>V apply_qregister CQi \<rho>)) summable_on UNIV\<close>
  proof -
    wlog \<open>iso_qregister (qregister_pair C Q)\<close>
      by (simp add: negation qregister_inv_non_iso_qregister CQi_def)
    then have dim: \<open>qregister_co_dim CQi = 1\<close>
      by (simp add: CQi_def iso_qregister_co_dim iso_qregister_inv_iso)
    with \<open>trace_class \<rho>\<close> 
    have CQi\<rho>: \<open>apply_qregister CQi \<rho> = from_trace_class \<rho>'\<close>
      by (simp add: \<rho>'_def Abs_trace_class_inverse apply_qregister_trace_class)
    then have rewrite_norm: \<open>trace_norm (sandwich (tensor_ell2_left (ket x)*) (from_trace_class \<rho>'))
      = norm (sandwich_tc (tensor_ell2_left (ket x)*) \<rho>')\<close> for x
      by (simp add: from_trace_class_sandwich_tc norm_trace_class.rep_eq)
    from partial_trace_abs_summable'[of \<open>sandwich_tc swap_ell2 \<rho>'\<close>]
    have \<open>(\<lambda>x. sandwich_tc (tensor_ell2_left (ket x)*) \<rho>') abs_summable_on UNIV\<close>
      by (auto intro!: simp: sandwich_tc_compose[symmetric, unfolded o_def, THEN fun_cong])
    then show ?thesis
      by (simp add: CQi\<rho> rewrite_norm)
  qed
qed


lemma cq_operator_at_bounded_clinear[bounded_clinear]:
  \<open>bounded_clinear (\<lambda>\<rho>. cq_operator_at C Q \<rho> c)\<close>
proof -
  wlog iso: \<open>iso_qregister (qregister_pair C Q)\<close>
    using cq_operator_at_non_partition[OF negation]
    by simp
  then have dim: \<open>qregister_co_dim (qregister_inv (qregister_pair C Q)) = 1\<close>
    using iso_qregister_co_dim iso_qregister_inv_iso by blast

  have 1: \<open>cq_operator_at C Q (x + y) c = cq_operator_at C Q x c + cq_operator_at C Q y c\<close> for x y
    apply (transfer' fixing: C Q c)
    by (simp add: apply_qregister_plus cblinfun.add_right)
  have 2: \<open>cq_operator_at C Q (r *\<^sub>C x) c = r *\<^sub>C cq_operator_at C Q x c\<close> for x r
    apply (transfer' fixing: C Q c)
    by (simp add: apply_qregister_scaleC cblinfun.scaleC_right)
  have 3: \<open>norm (cq_operator_at C Q x c) \<le> norm x * 1\<close> for x
  proof (transfer fixing: C Q c, erule CollectE)
    fix x :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
    assume \<open>trace_class x\<close>
    then have tc: \<open>trace_class (apply_qregister (qregister_inv (qregister_pair C Q)) x)\<close>
      by (auto intro!: apply_qregister_trace_class iso_qregister_inv_iso simp: dim)
    have \<open>trace_norm (sandwich (tensor_ell2_left (ket c)*) *\<^sub>V apply_qregister (qregister_inv (qregister_pair C Q)) x)
      \<le> trace_norm (apply_qregister (qregister_inv (qregister_pair C Q)) x)\<close>
      using trace_norm_sandwich[OF tc, of \<open>tensor_ell2_left (ket c)*\<close>]
      by simp
    also have \<open>\<dots> = trace_norm x\<close>
      apply (rule apply_iso_qregister_trace_norm)
      apply (auto intro!: iso_qregister_inv_iso simp: )
      using iso by blast
    also have \<open>\<dots> = trace_norm x * 1\<close>
      by simp
    finally show \<open>trace_norm (sandwich (tensor_ell2_left (ket c)*) *\<^sub>V apply_qregister (qregister_inv (qregister_pair C Q)) x) \<le> \<dots>\<close>
      by -
  qed
  from 1 2 3
  show ?thesis
    by (rule bounded_clinearI)
qed


lemma cq_operator_reconstruct_inv:
  fixes C :: \<open>('c, 'a) qregister\<close> and Q :: \<open>('q, 'a) qregister\<close> and \<rho> :: \<open>'c \<Rightarrow> ('q ell2, 'q ell2) trace_class\<close>
  assumes iso: \<open>iso_qregister (qregister_pair C Q)\<close>
  assumes sum_\<rho>: \<open>\<rho> abs_summable_on UNIV\<close>
  shows \<open>cq_operator_at C Q (cq_operator_reconstruct C Q \<rho>) = \<rho>\<close>
proof (rule ext)
  fix c
  define CQ CQi where \<open>CQ = qregister_pair C Q\<close> and \<open>CQi = qregister_inv CQ\<close>
  have dim: \<open>qregister_co_dim CQ = 1\<close>
    using CQ_def iso iso_qregister_co_dim by blast
  have *: \<open>cq_operator_at C Q (Abs_trace_class (apply_qregister CQ (selfbutter (ket d) \<otimes>\<^sub>o from_trace_class (\<rho> d)))) c
    = of_bool (c=d) *\<^sub>C \<rho> d\<close> for d
  proof (rule from_trace_class_inject[THEN iffD1])
    have \<open>from_trace_class (cq_operator_at C Q (Abs_trace_class (apply_qregister CQ (selfbutter (ket d) \<otimes>\<^sub>o from_trace_class (\<rho> d)))) c)
        = sandwich (tensor_ell2_left (ket c)*) (apply_qregister CQi (from_trace_class (Abs_trace_class (apply_qregister CQ (selfbutter (ket d) \<otimes>\<^sub>o from_trace_class (\<rho> d))))))\<close>
      by (simp add: cq_operator_at.rep_eq CQi_def CQ_def)
    also have \<open>\<dots> = sandwich (tensor_ell2_left (ket c)*) *\<^sub>V apply_qregister CQi (apply_qregister CQ (selfbutter (ket d) \<otimes>\<^sub>o from_trace_class (\<rho> d)))\<close>
      apply (subst Abs_trace_class_inverse)
      by (auto intro!: apply_qregister_trace_class trace_class_tensor iso simp: dim)
    also have \<open>\<dots> = sandwich (tensor_ell2_left (ket c)*) *\<^sub>V (selfbutter (ket d) \<otimes>\<^sub>o from_trace_class (\<rho> d))\<close>
      by (auto intro!: simp: CQi_def apply_qregister_inv_inverse iso CQ_def)
    also have \<open>\<dots> = from_trace_class (of_bool (c = d) *\<^sub>C \<rho> d)\<close>
      by (simp add: sandwich_tensor_ell2_left)
    finally show \<open>from_trace_class (cq_operator_at C Q (Abs_trace_class (apply_qregister CQ (selfbutter (ket d) \<otimes>\<^sub>o from_trace_class (\<rho> d)))) c) =
                  from_trace_class (of_bool (c = d) *\<^sub>C \<rho> d)\<close>
      by -
  qed
  have summable1: \<open>(\<lambda>d. Abs_trace_class (apply_qregister CQ (selfbutter (ket d) \<otimes>\<^sub>o from_trace_class (\<rho> d)))) summable_on UNIV\<close>
  proof -
    have tc1: \<open>trace_class (apply_qregister CQ (selfbutter (ket x) \<otimes>\<^sub>o from_trace_class t))\<close> for x t
      by (auto intro!: apply_qregister_trace_class trace_class_tensor simp: dim)
    from sum_\<rho> have \<open>(\<lambda>x. trace_norm (selfbutter (ket x) \<otimes>\<^sub>o from_trace_class (\<rho> x))) summable_on UNIV\<close>
      by (simp add: trace_norm_tensor trace_norm_butterfly flip: norm_trace_class.rep_eq)
    then have \<open>(\<lambda>x. trace_norm (apply_qregister CQ (selfbutter (ket x) \<otimes>\<^sub>o from_trace_class (\<rho> x)))) summable_on UNIV\<close>
      apply (subst apply_iso_qregister_trace_norm)
      by (simp_all add: iso CQ_def)
    then show ?thesis
      apply (rule_tac abs_summable_summable)
      by (simp add: eq_onp_def tc1 norm_trace_class.abs_eq)
  qed
  have \<open>cq_operator_at C Q (cq_operator_reconstruct C Q \<rho>) c
     = cq_operator_at C Q (\<Sum>\<^sub>\<infinity>d. Abs_trace_class (apply_qregister CQ (selfbutter (ket d) \<otimes>\<^sub>o from_trace_class (\<rho> d)))) c\<close>
    by (simp add: cq_operator_reconstruct_def CQ_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. cq_operator_at C Q (Abs_trace_class (apply_qregister CQ (selfbutter (ket d) \<otimes>\<^sub>o from_trace_class (\<rho> d)))) c)\<close>
    apply (subst infsum_bounded_linear[where h=\<open>\<lambda>\<rho>. cq_operator_at C Q \<rho> c\<close>])
      apply (simp add: bounded_clinear.bounded_linear cq_operator_at_bounded_clinear) 
     apply (rule summable1)
    by simp
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d::'c. of_bool (c = d) *\<^sub>C \<rho> d)\<close>
    by (simp add: * )
  also have \<open>\<dots> = \<rho> c\<close>
    apply (subst infsum_single[where i=c])
    by auto
  finally show \<open>cq_operator_at C Q (cq_operator_reconstruct C Q \<rho>) c = \<rho> c\<close>
    by -
qed

lemma cq_operator_reconstruct:
  assumes iso: \<open>iso_qregister (qregister_pair C Q)\<close>
  assumes cq: \<open>classical_on C \<rho>\<close>
  shows \<open>cq_operator_reconstruct C Q (cq_operator_at C Q \<rho>) = \<rho>\<close>
proof -
  define CQ CQi where \<open>CQ = qregister_pair C Q\<close> and \<open>CQi = qregister_inv CQ\<close>

  from iso
  have [simp]: \<open>qregister_co_dim CQ = 1\<close>
    using CQ_def iso_qregister_co_dim by blast

  have [simp]: \<open>qregister_co_dim CQi = 1\<close>
    by (simp add: CQ_def CQi_def assms(1) iso_qregister_co_dim iso_qregister_inv_iso)

  have \<open>cq_operator_reconstruct C Q (cq_operator_at C Q \<rho>)
        = (\<Sum>\<^sub>\<infinity>c. Abs_trace_class (apply_qregister CQ (selfbutter (ket c) \<otimes>\<^sub>o sandwich (tensor_ell2_left (ket c)*) *\<^sub>V apply_qregister CQi (from_trace_class \<rho>))))\<close>
    by (simp add: cq_operator_reconstruct_def cq_operator_at.rep_eq CQ_def CQi_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>c. sandwich_tc (apply_qregister C (selfbutter (ket c))) \<rho>)\<close>
    (is \<open>(\<Sum>\<^sub>\<infinity>c. ?lhs c) = (\<Sum>\<^sub>\<infinity>c. ?rhs c)\<close>)
  proof (rule infsum_cong)
    fix c
    have \<open>?lhs c
        = apply_qregister_tc CQ
                  (Abs_trace_class  (selfbutter (ket c) \<otimes>\<^sub>o sandwich (tensor_ell2_left (ket c)*) *\<^sub>V apply_qregister CQi (from_trace_class \<rho>)))\<close>
      apply (subst apply_qregister_tc.abs_eq)
       apply (simp add: apply_qregister_trace_class eq_onp_def trace_class_sandwich trace_class_tensor)
      by simp
    also have \<open>\<dots> = apply_qregister_tc CQ (tc_tensor (tc_butterfly (ket c) (ket c))
       (sandwich_tc (tensor_ell2_left (ket c)*) (Abs_trace_class (apply_qregister CQi (from_trace_class \<rho>)))))\<close>
      by (simp add: eq_onp_def apply_qregister_trace_class trace_class_sandwich
          flip: tc_butterfly.abs_eq tc_tensor.abs_eq sandwich_tc_Abs_trace_class)
    also have \<open>\<dots> = apply_qregister_tc CQ (tc_tensor (tc_butterfly (ket c) (ket c))
       (sandwich_tc (tensor_ell2_left (ket c)*) (apply_qregister_tc CQi (Abs_trace_class (from_trace_class \<rho>)))))\<close>
      apply (subst apply_qregister_tc.abs_eq)
      by (simp_all add: eq_onp_def)
    also have \<open>\<dots> = apply_qregister_tc CQ
     (tc_tensor (tc_butterfly (ket c) (ket c))
       (sandwich_tc (tensor_ell2_left (ket c)*) (apply_qregister_tc CQi \<rho>)))\<close>
      by (simp add: from_trace_class_inverse)
    also have \<open>\<dots> = apply_qregister_tc CQ (sandwich_tc (selfbutter (ket c) \<otimes>\<^sub>o id_cblinfun) (apply_qregister_tc CQi \<rho>))\<close>
    proof -
      have *: \<open>sandwich_tc (selfbutter (ket c) \<otimes>\<^sub>o id_cblinfun) (tc_tensor x (tc_butterfly a b)) =
       tc_tensor (tc_butterfly (ket c) (ket c)) (sandwich_tc (tensor_ell2_left (ket c)*) (tc_tensor x (tc_butterfly a b)))\<close>
        for x :: \<open>('a ell2, 'a ell2) trace_class\<close> and a b :: \<open>'e ell2\<close>
        apply (rule from_trace_class_inject[THEN iffD1])
        apply (simp add: from_trace_class_sandwich_tc tc_tensor.rep_eq tc_butterfly.rep_eq sandwich_tensor_ell2_left)
        by (simp add: sandwich_apply tensor_op_adjoint comp_tensor_op butterfly_comp_cblinfun cinner_adj_left tensor_op_cbilinear.scaleC_left tensor_op_cbilinear.scaleC_right)
      have \<open>sandwich_tc (selfbutter (ket c) \<otimes>\<^sub>o id_cblinfun) = (\<lambda>\<rho>. tc_tensor (tc_butterfly (ket c) (ket c))
       (sandwich_tc (tensor_ell2_left (ket c)*) \<rho>))\<close>
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
    also have \<open>\<dots> = sandwich_tc (apply_qregister CQ (selfbutter (ket c) \<otimes>\<^sub>o id_cblinfun)) (apply_qregister_tc CQ (apply_qregister_tc CQi \<rho>))\<close>
      by (rule apply_qregister_tc_sandwich)
    also have \<open>\<dots> = sandwich_tc (apply_qregister CQ (selfbutter (ket c) \<otimes>\<^sub>o id_cblinfun)) \<rho>\<close>
      using \<open>qregister_co_dim CQ = 1\<close> \<open>qregister_co_dim CQi = 1\<close> 
      by (smt (verit, ccfv_SIG) CQ_def CQi_def apply_qregister_inv_inverse apply_qregister_tc.rep_eq from_trace_class_inverse iso iso_qregister_inv_iso one_neq_zero)
    also have \<open>\<dots> = sandwich_tc (apply_qregister C (selfbutter (ket c))) \<rho>\<close>
      by (metis CQ_def apply_qregister_extend_pair_right assms(1) iso_qregister_def')
    finally show \<open>?lhs c = ?rhs c\<close>
      by -
  qed
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>range (\<lambda>x::'a. (apply_qregister C (selfbutter (ket x)), ket x)). sandwich_tc (fst E) \<rho>)\<close>
    apply (subst infsum_reindex)
    by (simp_all add: inj_def o_def) 
  also have \<open>\<dots> = kraus_family_map (apply_qregister_kraus_map C (complete_measurement (range ket))) \<rho>\<close>
    apply (transfer' fixing: \<rho> C)
    apply (simp add: image_image)
    apply transfer' (* Need to do this because the first transfer transferred a "ket x" that we didn't want transferred. *)
    by simp
  also have \<open>\<dots> = \<rho>\<close>
    by (metis cq classical_on_def)
  finally show ?thesis
    by -
qed


definition cq_map_from_measurement :: \<open>(('c1\<times>'q1) ell2, 'q2 ell2, 'c2) kraus_family \<Rightarrow> (('c1\<times>'q1) ell2, ('c2\<times>'q2) ell2, unit) kraus_family\<close> where
  \<open>cq_map_from_measurement E = kraus_family_flatten
      (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) E)\<close>

definition cq_map_from_pointwise :: \<open>('c1 \<Rightarrow> ('q1 ell2, 'q2 ell2, 'c2) kraus_family) \<Rightarrow> (('c1\<times>'q1) ell2, ('c2\<times>'q2) ell2, unit) kraus_family\<close> where
  \<open>cq_map_from_pointwise E = cq_map_from_measurement (kraus_family_map_outcome (\<lambda>(c,d). d) (kraus_family_comp_dependent E (kraus_map_partial_trace' (range ket))))\<close>


end

