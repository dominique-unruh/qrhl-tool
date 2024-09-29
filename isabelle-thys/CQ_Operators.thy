theory CQ_Operators
  imports Kraus_Maps Registers2.Missing_Bounded_Operators Registers2.Quantum_Registers
begin


lemma apply_qregister_trace_class_transfer:
  assumes \<open>\<rho> \<noteq> 0\<close>
  assumes \<open>trace_class (apply_qregister Q \<rho>)\<close>
  assumes \<open>trace_class \<sigma>\<close>
  shows \<open>trace_class (apply_qregister Q \<sigma>)\<close>
proof -
  wlog \<open>qregister Q\<close>
    using negation by (simp add: non_qregister)
  from qregister_decomposition[OF this]
  have \<open>let 'c::type = qregister_decomposition_basis Q in
        trace_class (apply_qregister Q \<sigma>)\<close>
  proof with_type_mp
    with_type_case
    from with_type_mp.premise
    obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
      where \<open>unitary U\<close> and QU: \<open>Q = qregister_chain (transform_qregister U) qFst\<close>
      by auto
    let ?idc = \<open>id_cblinfun :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>
    have \<open>trace_class ?idc\<close>
    proof -
      from assms 
      have \<open>trace_class (sandwich U (\<rho> \<otimes>\<^sub>o ?idc))\<close>
        by (simp add: QU \<open>unitary U\<close> apply_qregister_fst transform_qregister.rep_eq)
      then have \<open>trace_class (sandwich (U*) (sandwich U (\<rho> \<otimes>\<^sub>o ?idc)))\<close>
        using trace_class_sandwich by blast
      then have \<open>trace_class (\<rho> \<otimes>\<^sub>o ?idc)\<close>
        by (simp add: unitaryD1 \<open>unitary U\<close> flip: cblinfun_apply_cblinfun_compose sandwich_compose)
      then show \<open>trace_class ?idc\<close>
        by (simp add: assms(1) trace_class_tensor_iff)
    qed
    then show \<open>trace_class (apply_qregister Q \<sigma>)\<close>
      by (auto intro!: trace_class_sandwich trace_class_tensor assms simp add: QU apply_qregister_fst transform_qregister.rep_eq \<open>unitary U\<close>)
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

definition qregister_co_dim :: \<open>('a,'b) qregister \<Rightarrow> real\<close> where
  \<open>qregister_co_dim Q = trace_norm (apply_qregister Q (selfbutter (ket undefined)))\<close>




(* definition trace_class_qregister :: \<open>('a,'b) qregister \<Rightarrow> bool\<close> where
  \<open>trace_class_qregister Q = trace_class (apply_qregister Q (selfbutter (ket undefined)))\<close> *)

lift_definition apply_qregister_tc :: \<open>('a,'b) qregister \<Rightarrow> ('a ell2, 'a ell2) trace_class \<Rightarrow> ('b ell2, 'b ell2) trace_class\<close> is
  \<open>\<lambda>Q. if qregister_co_dim Q \<noteq> 0 then apply_qregister Q else 0\<close>
proof (erule CollectE, rule CollectI, rename_tac Q t)
  fix Q :: \<open>('a, 'b) qregister\<close> and t :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assume \<open>trace_class t\<close>
  have \<open>trace_class (apply_qregister Q t)\<close> if \<open>qregister_co_dim Q \<noteq> 0\<close>
  proof -
    from that have norm: \<open>trace_norm (apply_qregister Q (selfbutter (ket undefined))) \<noteq> 0\<close>
      by (simp add: qregister_co_dim_def)
    then have \<open>trace_class (apply_qregister Q (selfbutter (ket undefined)))\<close>
      apply (rule_tac ccontr)
      by (simp_all add: trace_norm_def)
    then show \<open>trace_class (apply_qregister Q t)\<close>
      apply (rule apply_qregister_trace_class_transfer[rotated])
      using norm \<open>trace_class t\<close> by auto
  qed
  then show \<open>trace_class ((if qregister_co_dim Q \<noteq> 0 then apply_qregister Q else 0) t)\<close>
    by simp
qed

(* TODO move *)
lemma iso_qregister_decomposition:
  assumes \<open>iso_qregister X\<close>
  shows \<open>\<exists>U. unitary U \<and> apply_qregister X = sandwich U\<close>
proof -
  have \<open>iso_register (apply_qregister X)\<close>
    using assms
    unfolding iso_qregister_def iso_register_def
    apply (transfer' fixing: )
    by auto
  from iso_register_decomposition[OF this]
  show ?thesis
    apply transfer' by auto
qed

lemma trace_norm_sandwich_isometry: \<open>trace_norm (sandwich e t) = trace_norm t\<close> if \<open>isometry e\<close>
proof -
  have \<open>trace_norm (sandwich e t) = cmod (trace (abs_op (sandwich e t)))\<close>
    by simp
  also have \<open>\<dots> = cmod (trace (sandwich e (abs_op t)))\<close>
    by (metis (no_types, lifting) abs_op_def abs_op_id_on_pos abs_op_pos abs_op_square sandwich_apply_adj sandwich_arg_compose sandwich_pos that)
  also have \<open>\<dots> = cmod (trace (abs_op t))\<close>
    by (simp add: that)
  also have \<open>\<dots> = trace_norm t\<close>
    by simp
  finally show ?thesis
    by -
qed


lemma iso_qregister_co_dim: 
  assumes \<open>iso_qregister X\<close>
  shows \<open>qregister_co_dim X = 1\<close>
proof -
  from iso_qregister_decomposition[OF assms(1)]
  obtain U where \<open>unitary U\<close> and \<open>apply_qregister X = sandwich U\<close>
    by auto
  with assms show ?thesis
    by (simp add: trace_class_sandwich qregister_co_dim_def trace_butterfly trace_norm_sandwich_isometry trace_norm_butterfly)
qed

lemma apply_qregister_tc_codim0: \<open>qregister_co_dim Q = 0 \<Longrightarrow> apply_qregister_tc Q t = 0\<close>
  by (metis (mono_tags, lifting) apply_qregister_tc.rep_eq from_trace_class_inverse func_zero zero_trace_class_def)


(* TODO move *)
lemma apply_qregister_trace_class:
  assumes \<open>qregister_co_dim X \<noteq> 0\<close>
  assumes \<open>trace_class t\<close>
  shows \<open>trace_class (apply_qregister X t)\<close>
proof -
  from assms have norm: \<open>trace_norm (apply_qregister X (selfbutter (ket undefined))) \<noteq> 0\<close>
    by (simp add: qregister_co_dim_def)
  then have \<open>trace_class (apply_qregister X (selfbutter (ket undefined)))\<close>
    apply (rule_tac ccontr)
    by (simp_all add: trace_norm_def)
  then show \<open>trace_class (apply_qregister X t)\<close>
    apply (rule apply_qregister_trace_class_transfer[rotated])
    using norm \<open>trace_class t\<close> by auto
qed


(* TODO move *)
lemma apply_iso_qregister_trace_norm:
  assumes \<open>iso_qregister X\<close>
  shows \<open>trace_norm (apply_qregister X t) = trace_norm t\<close>
proof -
  from iso_qregister_decomposition[OF assms(1)]
  obtain U where \<open>unitary U\<close> and \<open>apply_qregister X = sandwich U\<close>
    by auto
  with assms show ?thesis
    by (metis apply_qregister_abs_op of_real_hom.injectivity trace_abs_op trace_sandwich_isometry unitary_isometry)
qed

lemma apply_qregister_tc_0[simp]: \<open>apply_qregister_tc Q 0 = 0\<close>
  apply (transfer' fixing: Q)
  by auto


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

(* TODO move *)
lemma qregister_inv_non_qregister[simp]: \<open>qregister_inv non_qregister = non_qregister\<close>
  apply transfer
  using [[simproc del: Laws_Quantum.compatibility_warn]]
  using iso_register_is_register by auto

lemma qregister_inv_non_iso_qregister: 
  assumes \<open>\<not> iso_qregister Q\<close>
  shows \<open>qregister_inv Q = non_qregister\<close>
  using assms
  apply transfer'
  by simp

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

lemma tensor_ell2_right_o_swap[simp]: \<open>(tensor_ell2_right \<psi>)* o\<^sub>C\<^sub>L swap_ell2 = (tensor_ell2_left \<psi>)*\<close>
  apply (rule tensor_ell2_extensionality)
  by simp

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


(* TODO move *)
(* TODO same for _right *)
lemma norm_tensor_ell2_left[simp]: \<open>norm (tensor_ell2_left \<psi>) = norm \<psi>\<close>
proof (rule norm_cblinfun_eqI)
  fix \<phi>
  show \<open>0 \<le> norm \<psi>\<close>
    by simp
  show \<open>norm \<psi> \<le> norm (tensor_ell2_left \<psi> *\<^sub>V ket undefined) / norm (ket undefined)\<close>
    by (simp add: norm_tensor_ell2)
  show \<open>norm (tensor_ell2_left \<psi> *\<^sub>V \<phi>) \<le> norm \<psi> * norm \<phi>\<close>
    by (simp add: norm_tensor_ell2)
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


lemma apply_qregister_inv_inverse:
  assumes \<open>iso_qregister Q\<close>
  shows \<open>apply_qregister (qregister_inv Q) (apply_qregister Q a) = a\<close>
  using assms
  apply transfer'
  using iso_register_is_register register_inj by (auto intro!: inv_f_f simp: )

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

lemma sandwich_tc_Abs_trace_class: \<open>sandwich_tc a (Abs_trace_class t) = Abs_trace_class (sandwich a t)\<close> if \<open>trace_class t\<close>
  by (metis Abs_trace_class_inverse from_trace_class_inject from_trace_class_sandwich_tc mem_Collect_eq that trace_class_sandwich)

(* TODO move *)
lemma sgn_ket[simp]: \<open>sgn (ket x) = ket x\<close>
  by (simp add: sgn_div_norm)

lemma apply_non_qregister_tc[simp]: \<open>apply_qregister_tc non_qregister x = 0\<close>
  apply transfer'
  by simp

lemma apply_qregister_sandwich:
  (* assumes \<open>qregister Q\<close> (* TODO remove *) *)
  shows \<open>apply_qregister Q (sandwich a b) = sandwich (apply_qregister Q a) (apply_qregister Q b)\<close>
  apply (cases \<open>qregister Q\<close>)
  using qregister.rep_eq register_sandwich apply blast
  by (simp add: non_qregister)


lemma apply_qregister_tc_sandwich:
  shows \<open>apply_qregister_tc Q (sandwich_tc a b) = sandwich_tc (apply_qregister Q a) (apply_qregister_tc Q b)\<close>
proof -
  wlog qreg: \<open>qregister Q\<close>
    using negation by (simp add: non_qregister)
  wlog dim: \<open>qregister_co_dim Q \<noteq> 0\<close> keeping qreg
    using negation by (simp add: apply_qregister_tc_codim0)
  show ?thesis
    using qreg
    apply (transfer' fixing: Q)
    by (simp add: dim apply_qregister_sandwich)
qed


lemma cq_operator_reconstruct:
(* TODO assms *)
  assumes iso: \<open>iso_qregister (qregister_pair C Q)\<close>
  assumes cq: \<open>classical_on C \<rho>\<close>
  shows \<open>cq_operator_reconstruct C Q (cq_operator_at C Q \<rho>) = \<rho>\<close>
proof -
  define CQ CQi where \<open>CQ = qregister_pair C Q\<close> and \<open>CQi = qregister_inv CQ\<close>

(*   obtain U where \<open>unitary U\<close> and CQ_U: \<open>apply_qregister (qregister_pair C Q) a = sandwich U a\<close> for a
    using iso_qregister_decomposition by force
  then have CQi_U: \<open>apply_qregister (qregister_inv (qregister_pair C Q)) a = sandwich (U* ) a\<close> for a
    by (smt (verit, ccfv_SIG) apply_qregister_inv_inverse assms cblinfun_apply_cblinfun_compose cblinfun_compose_id_right iso_qregister_decomposition iso_qregister_inv_iso sandwich_compose unitaryD2)
  have \<open>cq_operator_reconstruct C Q (cq_operator_at C Q \<rho>)
     = (\<Sum>\<^sub>\<infinity>c. Abs_trace_class (sandwich U *\<^sub>V selfbutter (ket c) \<otimes>\<^sub>o sandwich (tensor_ell2_left (ket c)* ) *\<^sub>V sandwich (U* ) *\<^sub>V from_trace_class \<rho>))\<close>
    by (simp add: cq_operator_reconstruct_def CQ_U cq_operator_at.rep_eq CQi_U)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>c. sandwich_tc U (tc_tensor (tc_butterfly (ket c) (ket c)) (sandwich_tc (tensor_ell2_left (ket c)* ) (sandwich_tc (U* ) \<rho>))))\<close>
    by (simp add: trace_class_tensor trace_class_sandwich eq_onp_def from_trace_class_inverse 
        flip: tc_tensor.abs_eq tc_butterfly.abs_eq sandwich_tc_Abs_trace_class) *)

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










(* ************ END ***************** *)



















(* definition \<open>cq_map_rel \<EE> \<FF> \<longleftrightarrow> (\<forall>x. kraus_family_norm (\<EE> x) \<le> 1 \<and> kraus_equivalent' (\<EE> x) (\<FF> x))\<close>
  for \<EE> \<FF> :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'cl2) kraus_family\<close> *)

(* lemma cq_map_rel_refl:
  assumes \<open>\<And>x. \<EE> x = \<FF> x\<close>
  assumes \<open>\<And>x. kraus_family_norm (\<EE> x) \<le> 1\<close>
  shows \<open>cq_map_rel \<EE> \<FF>\<close>
  using assms by (simp add: cq_map_rel_def) *)

definition cq_norm_raw :: \<open>('cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class) \<Rightarrow> real\<close> where
  \<open>cq_norm_raw \<rho> = (\<Sum>\<^sub>\<infinity>c. norm (\<rho> c))\<close>

lemma cq_norm_raw_0[simp]: \<open>cq_norm_raw (\<lambda>_. 0) = 0\<close>
  by (simp add: cq_norm_raw_def)

lemma cq_norm_raw_trace: 
  assumes \<open>\<And>c. \<rho> c \<ge> 0\<close>
  shows \<open>of_real (cq_norm_raw \<rho>) = (\<Sum>\<^sub>\<infinity>c. trace_tc (\<rho> c))\<close>
  using assms
  by (auto intro!: infsum_cong norm_tc_pos simp: cq_norm_raw_def simp flip: infsum_of_real)

typedef ('cl,'qu) cq_operator = \<open>{\<rho> :: 'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class. (\<forall>c. \<rho> c \<ge> 0) \<and> 
                          \<rho> abs_summable_on UNIV}\<close>
  apply (rule exI[of _ \<open>\<lambda>_. 0\<close>])
  by auto
setup_lifting type_definition_cq_operator

lift_definition fixed_cl_cq_operator :: \<open>'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class \<Rightarrow> ('cl,'qu) cq_operator\<close> is
  \<open>\<lambda>c (\<rho>::('qu ell2, 'qu ell2) trace_class) d. if \<rho> \<ge> 0 then of_bool (c=d) *\<^sub>R \<rho> else 0\<close>
proof (rename_tac c \<rho>, intro conjI allI)
  fix c d :: 'cl and \<rho> :: \<open>('qu ell2, 'qu ell2) trace_class\<close>
  show \<open>0 \<le> (if \<rho> \<ge> 0 then of_bool (c = d) *\<^sub>R \<rho> else 0)\<close>
    by simp
  show \<open>(\<lambda>d. if \<rho> \<ge> 0 then of_bool (c = d) *\<^sub>R \<rho> else 0) abs_summable_on UNIV\<close>
  proof (cases \<open>\<rho> \<ge> 0\<close>)
    case True
    have \<open>(\<lambda>d. of_bool (c = d) *\<^sub>R \<rho>) abs_summable_on UNIV\<close>
      apply (rule finite_nonzero_values_imp_summable_on)
      by auto
    with True show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by auto
  qed
qed

typedef ('cl1,'qu1,'cl2,'qu2) cq_map = \<open>{E :: 'cl1 \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'cl2) kraus_family. bdd_above (range (\<lambda>x. kraus_family_norm (E x)))}\<close>
  by (rule exI[of _ 0], simp)
setup_lifting type_definition_cq_map

lift_definition cq_map_id :: \<open>('cl,'qu,'cl,'qu) cq_map\<close> is 
  \<open>\<lambda>c. kraus_family_map_outcome (\<lambda>(). c) kraus_family_id\<close>
  by simp

lift_definition cq_map_apply :: \<open>('cl1,'qu1,'cl2,'qu2) cq_map \<Rightarrow> ('cl1,'qu1) cq_operator \<Rightarrow> ('cl2,'qu2) cq_operator\<close> is
  \<open>\<lambda>\<EE> \<rho> c. (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))\<close>
proof (rename_tac \<EE> \<rho>, intro conjI allI ext)
  fix \<EE> :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'cl2) kraus_family\<close>
    and \<rho> :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu1 ell2) trace_class\<close> and c :: 'cl2
  assume \<open>bdd_above (range (\<lambda>x. kraus_family_norm (\<EE> x)))\<close>
  then obtain N where norm_\<EE>: \<open>kraus_family_norm (\<EE> x) \<le> N\<close> for x
    by (auto simp: bdd_above_def)
  assume \<open>(\<forall>c. 0 \<le> \<rho> c) \<and> \<rho> abs_summable_on UNIV\<close>
  then have \<rho>_pos: \<open>0 \<le> \<rho> c\<close> and \<rho>_sum: \<open>\<rho> abs_summable_on UNIV\<close> for c
    by auto
  define R where \<open>R = (\<Sum>\<^sub>\<infinity>c. norm (\<rho> c))\<close>
  from \<rho>_pos
  show \<open>0 \<le> (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))\<close>
    by (auto intro!: infsum_nonneg_traceclass kraus_family_map'_pos)

  from \<rho>_pos
  have 9: \<open>trace_tc (kraus_family_map (\<EE> d) (\<rho> d)) \<le> kraus_family_norm (\<EE> d) * trace_tc (\<rho> d)\<close> for d
    by (smt (verit) Extra_Ordered_Fields.complex_of_real_cmod cmod_mono complex_of_real_nn_iff 
        kraus_family_map_bounded_pos abs_pos kraus_family_map_pos nn_comparable norm_tc_pos of_real_hom.hom_mult 
        of_real_hom.injectivity trace_tc_0 trace_tc_mono) 
  from \<rho>_pos have 10: \<open>\<dots>d \<le> N * trace_tc (\<rho> d)\<close> for d
    by (simp add: mult_right_mono norm_\<EE> trace_tc_pos)
  have 0: \<open>0 \<le> Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close> for c d
    by (metis Re_complex_of_real \<rho>_pos kraus_family_map'_pos norm_cblinfun_mono_trace_class norm_tc_pos norm_zero order_eq_refl)
  have 3: \<open>(\<Sum>\<^sub>\<infinity>c. kraus_family_map' {c} (\<EE> d) (\<rho> d)) = kraus_family_map (\<EE> d) (\<rho> d)\<close> for d
  proof -
    have \<open>(\<Sum>\<^sub>\<infinity>c. kraus_family_map' {c} (\<EE> d) (\<rho> d)) = (\<Sum>\<^sub>\<infinity>X\<in>range (\<lambda>c. {c}). kraus_family_map' X (\<EE> d) (\<rho> d))\<close>
      by (simp add: infsum_reindex o_def)
    also have \<open>\<dots> = kraus_family_map' (\<Union>(range (\<lambda>c. {c}))) (\<EE> d) (\<rho> d)\<close>
      apply (rule kraus_family_map'_union_infsum)
      by auto
    also have \<open>\<dots> = kraus_family_map (\<EE> d) (\<rho> d)\<close>
      by simp
    finally show ?thesis
      by -
  qed
  have 4: \<open>(\<lambda>c. kraus_family_map' {c} (\<EE> d) (\<rho> d)) summable_on UNIV\<close> for d
  proof -
    have \<open>(\<lambda>X. kraus_family_map' X (\<EE> d) (\<rho> d)) summable_on range (\<lambda>c. {c})\<close> for d
      apply (rule kraus_family_map'_union_summable_on)
      by auto
    then show ?thesis
      apply (rule summable_on_reindex[THEN iffD1, unfolded o_def, rotated])
      by simp
  qed
  have 16: \<open>bounded_linear (\<lambda>x. Re (trace_tc x))\<close> for x :: \<open>('qu ell2,'qu ell2) trace_class\<close>
    by (intro bounded_linear_compose[OF bounded_linear_Re] bounded_linear_intros)
  from 3 4 have 5: \<open>(\<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) = Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))\<close> for d
    apply (subst infsum_bounded_linear[where h=\<open>Re o trace_tc\<close>, unfolded o_def])
    using 16 by auto
  have 13: \<open>0 \<le> Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))\<close> for d
    by (metis Re_complex_of_real \<rho>_pos kraus_family_map_pos norm_cblinfun_mono_trace_class norm_tc_pos norm_zero order_eq_refl)
  from \<rho>_sum have 12:  \<open>(\<lambda>d. Re (trace_tc (\<rho> d))) summable_on UNIV\<close>
    by (meson \<rho>_pos norm_tc_pos_Re summable_on_cong)
  from 9 10 have 14: \<open>Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d))) \<le> N * Re (trace_tc (\<rho> d))\<close> for d
    using dual_order.trans Re_mono
    by (metis scaleR_complex.simps(1) scaleR_conv_of_real)
  have 6: \<open>(\<lambda>d. Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (rule summable_on_comparison_test[where f=\<open>\<lambda>d. N * Re (trace_tc (\<rho> d))\<close>])
    using 12 13 14 by (auto intro!: summable_on_cmult_right)
  have 29: \<open>(\<lambda>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close> for d
    apply (rule summable_on_bounded_linear[where h=\<open>\<lambda>x. Re (trace_tc x)\<close>])
    using 16 4 by auto
  have 18: \<open>(\<lambda>(d,c). Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on (UNIV \<times> UNIV)\<close>
    apply (rule summable_on_SigmaI[where g=\<open>\<lambda>d. \<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close>])
    using 0 5 6 29 by (auto intro!: has_sumI)
  have 21: \<open>(\<lambda>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close> for c
    using summable_on_SigmaD1[OF summable_on_swap[THEN iffD1, OF 18]]
    by auto
  have 22: \<open>(\<lambda>c. \<Sum>\<^sub>\<infinity>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (rule summable_on_Sigma_banach)
    apply (rule summable_on_swap[THEN iffD2])
    using 18 by simp
  have 36: \<open>norm (kraus_family_map' {c} (\<EE> d) (\<rho> d)) = Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close> for c d
    apply (rule norm_tc_pos_Re)
    by (simp add: \<rho>_pos kraus_family_map'_pos)
  from 36 have 35: \<open>(\<lambda>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)) abs_summable_on UNIV\<close> for c
    by (simp add: 36 21)
  from 35 have 34: \<open>(\<lambda>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)) summable_on UNIV\<close> for c
    by (rule abs_summable_summable)
  from 22 have 23: \<open>(\<lambda>c. Re (trace_tc (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (rule summable_on_cong[THEN iffD1, rotated])
    using 16 34 by (rule infsum_bounded_linear[unfolded o_def])
  from 23 \<rho>_pos show \<open>(\<lambda>c. \<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)) abs_summable_on UNIV\<close>
    by (simp add: infsum_nonneg_traceclass kraus_family_map'_pos norm_tc_pos_Re)
qed

(* lift_definition cq_map_apply :: \<open>('cl1,'qu1,'cl2,'qu2) cq_map \<Rightarrow> ('cl1,'qu1) cq_operator \<Rightarrow> ('cl2,'qu2) cq_operator\<close> is
  \<open>\<lambda>\<EE> \<rho> c. (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))\<close>
proof (rename_tac \<EE> \<EE>' \<rho>, intro conjI allI ext)
  fix \<EE> \<EE>' :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'cl2) kraus_family\<close>
  assume rel: \<open>cq_map_rel \<EE> \<EE>'\<close>
  then have norm_\<EE>: \<open>kraus_family_norm (\<EE> x) \<le> 1\<close> for x
    unfolding cq_map_rel_def by blast
  fix \<rho> :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu1 ell2) trace_class\<close> and c
  assume \<open>(\<forall>c. 0 \<le> \<rho> c) \<and> (\<lambda>c. trace_tc (\<rho> c)) summable_on UNIV \<and> cq_norm_raw \<rho> \<le> 1\<close>
  then have \<rho>_pos: \<open>0 \<le> \<rho> c\<close> and \<rho>_sum: \<open>(\<lambda>c. trace_tc (\<rho> c)) summable_on UNIV\<close> and \<rho>_leq1: \<open>cq_norm_raw \<rho> \<le> 1\<close> for c
    by auto
  from \<rho>_pos
  show \<open>0 \<le> (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))\<close>
    by (auto intro!: infsum_nonneg_traceclass kraus_family_map'_pos)

  from \<rho>_pos
  have 9: \<open>trace_tc (kraus_family_map (\<EE> d) (\<rho> d)) \<le> kraus_family_norm (\<EE> d) * trace_tc (\<rho> d)\<close> for d
    by (smt (verit) Extra_Ordered_Fields.complex_of_real_cmod cmod_mono complex_of_real_nn_iff 
        kraus_family_map_bounded_pos abs_pos kraus_family_map_pos nn_comparable norm_tc_pos of_real_hom.hom_mult 
        of_real_hom.injectivity trace_tc_0 trace_tc_mono) 
  from \<rho>_pos have 10: \<open>\<dots>d \<le> trace_tc (\<rho> d)\<close> for d
    by (smt (verit, del_insts) Rings.mult_sign_intros(1) cmod_Re complex_of_real_leq_1_iff complex_of_real_nn_iff kraus_family_norm_geq0 less_eq_complex_def mult_left_le_one_le norm_\<EE> norm_ge_zero norm_mult norm_one trace_tc_pos)
  have 0: \<open>0 \<le> Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close> for c d
    by (metis Re_complex_of_real \<rho>_pos kraus_family_map'_pos norm_cblinfun_mono_trace_class norm_tc_pos norm_zero order_eq_refl)
  have 3: \<open>(\<Sum>\<^sub>\<infinity>c. kraus_family_map' {c} (\<EE> d) (\<rho> d)) = kraus_family_map (\<EE> d) (\<rho> d)\<close> for d
  proof -
    have \<open>(\<Sum>\<^sub>\<infinity>c. kraus_family_map' {c} (\<EE> d) (\<rho> d)) = (\<Sum>\<^sub>\<infinity>X\<in>range (\<lambda>c. {c}). kraus_family_map' X (\<EE> d) (\<rho> d))\<close>
      by (simp add: infsum_reindex o_def)
    also have \<open>\<dots> = kraus_family_map' (\<Union>(range (\<lambda>c. {c}))) (\<EE> d) (\<rho> d)\<close>
      apply (rule kraus_family_map'_union_infsum)
      by auto
    also have \<open>\<dots> = kraus_family_map (\<EE> d) (\<rho> d)\<close>
      by simp
    finally show ?thesis
      by -
  qed
  have 4: \<open>(\<lambda>c. kraus_family_map' {c} (\<EE> d) (\<rho> d)) summable_on UNIV\<close> for d
  proof -
    have \<open>(\<lambda>X. kraus_family_map' X (\<EE> d) (\<rho> d)) summable_on range (\<lambda>c. {c})\<close> for d
      apply (rule kraus_family_map'_union_summable_on)
      by auto
    then show ?thesis
      apply (rule summable_on_reindex[THEN iffD1, unfolded o_def, rotated])
      by simp
  qed
  have 16: \<open>bounded_linear (\<lambda>x. Re (trace_tc x))\<close> for x :: \<open>('qu ell2,'qu ell2) trace_class\<close>
    by (intro bounded_linear_compose[OF bounded_linear_Re] bounded_linear_intros)
  from 3 4 have 5: \<open>(\<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) = Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))\<close> for d
    apply (subst infsum_bounded_linear[where h=\<open>Re o trace_tc\<close>, unfolded o_def])
    using 16 by auto
  have 13: \<open>0 \<le> Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))\<close> for d
    by (metis Re_complex_of_real \<rho>_pos kraus_family_map_pos norm_cblinfun_mono_trace_class norm_tc_pos norm_zero order_eq_refl)
  from \<rho>_sum   have 12:  \<open>(\<lambda>d. Re (trace_tc (\<rho> d))) summable_on UNIV\<close>
    using summable_on_Re by blast
  from 9 10 have 14: \<open>Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d))) \<le> Re (trace_tc (\<rho> d))\<close> for d
    apply (auto intro!: Re_mono)
    using basic_trans_rules(23) by blast
  have 6: \<open>(\<lambda>d. Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (rule summable_on_comparison_test[where f=\<open>\<lambda>d. Re (trace_tc (\<rho> d))\<close>])
    using 12 13 14 by auto
  from 6 have 11: \<open>(\<Sum>\<^sub>\<infinity>d. Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))) \<le> (\<Sum>\<^sub>\<infinity>d. Re (trace_tc (\<rho> d)))\<close>
    apply (rule infsum_mono)
    using 12 14 by auto
  have 28: \<open>norm (\<rho> d) = Re (trace_tc (\<rho> d))\<close> for d
    by (metis Re_complex_of_real \<rho>_pos norm_tc_pos)
  have 27: \<open>\<rho> summable_on UNIV\<close>
    apply (rule abs_summable_summable)
    using 12 28 by auto
  have 15: \<open>(\<Sum>\<^sub>\<infinity>d. Re (trace_tc (\<rho> d))) \<le> 1\<close>
    apply (subst infsum_bounded_linear[where h=\<open>Re o trace_tc\<close>, unfolded o_def])
    using 16 27 28 \<rho>_sum \<rho>_leq1 \<rho>_pos
      apply auto
    by (smt (verit) Infinite_Sum.infsum_nonneg_complex abs_summable_on_comparison_test cmod_mono complex_Re_le_cmod infsum_Re infsum_cong norm_infsum_bound norm_one summable_on_iff_abs_summable_on_complex trace_tc_norm trace_tc_pos)
  from 5 6 have 2: \<open>(\<lambda>d. \<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    by simp
  have 17: \<open>(\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) \<le> 1\<close>
    using 5 15 11
    by auto
  have 29: \<open>(\<lambda>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close> for d
    apply (rule summable_on_bounded_linear[where h=\<open>\<lambda>x. Re (trace_tc x)\<close>])
    using 16 4 by auto
  have 18: \<open>(\<lambda>(d,c). Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on (UNIV \<times> UNIV)\<close>
    apply (rule summable_on_SigmaI[where g=\<open>\<lambda>d. \<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close>])
    using 0 5 6 29 by (auto intro!: has_sumI)
  have 21: \<open>(\<lambda>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close> for c
    using summable_on_SigmaD1[OF summable_on_swap[THEN iffD1, OF 18]]
    by auto
  have 22: \<open>(\<lambda>c. \<Sum>\<^sub>\<infinity>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (rule summable_on_Sigma_banach)
    apply (rule summable_on_swap[THEN iffD2])
    using 18 by simp
  have 20: \<open>(\<lambda>(c, d). Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (subst asm_rl[of \<open>UNIV = UNIV \<times> UNIV\<close>], simp)
    apply (rule summable_on_SigmaI[where g=\<open>\<lambda>c. \<Sum>\<^sub>\<infinity>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close>])
    using 21 22 0 by (auto intro!: has_sum_infsum)
  from 17 18 20 have 19: \<open>(\<Sum>\<^sub>\<infinity>c. \<Sum>\<^sub>\<infinity>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) \<le> 1\<close>
    apply (subst infsum_swap_banach)
    by auto
  have 36: \<open>norm (kraus_family_map' {c} (\<EE> d) (\<rho> d)) = Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close> for c d
    apply (rule norm_tc_pos_Re)
    by (simp add: \<rho>_pos kraus_family_map'_pos)
  from 36 have 35: \<open>(\<lambda>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)) abs_summable_on UNIV\<close> for c
    by (simp add: 36 21)
  from 35 have 34: \<open>(\<lambda>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)) summable_on UNIV\<close> for c
    by (rule abs_summable_summable)
  from 22 have 23: \<open>(\<lambda>c. Re (trace_tc (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (rule summable_on_cong[THEN iffD1, rotated])
    using 16 34 by (rule infsum_bounded_linear[unfolded o_def])
  have 25: \<open>(\<Sum>\<^sub>\<infinity>c. \<Sum>\<^sub>\<infinity>d. trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d))) \<ge> 0\<close>
    by (auto intro!: infsum_nonneg_complex trace_tc_pos kraus_family_map'_pos \<rho>_pos)
  from 23 show \<open>(\<lambda>c. trace_tc (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))) summable_on UNIV\<close>
    apply (rewrite at \<open>trace_tc _\<close> of_real_Re[symmetric])
    by (auto intro!: nonnegative_complex_is_real summable_on_bounded_linear[where h=of_real]
        bounded_linear_of_real trace_tc_pos  infsum_nonneg_traceclass kraus_family_map'_pos \<rho>_pos)
  have 26: \<open>(\<Sum>\<^sub>\<infinity>c. Re (trace_tc (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)))) \<le> 1\<close>
    apply (subst infsum_bounded_linear[OF 16, symmetric, unfolded o_def])
    using 19 34 by auto
  from 26 show \<open>(\<Sum>\<^sub>\<infinity>c. trace_tc (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))) \<le> 1\<close>
    apply (rewrite at \<open>trace_tc _\<close> of_real_Re[symmetric])
    by (auto intro!: nonnegative_complex_is_real summable_on_bounded_linear[where h=of_real]
        bounded_linear_of_real trace_tc_pos  infsum_nonneg_traceclass kraus_family_map'_pos \<rho>_pos
        simp: infsum_of_real )
  from rel
  show \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)) = (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE>' d) (\<rho> d))\<close>
    by (auto intro!: kraus_family_map'_eqI infsum_cong simp: cq_map_rel_def)
qed
 *)

lift_definition cq_map_seq :: \<open>('cl1,'qu1,'cl2,'qu2) cq_map \<Rightarrow> ('cl2,'qu2,'cl3,'qu3) cq_map \<Rightarrow> ('cl1,'qu1,'cl3,'qu3) cq_map\<close>
  is \<open>\<lambda>\<EE> \<FF> c. kraus_family_map_outcome snd (kraus_family_comp_dependent \<FF> (\<EE> c))\<close>
proof (rename_tac \<EE> \<FF>)
  fix \<EE> :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'cl2) kraus_family\<close>
  fix \<FF> :: \<open>'cl2 \<Rightarrow> ('qu2 ell2, 'qu3 ell2, 'cl3) kraus_family\<close>
  assume asms: \<open>bdd_above (range (\<lambda>x. kraus_family_norm (\<EE> x)))\<close> \<open>bdd_above (range (\<lambda>x. kraus_family_norm (\<FF> x)))\<close>
  then obtain F where F1: \<open>kraus_family_norm (\<FF> x) \<le> F\<close> for x
    by (auto intro!: simp: bdd_above_def)
  from kraus_family_norm_geq0 this have \<open>F \<ge> 0\<close>
    by (rule order_trans)
  from asms obtain E where E1: \<open>kraus_family_norm (\<EE> x) \<le> E\<close> for x
    by (auto intro!: simp: bdd_above_def)
  have \<open>kraus_family_norm (kraus_family_comp_dependent \<FF> (\<EE> x)) \<le> F * kraus_family_norm (\<EE> x)\<close> for x
    apply (rule kraus_family_comp_dependent_norm)
    by (simp add: F1)
  also have \<open>\<dots>x \<le> F * E\<close> for x
    by (intro mult_left_mono E1 \<open>F \<ge> 0\<close>)
  finally have 1: \<open>kraus_family_norm (kraus_family_comp_dependent \<FF> (\<EE> x)) \<le> F * E\<close> for x
    by simp
  then show \<open>bdd_above (range (\<lambda>x. kraus_family_norm (kraus_family_map_outcome snd (kraus_family_comp_dependent \<FF> (\<EE> x)))))\<close>
    by (auto intro!: bdd_aboveI simp: kraus_family_map_outcome_norm)
qed

lift_definition cq_map_equiv :: \<open>('c1,'q1,'c2,'q2) cq_map \<Rightarrow> ('c1,'q1,'c2,'q2) cq_map \<Rightarrow> bool\<close> is
  \<open>\<lambda>E F. \<forall>x. kraus_equivalent' (E x) (F x)\<close>.

lemma cq_map_equiv_ext: \<open>cq_map_equiv s t \<longleftrightarrow> cq_map_apply s = cq_map_apply t\<close>
  for s t :: \<open>('c1,'q1,'c2,'q2) cq_map\<close>
proof (intro iffI ext)
  fix \<rho> :: \<open>('c1, 'q1) cq_operator\<close>
  assume \<open>cq_map_equiv s t\<close>
  then have \<open>kraus_equivalent' (Rep_cq_map s x) (Rep_cq_map t x)\<close> for x
    by (simp add: cq_map_equiv_def)
  then show \<open>cq_map_apply s \<rho> = cq_map_apply t \<rho>\<close>
    apply transfer'
    by (intro ext infsum_cong kraus_family_map'_eqI)
next
  assume \<open>cq_map_apply s = cq_map_apply t\<close>
  then have *: \<open>Rep_cq_operator (cq_map_apply s \<rho>) = Rep_cq_operator (cq_map_apply t \<rho>)\<close> for \<rho>
    by simp
  (* then have \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (Rep_cq_map s d) (\<rho> d)) = (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (Rep_cq_map t d) (\<rho> d))\<close> for c *)
  have \<open>kraus_equivalent' (Rep_cq_map s x) (Rep_cq_map t x)\<close> for x
  proof (rule kraus_equivalent'I)
    fix c :: 'c2 and \<rho> :: \<open>('q1 ell2, 'q1 ell2) trace_class\<close>
    assume [simp]: \<open>\<rho> \<ge> 0\<close>
    note *[of \<open>fixed_cl_cq_operator x \<rho>\<close>]
    then have **: \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (Rep_cq_map s d) (of_bool (x = d) *\<^sub>R \<rho>))
             = (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (Rep_cq_map t d) (of_bool (x = d) *\<^sub>R \<rho>))\<close>
      apply (simp add: cq_map_apply.rep_eq fixed_cl_cq_operator.rep_eq)
      by meson
    show \<open>kraus_family_map' {c} (Rep_cq_map s x) \<rho> = kraus_family_map' {c} (Rep_cq_map t x) \<rho>\<close>
      using **
      apply (subst (asm) infsum_single[where i=x])
       apply simp
      apply (subst (asm) infsum_single[where i=x])
       apply simp
      by simp
  qed
  then show \<open>cq_map_equiv s t\<close>
    using cq_map_equiv.rep_eq by blast
qed

lemma cq_map_eqI:
  assumes \<open>\<And>\<rho>. cq_map_apply s \<rho> = cq_map_apply t \<rho>\<close>
  shows \<open>cq_map_equiv s t\<close>
  using assms by (auto simp: cq_map_equiv_ext)


lemma cq_map_apply_id[simp]: \<open>cq_map_apply cq_map_id \<rho> = \<rho>\<close>
proof transfer'
  fix \<rho> :: \<open>'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class\<close>
  have inj: \<open>inj_on (\<lambda>(). x) X\<close> for x :: 'cl and X
    by (simp add: inj_onI)
  have [simp]: \<open>(\<lambda>(). c) -` {c} = UNIV\<close> for c :: 'cl
    using unit.simps(1) by force
  have [simp]: \<open>(\<lambda>(). j) -` {c} = {}\<close> if \<open>j \<noteq> c\<close> for j c :: 'cl
    by (metis (mono_tags, lifting) CARD_1_UNIV UNIV_witness inj inj_vimage_singleton old.unit.case subset_singletonD that vimage_singleton_eq)
  have \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome (\<lambda>(). d) kraus_family_id) (\<rho> d)) = \<rho> c\<close> for c
    apply (subst infsum_single[where i=c])
    by (auto intro!: simp: kraus_family_map'_map_outcome)
  then show \<open>(\<lambda>c. \<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome (\<lambda>(). d) kraus_family_id) (\<rho> d)) = \<rho>\<close>
    by auto
qed

lemma cq_map_apply_seq: \<open>cq_map_apply (cq_map_seq s t) \<rho> = cq_map_apply t (cq_map_apply s \<rho>)\<close>
proof (transfer, intro ext)
  fix s :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'cl2) kraus_family\<close>
    and t :: \<open>'cl2 \<Rightarrow> ('qu2 ell2, 'qu3 ell2, 'cl3) kraus_family\<close>
    and \<rho> :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu1 ell2) trace_class\<close> and c :: 'cl3
  assume assms: \<open>(\<forall>c. 0 \<le> \<rho> c) \<and> \<rho> abs_summable_on UNIV\<close>
  assume bdd_s: \<open>bdd_above (range (\<lambda>x. kraus_family_norm (s x)))\<close>
  then obtain S where S: \<open>kraus_family_norm (s x) \<le> S\<close> for x
    by (auto intro!: simp: bdd_above_def)
  assume bdd_t: \<open>bdd_above (range (\<lambda>x. kraus_family_norm (t x)))\<close>
  then obtain T where T: \<open>kraus_family_norm (t x) \<le> T\<close> for x
    by (auto intro!: simp: bdd_above_def)
  have [simp]: \<open>T \<ge> 0\<close>
    using kraus_family_norm_geq0 T
    by (rule order_trans)
  have inj: \<open>inj_on fst (Set.filter (\<lambda>(E, x). x = f) X)\<close> for X f
    by (auto intro!: inj_onI)
  from bdd_t have bdd': \<open>bdd_above (range (kraus_family_norm \<circ> (\<lambda>e. kraus_family_filter (\<lambda>f. f = c) (t e))))\<close>
    apply (rule bdd_above_mono2)
    by (auto simp: kraus_family_norm_filter)
  have \<rho>_abs: \<open>\<rho> abs_summable_on UNIV\<close>
    by (smt (verit) assms complex_Re_le_cmod norm_tc_pos_Re summable_on_cong summable_on_iff_abs_summable_on_complex trace_tc_norm)

  have summ2: \<open>(\<lambda>d. kraus_family_map' {f} (s d) (\<rho> d)) summable_on UNIV\<close> for f
  proof (rule abs_summable_summable, rule abs_summable_on_comparison_test)
    from \<rho>_abs show \<open>(\<lambda>d. S *\<^sub>R \<rho> d) abs_summable_on UNIV\<close>
      by blast
    fix d
    have \<open>norm (kraus_family_map' {f} (s d) (\<rho> d)) \<le> kraus_family_norm (kraus_family_filter (\<lambda>x. x = f) (s d)) * norm (\<rho> d)\<close>
      using assms by (auto intro!: kraus_family_map_bounded_pos simp add: kraus_family_map'_def)
    also have \<open>\<dots> \<le> S * norm (\<rho> d)\<close>
      apply (rule mult_right_mono)
      using S kraus_family_norm_filter[of \<open>\<lambda>x. x = f\<close> \<open>s d\<close>]
       apply (auto intro!: simp: )
      by (smt (verit, del_insts))
    also have \<open>\<dots> = norm (S *\<^sub>R \<rho> d)\<close>
      by (smt (verit, del_insts) S kraus_family_norm_geq0 norm_scaleR)
    finally show \<open>norm (kraus_family_map' {f} (s d) (\<rho> d)) \<le> norm (S *\<^sub>R \<rho> d)\<close>
      by -
  qed
  have summ3: \<open>(\<lambda>F. sandwich_tc F (\<rho> c)) summable_on {F. (F, f) \<in> Rep_kraus_family (s c)}\<close> for c f
  proof -
    have *: \<open>(\<lambda>x. fst x) ` Set.filter (\<lambda>Ff. snd Ff = f) (Rep_kraus_family (s c))
        = {F. (F, f) \<in> Rep_kraus_family (s c)}\<close>
      by (auto intro!: simp: image_iff Bex_def)
    from kraus_family_map_summable[of _ \<open>s c\<close>]
    have \<open>(\<lambda>Ff. sandwich_tc (fst Ff) (\<rho> c)) summable_on Rep_kraus_family (s c)\<close>
      by (simp add: case_prod_unfold)
    then have \<open>(\<lambda>Ff. sandwich_tc (fst Ff) (\<rho> c)) summable_on Set.filter (\<lambda>Ff. snd Ff = f) (Rep_kraus_family (s c))\<close>
      apply (rule summable_on_subset_banach)
      by auto
    then show ?thesis
      apply (subst (asm) summable_on_reindex[unfolded o_def, symmetric, where h=fst])
      by (auto intro!: inj_onI simp: * )
  qed
  have summ4: \<open>(\<lambda>y. kraus_family_map' {c} (t y) (kraus_family_map' {y} (s d) (\<rho> d))) summable_on UNIV\<close> for d
  proof -
    have 1: \<open>(\<lambda>f. T *\<^sub>R kraus_family_map' {f} (s d) (\<rho> d)) abs_summable_on UNIV\<close>
    proof -
      have \<open>(\<lambda>X. kraus_family_map' X (s d) (\<rho> d)) summable_on range (\<lambda>f. {f})\<close>
        apply (rule kraus_family_map'_union_summable_on)
        by auto
      then have \<open>(\<lambda>f. kraus_family_map' {f} (s d) (\<rho> d)) summable_on UNIV\<close>
        apply (subst (asm) summable_on_reindex)
        by (simp_all add: o_def)
      then show ?thesis
        apply (intro summable_abs_summable_tc scaleR_nonneg_nonneg kraus_family_map'_pos)
        using assms by auto
    qed
    have 2: \<open>norm (kraus_family_map' {c} (t f) (kraus_family_map' {f} (s d) (\<rho> d)))
         \<le> norm (T *\<^sub>R kraus_family_map' {f} (s d) (\<rho> d))\<close> for f
    proof -
      have \<open>norm (kraus_family_map' {c} (t f) (kraus_family_map' {f} (s d) (\<rho> d)))
        \<le> kraus_family_norm (kraus_family_filter (\<lambda>x. x\<in>{c}) (t f)) * norm (kraus_family_map' {f} (s d) (\<rho> d))\<close>
        using assms
        by (auto intro!: kraus_family_map_bounded_pos
            simp: kraus_family_map'_def kraus_family_map_pos)
      also have \<open>\<dots> \<le> T * norm (kraus_family_map' {f} (s d) (\<rho> d))\<close>
        apply (rule mult_right_mono)
        using T
         apply (smt (verit, ccfv_threshold) kraus_family_norm_filter)
        by simp
      also have \<open>\<dots> = norm (T *\<^sub>R kraus_family_map' {f} (s d) (\<rho> d))\<close>
        by (smt (verit) T kraus_family_norm_geq0 norm_scaleR)
      finally show ?thesis
        by simp
    qed
    show ?thesis
      apply (rule abs_summable_summable)
      using 1 2 by (rule abs_summable_on_comparison_test)
  qed

  have \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome snd (kraus_family_comp_dependent t (s d))) (\<rho> d))
     = (\<Sum>\<^sub>\<infinity>d. kraus_family_map (kraus_family_filter (\<lambda>(e, f). f=c \<and> True) (kraus_family_comp_dependent t (s d))) (\<rho> d))\<close>
    by (simp add: kraus_family_map'_def kraus_family_filter_map_outcome case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. kraus_family_map (kraus_family_comp_dependent (\<lambda>e. kraus_family_filter (\<lambda>f. f = c) (t e)) (s d)) (\<rho> d))\<close>
    apply (subst kraus_family_filter_comp_dependent)
    using bdd_t by simp_all
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>(F, f)\<in>Rep_kraus_family (s d). kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d)))\<close>
    using bdd'
    by (simp add: kraus_family_comp_dependent_apply kraus_family_map'_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>(f, F)\<in>prod.swap ` Rep_kraus_family (s d). kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d)))\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>(f, F)\<in>(SIGMA f:UNIV. {F. (F, f) \<in> Rep_kraus_family (s d)}). kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d)))\<close>
    apply (rule infsum_cong)
    apply (rule arg_cong[where f=\<open>infsum _\<close>])
    by fastforce
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>f. \<Sum>\<^sub>\<infinity>F\<in>{F. (F,f) \<in> Rep_kraus_family (s d)}. kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d)))\<close>
    apply (rule infsum_cong)
    apply (subst infsum_Sigma_positive_tc)
    using assms by (auto intro!: summ3 kraus_family_map'_pos sandwich_tc_pos
        summable_on_bounded_linear[where h=\<open>kraus_family_map' _ _\<close>]
        bounded_clinear.bounded_linear kraus_family_map'_bounded_clinear)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>f. kraus_family_map' {c} (t f) (\<Sum>\<^sub>\<infinity>F\<in>{F. (F,f) \<in> Rep_kraus_family (s d)}. sandwich_tc F (\<rho> d)))\<close>
    apply (intro infsum_cong)
    apply (rule infsum_bounded_linear[unfolded o_def])
    by (auto intro!: bounded_clinear.bounded_linear kraus_family_map'_bounded_clinear summ3)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>f. kraus_family_map' {c} (t f) (kraus_family_map' {f} (s d) (\<rho> d)))\<close>
    apply (auto intro!: infsum_cong arg_cong[where f=\<open>kraus_family_map' _ _\<close>]
        simp: kraus_family_map'_def kraus_family_map.rep_eq kraus_family_filter.rep_eq)
    apply (subst infsum_reindex[OF inj, symmetric, unfolded o_def])
    by (auto intro!: arg_cong[where f=\<open>sandwich_tc _\<close>] arg_cong[where f=\<open>infsum _\<close>]
        simp: image_iff Bex_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>f. \<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (t f) (kraus_family_map' {f} (s d) (\<rho> d)))\<close>
    apply (rule infsum_swap_positive_tc)
    using assms
    by (auto intro!: summ4 summ2 summable_on_bounded_linear[where h=\<open>kraus_family_map' _ _\<close>]
        bounded_clinear.bounded_linear kraus_family_map'_bounded_clinear kraus_family_map'_pos simp: )
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>f. kraus_family_map' {c} (t f) (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {f} (s d) (\<rho> d)))\<close>
    apply (intro infsum_cong)
    apply (rule infsum_bounded_linear[unfolded o_def])
    by (auto intro!: bounded_clinear.bounded_linear kraus_family_map'_bounded_clinear summ2)
  finally  show \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome snd (kraus_family_comp_dependent t (s d))) (\<rho> d)) =
       (\<Sum>\<^sub>\<infinity>f. kraus_family_map' {c} (t f) (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {f} (s d) (\<rho> d)))\<close>
    by -
qed


lemma cq_map_seq_id_right[simp]: \<open>cq_map_equiv (cq_map_seq s cq_map_id) s\<close>
  apply (rule cq_map_eqI)
  by (simp add: cq_map_apply_seq)

lemma cq_map_seq_id_left[simp]: \<open>cq_map_equiv (cq_map_seq cq_map_id s) s\<close>
  apply (rule cq_map_eqI)
  by (simp add: cq_map_apply_seq)

lift_definition cq_map_if :: \<open>('cl1 \<Rightarrow> bool) \<Rightarrow> ('cl1,'qu1,'cl2,'qu2) cq_map \<Rightarrow> ('cl1,'qu1,'cl2,'qu2) cq_map \<Rightarrow> ('cl1,'qu1,'cl2,'qu2) cq_map\<close> is
  \<open>\<lambda>e p q c. if e c then p c else q c\<close>
proof (rename_tac e \<EE> \<FF>)
  fix e :: \<open>'cl1 \<Rightarrow> bool\<close> and \<EE> :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'cl2) kraus_family\<close> and \<FF> :: \<open>'cl1 \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'cl2) kraus_family\<close>
  assume \<open>bdd_above (range (\<lambda>x. kraus_family_norm (\<EE> x)))\<close>
  then obtain B where B: \<open>kraus_family_norm (\<EE> x) \<le> B\<close> for x
    by (auto intro!: simp: bdd_above_def)
  assume \<open>bdd_above (range (\<lambda>x. kraus_family_norm (\<FF> x)))\<close>
  then obtain C where C: \<open>kraus_family_norm (\<FF> x) \<le> C\<close> for x
    by (auto intro!: simp: bdd_above_def)
  from B C
  have \<open>kraus_family_norm (if e x then \<EE> x else \<FF> x) \<le> max B C\<close> for x
    by smt
  then show \<open>bdd_above (range (\<lambda>x. kraus_family_norm (if e x then \<EE> x else \<FF> x)))\<close>
    by (auto intro!: bdd_aboveI)
qed


lift_definition cq_map_quantum_op :: \<open>('cl \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'x) kraus_family) \<Rightarrow> ('cl,'qu1,'cl,'qu2) cq_map\<close> is
  \<open>\<lambda>(\<EE>::'cl \<Rightarrow> ('qu1 ell2, 'qu2 ell2, 'x) kraus_family) c. 
      if bdd_above (range (\<lambda>c. kraus_family_norm (\<EE> c))) then kraus_family_map_outcome (\<lambda>_. c) (\<EE> c) else 0\<close>
  apply (simp add: bdd_above_def)
  by blast

definition cq_map_of_op :: \<open>'qu1 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'qu2 ell2 \<Rightarrow> ('cl, 'qu1, 'cl, 'qu2) cq_map\<close> where
  \<open>cq_map_of_op U = cq_map_quantum_op (\<lambda>_. kraus_family_of_op U)\<close>

lift_definition cq_map_tensor_op_right :: \<open>('extra ell2, 'extra ell2) trace_class \<Rightarrow> ('cl, 'qu, 'cl, 'qu\<times>'extra) cq_map\<close> is
  \<open>\<lambda>\<rho> c. if \<rho> \<ge> 0 then kraus_family_map_outcome_inj (\<lambda>_. c) (kraus_family_tensor_op_right \<rho>) else 0\<close>
  by (auto simp: bdd_above_def kraus_family_map_outcome_inj_norm inj_on_def kraus_family_norm_tensor_op_right)

lift_definition cq_map_partial_trace :: \<open>('cl, 'qu1\<times>'qu2, 'cl, 'qu1) cq_map\<close> is
  \<open>\<lambda>c. kraus_family_map_outcome (\<lambda>_. c) (kraus_map_partial_trace (range ket))\<close>
  by (auto simp: bdd_above_def)

definition cq_map_auxiliary_state ::
  \<open>('aux ell2, 'aux ell2) trace_class \<Rightarrow> ('cl1, 'qu1\<times>'aux, 'cl2, 'qu2\<times>'aux) cq_map \<Rightarrow> ('cl1,'qu1,'cl2,'qu2) cq_map\<close> where
  \<open>cq_map_auxiliary_state \<rho> \<EE> = 
      cq_map_seq (cq_map_tensor_op_right \<rho>) (cq_map_seq \<EE> cq_map_partial_trace)\<close>

lift_definition cq_map_tensor_id_right :: \<open>('cl1, 'qu1, 'cl2, 'qu2) cq_map \<Rightarrow> ('cl1, 'qu1\<times>'extra, 'cl2, 'qu2\<times>'extra) cq_map\<close> is
  \<open>\<lambda>\<EE> c. kraus_family_map_outcome fst (kraus_family_tensor (\<EE> c) kraus_family_id)\<close>
  apply (auto intro!: kraus_equivalent'_map_cong kraus_family_tensor_cong'
      simp: bdd_above_def)
  by (smt (verit) kraus_family_norm_tensor kraus_map_norm_id mult_cancel_left2)

instantiation cq_map :: (type,type,type,type) zero begin
lift_definition zero_cq_map :: \<open>('a, 'b, 'c, 'd) cq_map\<close> is
  \<open>\<lambda>c. 0\<close>
  by simp
instance..
end

fun cq_map_while_n :: \<open>('cl \<Rightarrow> bool) \<Rightarrow> ('cl,'qu,'cl,'qu) cq_map \<Rightarrow> nat \<Rightarrow> ('cl,'qu,'cl,'qu) cq_map\<close> where
  \<open>cq_map_while_n c _ 0 = cq_map_if c cq_map_id 0\<close>
| \<open>cq_map_while_n c \<EE> (Suc n) = cq_map_if c (cq_map_seq \<EE> (cq_map_while_n c \<EE> n)) 0\<close>


lift_definition cq_map_infsum :: \<open>('a \<Rightarrow> ('cl1,'qu1,'cl2,'qu2) cq_map) \<Rightarrow> 'a set \<Rightarrow> ('cl1,'qu1,'a\<times>'cl2,'qu2) cq_map\<close> is
  \<open>\<lambda>\<EE> A. if \<forall>c. has_kraus_map_infsum (\<lambda>a. \<EE> a c) A \<and> bdd_above (range (\<lambda>c. kraus_family_norm (kraus_map_infsum (\<lambda>a. \<EE> a c) A)))
      then \<lambda>c. kraus_map_infsum (\<lambda>a. \<EE> a c) A else (\<lambda>_. 0)\<close>
  by auto

lift_definition cq_map_classical :: \<open>('cl1 \<Rightarrow> 'cl2) \<Rightarrow> ('cl1, 'qu, 'cl2, 'qu) cq_map\<close> is
  \<open>\<lambda>f c. kraus_family_map_outcome_inj (\<lambda>_. f c) kraus_family_id\<close>
  by (auto simp: bdd_above_def kraus_family_map_outcome_inj_norm inj_on_def)

definition cq_map_while :: \<open>('cl \<Rightarrow> bool) \<Rightarrow> ('cl,'qu,'cl,'qu) cq_map \<Rightarrow> ('cl,'qu,'cl,'qu) cq_map\<close> where
  \<open>cq_map_while c \<EE> = cq_map_seq (cq_map_infsum (\<lambda>n. cq_map_while_n c \<EE> n) UNIV) (cq_map_classical snd)\<close>

lift_definition cq_prob :: \<open>('cl,'qu) cq_operator \<Rightarrow> 'cl \<Rightarrow> real\<close> is
  \<open>\<lambda>\<rho> c. norm (\<rho> c)\<close>.

lemma cq_map_equiv_refl[iff]: \<open>cq_map_equiv E E\<close>
  using cq_map_equiv_ext by blast

lemma cq_map_equiv_sym[iff]: \<open>cq_map_equiv E F \<Longrightarrow> cq_map_equiv F E\<close>
  by (simp add: cq_map_equiv_ext)

lemma cq_map_equiv_trans[trans]: \<open>cq_map_equiv E F \<Longrightarrow> cq_map_equiv F G \<Longrightarrow> cq_map_equiv E G\<close>
  by (simp add: cq_map_equiv_ext)

lemma cq_map_seq_cong:
  assumes \<open>cq_map_equiv E E'\<close> and \<open>cq_map_equiv F F'\<close>
  shows \<open>cq_map_equiv (cq_map_seq E F) (cq_map_seq E' F')\<close>
  by (metis (no_types, lifting) assms(1) assms(2) cq_map_apply_seq cq_map_eqI cq_map_equiv_ext)


end
