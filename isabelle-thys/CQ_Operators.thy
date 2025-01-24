theory CQ_Operators
  imports Kraus_Maps.Kraus_Maps Registers2.Missing_Bounded_Operators Registers2.Quantum_Registers
    Registers2.Registers_Unsorted
begin

unbundle kraus_map_syntax

type_synonym ('c,'q) cq_operator = \<open>(('c\<times>'q) ell2, ('c\<times>'q) ell2) trace_class\<close>
type_synonym ('c1,'q1,'c2,'q2) cq_map = \<open>(('c1\<times>'q1) ell2, ('c2\<times>'q2) ell2, unit) kraus_family\<close>
type_synonym ('c,'q) cq_map2 = \<open>('c,'q,'c,'q) cq_map\<close>

(* TODO move *)
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
  \<open>classical_on C \<rho> \<longleftrightarrow> kraus_family_map (apply_qregister_kraus_map C (complete_measurement (range ket))) \<rho> = \<rho>\<close>

definition classical_fst :: \<open>(('c\<times>'q) ell2, ('c\<times>'q) ell2) trace_class \<Rightarrow> bool\<close> where
  \<open>classical_fst \<rho> \<longleftrightarrow> kraus_family_map (kraus_family_tensor (complete_measurement (range ket)) kraus_family_id) \<rho> = \<rho>\<close>

(* lemma \<open>classical_fst \<rho> \<longleftrightarrow> classical_on qFst \<rho>\<close>
  apply (simp add: classical_on_def classical_fst_def)
  by x *)

definition cq_operator_at :: \<open>(('c\<times>'q) ell2, ('c\<times>'q) ell2) trace_class \<Rightarrow> 'c \<Rightarrow> ('q ell2, 'q ell2) trace_class\<close> where
  \<open>cq_operator_at \<rho> c = sandwich_tc (tensor_ell2_left (ket c)*) \<rho>\<close>

definition cq_operator_reconstruct :: \<open>('c \<Rightarrow> ('q ell2, 'q ell2) trace_class) \<Rightarrow> (('c\<times>'q) ell2, ('c\<times>'q) ell2) trace_class\<close> where
  \<open>cq_operator_reconstruct \<rho> = (\<Sum>\<^sub>\<infinity>c. tc_tensor (tc_butterfly (ket c) (ket c)) (\<rho> c))\<close>

lemma cq_operator_at_summable:
  fixes \<rho> :: \<open>(('c\<times>'q) ell2, ('c\<times>'q) ell2) trace_class\<close> and c :: 'c
  shows \<open>cq_operator_at \<rho> abs_summable_on UNIV\<close>
  using partial_trace_abs_summable'[of \<open>sandwich_tc swap_ell2 \<rho>\<close>]
  by (simp add: cq_operator_at_def sandwich_tc_compose[symmetric, unfolded o_def, THEN fun_cong])

lemma cq_operator_at_bounded_clinear[bounded_clinear]:
  \<open>bounded_clinear (\<lambda>\<rho>. cq_operator_at \<rho> c)\<close>
proof -
  have 1: \<open>cq_operator_at (\<rho> + y) c = cq_operator_at \<rho> c + cq_operator_at y c\<close> for \<rho> y :: \<open>(('a \<times> 'b) ell2, ('a \<times> 'b) ell2) trace_class\<close>
    by (simp add: sandwich_tc_plus cq_operator_at_def)
  have 2: \<open>cq_operator_at (r *\<^sub>C \<rho>) c = r *\<^sub>C cq_operator_at \<rho> c\<close> for \<rho> :: \<open>(('a \<times> 'b) ell2, ('a \<times> 'b) ell2) trace_class\<close> and r
    by (simp add: cq_operator_at_def sandwich_tc_scaleC_right)
  have 3: \<open>norm (cq_operator_at \<rho> c) \<le> norm \<rho> * 1\<close> for \<rho> :: \<open>(('a \<times> 'b) ell2, ('a \<times> 'b) ell2) trace_class\<close>
    using norm_sandwich_tc[of \<open>tensor_ell2_left (ket c)*\<close> \<rho>]
    by (simp add: cq_operator_at_def)
  from 1 2 3
  show ?thesis
    by (rule bounded_clinearI)
qed

lemma cq_operator_reconstruct_inv:
  fixes \<rho> :: \<open>'c \<Rightarrow> ('q ell2, 'q ell2) trace_class\<close>
  assumes sum_\<rho>: \<open>\<rho> abs_summable_on UNIV\<close>
  shows \<open>cq_operator_at (cq_operator_reconstruct \<rho>) = \<rho>\<close>
proof (rule ext)
  fix c
  have *: \<open>cq_operator_at (tc_tensor (tc_butterfly (ket d) (ket d)) (\<rho> d)) c = of_bool (c=d) *\<^sub>C \<rho> d\<close> for d
    apply (rule from_trace_class_inject[THEN iffD1])
    by (simp add: cq_operator_at_def from_trace_class_sandwich_tc tc_tensor.rep_eq tc_butterfly.rep_eq sandwich_tensor_ell2_left)
  have summable1: \<open>(\<lambda>c. tc_tensor (tc_butterfly (ket c) (ket c)) (\<rho> c)) summable_on UNIV\<close>
    by (simp add: abs_summable_summable assms norm_tc_butterfly norm_tc_tensor)
  have \<open>cq_operator_at (cq_operator_reconstruct \<rho>) c
     = cq_operator_at (\<Sum>\<^sub>\<infinity>c. tc_tensor (tc_butterfly (ket c) (ket c)) (\<rho> c)) c\<close>
    by (simp add: cq_operator_reconstruct_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. cq_operator_at (tc_tensor (tc_butterfly (ket d) (ket d)) (\<rho> d)) c)\<close>
    apply (subst infsum_bounded_linear[where h=\<open>\<lambda>\<rho>. cq_operator_at \<rho> c\<close>])
      apply (simp add: bounded_clinear.bounded_linear cq_operator_at_bounded_clinear) 
     apply (rule summable1)
    by simp
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d::'c. of_bool (c = d) *\<^sub>C \<rho> d)\<close>
    by (simp add: * )
  also have \<open>\<dots> = \<rho> c\<close>
    apply (subst infsum_single[where i=c])
    by auto
  finally show \<open>cq_operator_at (cq_operator_reconstruct \<rho>) c = \<rho> c\<close>
    by -
qed

lemma cq_operator_reconstruct:
  fixes \<rho> :: \<open>(('c\<times>'q) ell2, ('c\<times>'q) ell2) trace_class\<close>
  assumes cq: \<open>classical_fst \<rho>\<close>
  shows \<open>cq_operator_reconstruct (cq_operator_at \<rho>) = \<rho>\<close>
proof -
  define f :: \<open>('c \<times> 'q) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'q) ell2 \<Rightarrow> 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close>
    where \<open>f = inv (\<lambda>E. E \<otimes>\<^sub>o id_cblinfun)\<close>
  have [simp]: \<open>f (E \<otimes>\<^sub>o id_cblinfun) = E\<close> for E :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close>
    unfolding f_def
    apply (subst inv_f_f)
    by (auto intro!: inj_tensor_left)
  have \<open>cq_operator_reconstruct (cq_operator_at \<rho>)
        = (\<Sum>\<^sub>\<infinity>c. (tc_tensor (tc_butterfly (ket c) (ket c)) (sandwich_tc (tensor_ell2_left (ket c)*) \<rho>)))\<close>
    by (simp add: cq_operator_reconstruct_def cq_operator_at_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>c. sandwich_tc (selfbutter (ket c) \<otimes>\<^sub>o id_cblinfun) \<rho>)\<close>
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
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>range (\<lambda>x::'c. ((selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun), ket x)). sandwich_tc (fst E) \<rho>)\<close>
    apply (subst infsum_reindex)
    by (simp_all add: inj_def o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((E, x), F, y)\<in>range (\<lambda>x. (selfbutter (ket x), ket x)) \<times> {(id_cblinfun, ())}. sandwich_tc (E \<otimes>\<^sub>o F) \<rho>)\<close>
    apply (subst infsum_reindex_bij_betw[where A=\<open>range (\<lambda>x. (selfbutter (ket x), ket x)) \<times> {(id_cblinfun, ())}\<close>
          and g=\<open>\<lambda>((E,x),(F,y)). (E \<otimes>\<^sub>o F, x)\<close>, symmetric])
     apply (rule bij_betw_byWitness[where f'=\<open>\<lambda>(Eid,x). ((f Eid,x),(id_cblinfun,()))\<close>])
        apply auto[4]
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> = kraus_family_map (kraus_family_tensor (complete_measurement (range ket)) kraus_family_id) \<rho>\<close>
    apply (simp only: kraus_family_map_tensor_sum kraus_family_id_def kraus_family_of_op.rep_eq complete_measurement.rep_eq)
    by (simp add: image_image)
  also have \<open>\<dots> = \<rho>\<close>
    using cq classical_fst_def by blast
  finally show ?thesis
    by -
qed


definition cq_map_from_measurement :: \<open>(('c1\<times>'q1) ell2, 'q2 ell2, 'c2) kraus_family \<Rightarrow> (('c1\<times>'q1) ell2, ('c2\<times>'q2) ell2, unit) kraus_family\<close> where
  \<open>cq_map_from_measurement E = kraus_family_flatten
      (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) E)\<close>

definition cq_map_from_pointwise :: \<open>('c1 \<Rightarrow> ('q1 ell2, 'q2 ell2, 'c2) kraus_family) \<Rightarrow> (('c1\<times>'q1) ell2, ('c2\<times>'q2) ell2, unit) kraus_family\<close> where
  \<open>cq_map_from_pointwise E = cq_map_from_measurement (kraus_family_map_outcome snd (kraus_family_comp_dependent E (kraus_map_partial_trace' (range ket))))\<close>

definition cq_map_to_pointwise :: \<open>(('c1\<times>'q1) ell2, ('c2\<times>'q2) ell2, unit) kraus_family \<Rightarrow> ('c1 \<Rightarrow> ('q1 ell2, 'q2 ell2, 'c2) kraus_family)\<close> where
\<open>cq_map_to_pointwise E = undefined\<close>

definition cq_map_cases :: \<open>('c1 \<Rightarrow> ('c1,'q1,'c2,'q2) cq_map) \<Rightarrow> ('c1,'q1,'c2,'q2) cq_map\<close> where
\<open>cq_map_cases E = kraus_family_flatten (kraus_family_comp_dependent (\<lambda>(c,()). E (inv ket c))
                       (kraus_family_tensor (complete_measurement (range ket)) kraus_family_id))\<close>

definition cq_map_sample :: \<open>('cl1 \<Rightarrow> 'cl2 \<Rightarrow> real) \<Rightarrow> ('cl1, 'qu,'cl2, 'qu) cq_map\<close> where
  \<open>cq_map_sample d = cq_map_from_pointwise (\<lambda>c. kraus_map_sample (d c))\<close>

definition cq_prob :: \<open>('c,'q) cq_operator \<Rightarrow> 'c \<Rightarrow> real\<close> where
  \<open>cq_prob \<rho> c = norm (cq_operator_at \<rho> c)\<close>

definition cq_map_comp :: \<open>('c2,'q2,'c3,'q3) cq_map \<Rightarrow> ('c1,'q1,'c2,'q2) cq_map \<Rightarrow> ('c1,'q1,'c3,'q3) cq_map\<close> where
  \<open>cq_map_comp E F = kraus_family_flatten (kraus_family_comp E F)\<close>

lemma cq_map_comp_cong:
  assumes \<open>kraus_equivalent E E'\<close>
  assumes \<open>kraus_equivalent F F'\<close>
  shows \<open>kraus_equivalent (cq_map_comp E F) (cq_map_comp E' F')\<close>
  by (auto intro!: kraus_equivalent_kraus_family_map_outcome_left kraus_equivalent_kraus_family_map_outcome_right kraus_family_comp_cong assms
      simp: cq_map_comp_def)

fun cq_map_seq where
  \<open>cq_map_seq [] = kraus_family_id\<close>
| \<open>cq_map_seq [E] = E\<close>
| \<open>cq_map_seq (E#Es) = cq_map_comp (cq_map_seq Es) E\<close>

definition cq_map_on_q :: \<open>('c \<Rightarrow> ('q1 ell2,'q2 ell2,'x) kraus_family) \<Rightarrow> ('c,'q1,'c,'q2) cq_map\<close> where
  \<open>cq_map_on_q E = cq_map_from_pointwise (\<lambda>c. kraus_family_map_outcome (\<lambda>_. c) (E c))\<close>

definition cq_map_on_c :: \<open>('c1 \<Rightarrow> 'c2) \<Rightarrow> ('c1,'q,'c2,'q) cq_map\<close> where
  \<open>cq_map_on_c f = cq_map_from_pointwise (\<lambda>c. kraus_family_map_outcome (\<lambda>_. f c) kraus_family_id)\<close>

definition cq_map_with_auxiliary_state ::
  \<open>('aux ell2, 'aux ell2) trace_class \<Rightarrow> ('cl1, 'qu1\<times>'aux, 'cl2, 'qu2\<times>'aux) cq_map \<Rightarrow> ('cl1,'qu1,'cl2,'qu2) cq_map\<close> where
  \<open>cq_map_with_auxiliary_state \<rho> \<EE> = cq_map_comp (cq_map_on_q (\<lambda>_. kraus_map_partial_trace (range ket))) (cq_map_comp \<EE> (cq_map_on_q (\<lambda>_. kraus_family_tensor_op_right \<rho>)))\<close>

definition \<open>cq_map_of_op U = cq_map_on_q (\<lambda>c. kraus_family_of_op (U c))\<close>

definition cq_map_tensor_id_right :: \<open>('cl1, 'qu1, 'cl2, 'qu2) cq_map \<Rightarrow> ('cl1, 'qu1\<times>'extra, 'cl2, 'qu2\<times>'extra) cq_map\<close> where
  \<open>cq_map_tensor_id_right \<EE> = cq_map_from_pointwise (\<lambda>c. 
      kraus_family_map_outcome fst (kraus_family_tensor (cq_map_to_pointwise \<EE> c) kraus_family_id))\<close>

definition cq_map_id :: \<open>('c,'q) cq_map2\<close> where
  \<open>cq_map_id = cq_map_on_q (\<lambda>_. kraus_family_id)\<close>

definition is_cq_map :: \<open>('c1,'q1,'c2,'q2) cq_map \<Rightarrow> bool\<close> where
  \<open>is_cq_map E \<longleftrightarrow> kraus_equivalent (cq_map_comp (cq_map_comp cq_map_id E) cq_map_id) E\<close>

lemma is_cq_mapI: 
  assumes \<open>kraus_equivalent (cq_map_comp (cq_map_comp cq_map_id E) cq_map_id) E\<close>
  shows \<open>is_cq_map E\<close>
  by (simp add: assms is_cq_map_def)

lemma is_cq_mapI2:
  assumes \<open>kraus_equivalent (cq_map_comp cq_map_id E) E\<close>
  assumes \<open>kraus_equivalent (cq_map_comp E cq_map_id) E\<close>
  shows \<open>is_cq_map E\<close>
  by (metis assms(1) assms(2) cq_map_comp_def is_cq_mapI kraus_equivalent_def kraus_family_comp_apply kraus_family_map_outcome_same_map)

lemma cq_map_comp_0L[simp]: \<open>cq_map_comp 0 E = 0\<close>
  by (simp add: cq_map_comp_def)

lemma cq_map_comp_0R[simp]: \<open>cq_map_comp E 0 = 0\<close>
  by (simp add: cq_map_comp_def)

lemma is_cq_map_0[iff]: \<open>is_cq_map 0\<close>
  by (simp add: is_cq_map_def)

definition cq_map_while :: \<open>('c \<Rightarrow> bool) \<Rightarrow> ('c,'q) cq_map2 \<Rightarrow> ('c,'q) cq_map2\<close> where
  \<open>cq_map_while = undefined\<close>

lemma cq_map_comp_cq_map_from_measurement:
  shows \<open>cq_map_comp (cq_map_from_measurement F) (cq_map_from_measurement E) 
      =\<^sub>k\<^sub>r cq_map_from_measurement (kraus_family_map_outcome snd (kraus_family_comp F (kraus_family_comp_dependent 
                                            (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) E)))\<close>
proof -
  have \<open>cq_map_comp (cq_map_from_measurement F) (cq_map_from_measurement E)
    = kraus_family_flatten (kraus_family_comp (kraus_family_flatten (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) F))
       (kraus_family_flatten (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) E)))\<close>
    by (simp add: cq_map_comp_def cq_map_from_measurement_def)
  also have \<open>kraus_family_flatten
     (kraus_family_comp (kraus_family_flatten (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) F))
       (kraus_family_flatten (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) E)))
=\<^sub>k\<^sub>r kraus_family_comp (kraus_family_flatten (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) F))
       (kraus_family_flatten (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) E))\<close>
  by (simp add: kraus_equivalent_def)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kraus_family_comp ( (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) F))
       (kraus_family_flatten (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) E))\<close>
    by (simp add: kraus_equivalent_def kraus_family_comp_apply)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kraus_family_comp ( (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) F))
       ( (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) E))\<close>
    by (simp add: kraus_equivalent_def kraus_family_comp_apply)
  also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kraus_family_map_outcome (\<lambda>((g, f), e). (g, f, ()))
     (kraus_family_comp_dependent (\<lambda>(_, f). kraus_family_of_op (tensor_ell2_left (ket f)))
       (kraus_family_comp F (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) E)))\<close>
    apply (rule kraus_equivalent'_trans)
    unfolding kraus_family_comp_def
     apply (rule kraus_family_comp_dependent_assoc')
    by auto
  also have \<open>\<dots> =\<^sub>k\<^sub>r kraus_family_comp_dependent (\<lambda>(_, f). kraus_family_of_op (tensor_ell2_left (ket f)))
       (kraus_family_comp F (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) E))\<close>
    by (simp add: kraus_equivalent_def)
  also have \<open>\<dots> =\<^sub>k\<^sub>r kraus_family_flatten (kraus_family_comp_dependent (\<lambda>f. kraus_family_of_op (tensor_ell2_left (ket f)))
       (kraus_family_map_outcome snd (kraus_family_comp F (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) E))))\<close>
    apply (rule kraus_equivalent_sym)
    apply (rule kraus_equivalent_trans)
     apply (rule kraus_family_flatten_cong)
     apply (rule kraus_equivalent'_imp_equivalent)
     apply (rule kraus_family_comp_dependent_map_outcome_right)
    by (simp add: kraus_equivalent_def case_prod_unfold)
  also have \<open>\<dots> = cq_map_from_measurement (kraus_family_map_outcome snd (kraus_family_comp F (kraus_family_comp_dependent 
                                            (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c))) E)))\<close>
    by (simp add: cq_map_from_measurement_def)
  finally show ?thesis
    by -
qed

lemma cq_map_from_measurement_cong:
  assumes \<open>E \<equiv>\<^sub>k\<^sub>r F\<close>
  shows \<open>cq_map_from_measurement E =\<^sub>k\<^sub>r cq_map_from_measurement F\<close>
by -

lemma kraus_family_map_outcome_equiv_left_iff[simp]: 
(* TODO right *)
  shows \<open>kraus_family_map_outcome f E =\<^sub>k\<^sub>r F \<longleftrightarrow> E =\<^sub>k\<^sub>r F\<close>
  by (simp add: kraus_equivalent_def)

lemma cq_map_comp_cq_map_from_pointwise:
  fixes E :: \<open>'c1 \<Rightarrow> ('q1 ell2, 'q2 ell2, 'c2) kraus_family\<close>
    and F :: \<open>'c2 \<Rightarrow> ('q2 ell2, 'q3 ell2, 'c3) kraus_family\<close>
  shows \<open>cq_map_comp (cq_map_from_pointwise F) (cq_map_from_pointwise E) 
      =\<^sub>k\<^sub>r cq_map_from_pointwise (\<lambda>c. kraus_family_map_outcome snd (kraus_family_comp_dependent (\<lambda>d. F d) (E c)))\<close>
proof -
  have \<open>cq_map_comp (cq_map_from_pointwise F) (cq_map_from_pointwise E) =\<^sub>k\<^sub>r 
      cq_map_from_measurement
           (kraus_family_map_outcome snd
             (kraus_family_comp (kraus_family_map_outcome snd (kraus_family_comp_dependent F (kraus_map_partial_trace' (range ket))))
               (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c)))
                 (kraus_family_map_outcome snd (kraus_family_comp_dependent E (kraus_map_partial_trace' (range ket)))))))\<close>
    unfolding cq_map_from_pointwise_def
    by (rule cq_map_comp_cq_map_from_measurement)
  also have \<open>\<dots> = xxx\<close>





]


  have \<open>kraus_family_map_outcome snd (kraus_family_comp (kraus_family_map_outcome snd (kraus_family_comp_dependent F (kraus_map_partial_trace' (range ket))))
         (kraus_family_comp_dependent (\<lambda>c. kraus_family_of_op (tensor_ell2_left (ket c)))
           (kraus_family_map_outcome snd (kraus_family_comp_dependent E (kraus_map_partial_trace' (range ket))))))
    \<equiv>\<^sub>k\<^sub>r
    kraus_family_map_outcome snd (kraus_family_comp_dependent (\<lambda>c. kraus_family_map_outcome snd (kraus_family_comp_dependent F (E c))) (kraus_map_partial_trace' (range ket)))\<close>
  proof -


    show a for a
      by x
  qed

  then
  show ?thesis
    unfolding cq_map_from_pointwise_def
    apply (rule_tac kraus_equivalent_trans)
     apply (rule cq_map_comp_cq_map_from_measurement)
    apply (rule cq_map_from_measurement_cong)
    by simp
qed

lemma cq_map_from_pointwise_cong:
  assumes \<open>\<And>x. kraus_equivalent (E x) (F x)\<close>
  shows \<open>kraus_equivalent (cq_map_from_pointwise E) (cq_map_from_pointwise F)\<close>
by -


lemma is_cq_map_cq_map_from_measurement[iff]: 
  assumes \<open>kraus_family_map_outcome snd (kraus_family_comp E cq_map_id) \<equiv>\<^sub>k\<^sub>r E\<close>
  shows \<open>is_cq_map (cq_map_from_measurement E)\<close>
by -

lemma cq_map_comp_id_left[simp]: \<open>cq_map_comp cq_map_id E = E\<close> if \<open>is_cq_map E\<close>
by -

lemma cq_map_comp_id_right[simp]: \<open>cq_map_comp E cq_map_id = E\<close> if \<open>is_cq_map E\<close>
by -

lemma kraus_family_comp_partial_trace'_cq_map_id: \<open>kraus_family_comp (kraus_map_partial_trace' (range ket)) cq_map_id
    \<equiv>\<^sub>k\<^sub>r kraus_family_map_outcome (\<lambda>x. ((),x)) (kraus_map_partial_trace' (range ket))\<close>
by -



lemma is_cq_map_cq_map_from_pointwise[iff]: 
  fixes E :: \<open>('c1 \<Rightarrow> ('q1 ell2, 'q2 ell2, 'c2) kraus_family)\<close>
  shows \<open>is_cq_map (cq_map_from_pointwise E)\<close>
proof (unfold cq_map_from_pointwise_def, rule is_cq_map_cq_map_from_measurement)
  let ?id = \<open>cq_map_id :: (('c1 \<times> 'q1) ell2, ('c1 \<times> 'q1) ell2, unit) kraus_family\<close>
  let ?lhs = \<open>kraus_family_map_outcome snd
     (kraus_family_comp (kraus_family_map_outcome (\<lambda>(c, d). d) (kraus_family_comp_dependent E (kraus_map_partial_trace' (range ket)))) ?id)\<close>
    and ?rhs = \<open>kraus_family_map_outcome (\<lambda>(c, d). d) (kraus_family_comp_dependent E (kraus_map_partial_trace' (range ket)))\<close>
  wlog bdd: \<open>bdd_above (range (kraus_family_norm \<circ> E))\<close> goal \<open>?lhs \<equiv>\<^sub>k\<^sub>r ?rhs\<close>
    using negation
    by (simp add: kraus_family_comp_dependent_invalid case_prod_unfold)
  have bdd1: \<open>bdd_above (range (kraus_family_norm \<circ> (\<lambda>g. kraus_map_partial_trace' (range ket))))\<close>
    by simp
  have bdd2: \<open>bdd_above ((kraus_family_norm \<circ> (\<lambda>(_, f). E f)) ` kraus_map_domain (kraus_family_comp (kraus_map_partial_trace' (range ket)) ?id))\<close>
  proof -
    have \<open>?thesis = bdd_above ((kraus_family_norm \<circ> E) ` ((\<lambda>(_, f). f) ` kraus_map_domain (kraus_family_comp (kraus_map_partial_trace' (range ket)) ?id)))\<close>
      apply (rule arg_cong[where f=bdd_above])
      by force
    also have \<open>\<dots>\<close>
      using bdd apply (rule bdd_above_mono2)
      by auto
    finally show ?thesis
      by -
  qed
  have bdd3: \<open>bdd_above ((kraus_family_norm \<circ> E) ` kraus_map_domain (kraus_map_partial_trace' (range ket)))\<close>
    using bdd bdd_above_mono2 by force

  show  \<open>?lhs \<equiv>\<^sub>k\<^sub>r ?rhs\<close>
  proof (rule kraus_equivalent'I_from_equivalent)
    fix x :: 'c2
    define E_x where \<open>E_x e = kraus_family_filter ((=) x) (E e)\<close> for e
    have aux1: \<open>(\<lambda>xa. x = snd xa) = (\<lambda>(e,f). x=f \<and> True)\<close>
      by auto
    have aux2: \<open>(\<lambda>xa. x = (case xa of (c, d) \<Rightarrow> d)) = (\<lambda>(e,f). x=f \<and> True)\<close>
      by auto
    from bdd
    have bdd4: \<open>bdd_above (range (kraus_family_norm \<circ> E_x))\<close>
      apply (rule bdd_above_mono2)
      by (auto intro!: kraus_family_norm_filter simp: E_x_def)
    have bdd5: \<open>bdd_above ((kraus_family_norm \<circ> (\<lambda>(_, f). E_x f)) ` kraus_map_domain (kraus_family_comp (kraus_map_partial_trace' (range ket)) ?id))\<close>
    proof -
      have \<open>?thesis = bdd_above ((kraus_family_norm \<circ> E_x) ` ((\<lambda>(_, f). f) ` kraus_map_domain (kraus_family_comp (kraus_map_partial_trace' (range ket)) ?id)))\<close>
        apply (rule arg_cong[where f=bdd_above])
        by force
      also have \<open>\<dots>\<close>
        using bdd4 apply (rule bdd_above_mono2)
        by auto
      finally show ?thesis
        by -
    qed

    have \<open>kraus_family_filter ((=) x) ?lhs = kraus_family_map_outcome snd
     (kraus_family_comp (kraus_family_map_outcome (\<lambda>(c, d). d)
         (kraus_family_comp_dependent E_x (kraus_map_partial_trace' (range ket)))) cq_map_id)\<close>
      by (simp only: kraus_family_filter_true kraus_family_filter_comp_dependent[OF bdd3] aux2 aux1
          kraus_family_filter_map_outcome kraus_family_filter_comp kraus_family_filter_map_outcome E_x_def[abs_def])
    also have \<open>\<dots> =\<^sub>k\<^sub>r kraus_family_comp (kraus_family_comp_dependent E_x (kraus_map_partial_trace' (range ket))) cq_map_id\<close>
      by (simp add: kraus_equivalent_def kraus_family_comp_apply)
    also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kraus_family_map_outcome (\<lambda>((g, f), e). (g, f, e))
       (kraus_family_comp_dependent (\<lambda>(_, f). E_x f) (kraus_family_comp (kraus_map_partial_trace' (range ket)) cq_map_id))\<close>
      using bdd1 bdd4 by (auto intro!: kraus_family_comp_dependent_assoc' simp only: kraus_family_comp_def)
    also have \<open>\<dots> =\<^sub>k\<^sub>r (kraus_family_comp_dependent (\<lambda>(_, f). E_x f) (kraus_family_comp (kraus_map_partial_trace' (range ket)) cq_map_id))\<close>
      by (simp add: kraus_equivalent_def)
    also have \<open>\<dots> \<equiv>\<^sub>k\<^sub>r kraus_family_comp_dependent (\<lambda>(_, f). E_x f) (kraus_family_map_outcome (\<lambda>x. ((),x)) (kraus_map_partial_trace' (range ket)))\<close>
      by (auto intro!: kraus_family_comp_dependent_cong' bdd5 kraus_family_comp_partial_trace'_cq_map_id)
    also have \<open>\<dots> =\<^sub>k\<^sub>r kraus_family_map_outcome (\<lambda>(c, d). d) (kraus_family_comp_dependent E_x (kraus_map_partial_trace' (range ket)))\<close>
      (* TODO: missing lemma for: comp_def (map_outcome f E) (G) = \<dots> *)
      by -
    also have \<open>\<dots> = kraus_family_filter ((=) x) (kraus_family_map_outcome (\<lambda>(c, d). d) (kraus_family_comp_dependent E (kraus_map_partial_trace' (range ket))))\<close>
      by (simp only: kraus_family_filter_true kraus_family_filter_comp_dependent[OF bdd3] aux2 
          kraus_family_filter_map_outcome E_x_def[abs_def])
    finally show \<open>kraus_family_filter ((=) x) ?lhs =\<^sub>k\<^sub>r kraus_family_filter ((=) x) ?rhs\<close>
      by -
  qed
qed

lemma kraus_family_norm_cq_map_from_pointwise:
  assumes \<open>\<And>x. kraus_family_norm (E x) \<le> B\<close>
  shows \<open>kraus_family_norm (cq_map_from_pointwise E) \<le> B\<close>
  by -

lemma kraus_family_norm_cq_map_to_pointwise:
  \<open>kraus_family_norm (cq_map_to_pointwise E x) \<le> kraus_family_norm E\<close>
by -

lemma cq_map_from_pointwise_cong:
  assumes \<open>\<And>c. kraus_equivalent' (\<EE> c) (\<FF> c)\<close>
  shows \<open>kraus_equivalent (cq_map_from_pointwise \<EE>) (cq_map_from_pointwise \<FF>)\<close>
by -

lemma cq_map_to_pointwise_cong:
  assumes \<open>kraus_equivalent \<EE> \<FF>\<close>
  shows \<open>kraus_equivalent' (cq_map_to_pointwise \<EE> c) (cq_map_to_pointwise \<FF> c)\<close>
  by (simp add: cq_map_to_pointwise_def)

end

