theory CQ_Operators
  imports Tensor_Product.Trace_Class Registers2.Missing_Bounded_Operators Discrete_Distributions Kraus_Maps
    Tensor_Product.Partial_Trace
begin


(* lift_definition measure_kraus_family :: \<open>('a ell2, 'a ell2, 'a) kraus_family\<close> is
  \<open>range (\<lambda>x. (selfbutter (ket x), x))\<close>
  sorry  *)

lemma complete_measurement_has_sum:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>((\<lambda>x. sandwich_tc (selfbutter (sgn x)) \<rho>) has_sum kraus_family_map (complete_measurement B) \<rho>) B\<close>
proof -
  define \<rho>' where \<open>\<rho>' = kraus_family_map (complete_measurement B) \<rho>\<close>
  have \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum \<rho>') (Rep_kraus_family (complete_measurement B))\<close>
    by (simp add: \<rho>'_def kraus_family_map_has_sum)
  then have \<open>((\<lambda>(E, x). sandwich_tc E \<rho>) has_sum \<rho>') ((\<lambda>x. (selfbutter (sgn x), x)) ` B)\<close>
    by (simp add: assms complete_measurement.rep_eq)
  then show \<open>((\<lambda>x. sandwich_tc (selfbutter (sgn x)) \<rho>) has_sum \<rho>') B\<close>
    apply (subst (asm) has_sum_reindex)
    by (auto simp add: inj_on_def o_def)
qed

definition \<open>measure_first = kraus_family_tensor (complete_measurement (range ket)) kraus_family_id\<close>

lemma complete_measurement_apply:
  assumes \<open>is_ortho_set B\<close>
  shows \<open>kraus_family_map (complete_measurement B) \<rho> = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter (sgn x)) \<rho>)\<close>
  by (metis (mono_tags, lifting) assms complete_measurement_has_sum infsumI)

(* lemma kraus_family_reconstruct_transfer:
  assumes sum: \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum kraus_map_apply \<EE> \<rho>) A\<close>
  defines \<open>F \<equiv> (\<lambda>a. (f a, a)) ` A\<close>
  shows \<open>cr_kraus_map (kraus_family_flatten F) \<EE>\<close>
proof -
  define flat where \<open>flat = kraus_family_flatten F\<close>
  have [iff]: \<open>kraus_family F\<close>
    by (auto intro!: kraus_family_reconstruct_is_family[OF sum] simp: F_def)
  have [iff]: \<open>kraus_family flat\<close>
    using flat_def by blast
  have \<open>kraus_map_apply (abs_kraus_map flat) = kraus_family_map F\<close>
    apply (simp add: kraus_equivalent_reflI kraus_map_apply.abs_eq)
    by (simp add: flat_def kraus_family_flatten_same_map)
  moreover have \<open>kraus_map_apply \<EE> = kraus_family_map F\<close>
    by (auto intro!: kraus_family_reconstruct[OF sum] simp: F_def)
  ultimately have \<open>kraus_map_apply (abs_kraus_map flat) = kraus_map_apply \<EE>\<close>
    by simp
  then show ?thesis
    by (auto intro!: kraus_equivalent_reflI kraus_map_apply_inj simp: cr_kraus_map_def flat_def)
qed *)

lemma kraus_map_apply_tensor_has_sum:
  assumes \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum kraus_family_map \<EE> \<rho>) A\<close>
  assumes \<open>\<And>\<sigma>. ((\<lambda>b. sandwich_tc (g b) \<sigma>) has_sum kraus_family_map \<FF> \<sigma>) B\<close>
  shows \<open>((\<lambda>(a,b). sandwich_tc (f a \<otimes>\<^sub>o g b) \<tau>) has_sum kraus_family_map (kraus_family_tensor_raw \<EE> \<FF>) \<tau>) (A\<times>B)\<close>
proof -
  define A' B' where \<open>A' = (\<lambda>a. (f a, a)) ` A\<close> and \<open>B' = (\<lambda>b. (g b, b)) ` B\<close>
    (* and \<open>A'B'\<tau> = kraus_family_map (kraus_family_tensor A' B') \<tau>\<close> *)
  define tensor\<tau> where \<open>tensor\<tau> = kraus_family_map (kraus_family_tensor_raw \<EE> \<FF>) \<tau>\<close>
  define A'B' where \<open>A'B' = (\<lambda>((E,x), (F,y)). (E \<otimes>\<^sub>o F, (E,F,x,y))) ` (A'\<times>B')\<close>

  note kraus_family_reconstruct_transfer[OF assms(1), folded A'_def, transfer_rule]
  note kraus_family_reconstruct_transfer[OF assms(2), folded B'_def, transfer_rule]

  write kraus_equivalent (infix \<open>~\<close> 50)

  have [iff]: \<open>kraus_family A'\<close>
    by (auto intro!: kraus_family_reconstruct_is_family assms kraus_family_map_bounded_clinear
        simp: A'_def)

  have [iff]: \<open>kraus_family B'\<close>
    by (auto intro!: kraus_family_reconstruct_is_family assms kraus_family_map_bounded_clinear
        simp: B'_def)
  have \<open>kraus_family_tensor (kraus_family_flatten A') (kraus_family_flatten B') ~ kraus_family_tensor A' B'\<close>
    by (auto intro!: kraus_tensor_cong kraus_equivalent_kraus_family_flatten_left kraus_equivalent_reflI)
  then have [simp]: \<open>kraus_family_map (kraus_family_flatten (kraus_family_tensor (kraus_family_flatten A') (kraus_family_flatten B')))
          = kraus_family_map (kraus_family_tensor A' B')\<close>
    by (simp add: kraus_equivalent_def kraus_family_flatten_same_map)

  have \<open>((\<lambda>(EF,ab). sandwich_tc EF \<tau>) has_sum tensor\<tau>) A'B'\<close>
    using kraus_family_map_has_sum[of \<tau> \<open>kraus_family_tensor_raw \<EE> \<FF>\<close>]
    apply (auto intro!: simp: A'B'_def tensor\<tau>_def kraus_family_tensor_raw.rep_eq)
    apply (transfer fixing: )

    by (metis (mono_tags, lifting) A'B'_def \<open>kraus_family A'\<close> \<open>kraus_family B'\<close> kraus_family_kraus_family_tensor kraus_family_map_has_sum)
  then have \<open>((\<lambda>((E,a), (F,b)). sandwich_tc (E \<otimes>\<^sub>o F) \<tau>) has_sum A'B'\<tau>) (A' \<times> B')\<close>
    apply (subst (asm) kraus_family_tensor_def)
    apply (subst (asm) has_sum_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  then have \<open>((\<lambda>((E,a), (F,b)). sandwich_tc (f a \<otimes>\<^sub>o g b) \<tau>) has_sum A'B'\<tau>) (A' \<times> B')\<close>
    apply (rule has_sum_cong[THEN iffD1, rotated -1])
    by (auto simp: A'_def B'_def)
  then have \<open>((\<lambda>((E,a), (F,b)). sandwich_tc (f a \<otimes>\<^sub>o g b) \<tau>) has_sum kraus_map_apply (kraus_map_tensor \<EE> \<FF>) \<tau>) (A' \<times> B')\<close>
    unfolding A'B'\<tau>_def
    apply (transfer' fixing: f g)
    by simp
  then show ?thesis
    by (auto intro!: simp: A'_def B'_def has_sum_reindex inj_on_def o_def case_prod_unfold
        simp flip: map_prod_image)
qed *)

lemma kraus_map_apply_tensor_has_sum:
  assumes \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum kraus_family_map \<EE> \<rho>) A\<close>
  assumes \<open>\<And>\<sigma>. ((\<lambda>b. sandwich_tc (g b) \<sigma>) has_sum kraus_family_map \<FF> \<sigma>) B\<close>
  shows \<open>((\<lambda>(a,b). sandwich_tc (f a \<otimes>\<^sub>o g b) \<tau>) has_sum kraus_family_map (kraus_family_tensor \<EE> \<FF>) \<tau>) (A\<times>B)\<close>


lemma kraus_map_apply_tensor_id_right_has_sum:
  assumes \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum kraus_family_map \<EE> \<rho>) A\<close>
  shows \<open>((\<lambda>a. sandwich_tc (f a \<otimes>\<^sub>o id_cblinfun) \<tau>) has_sum kraus_family_map (kraus_family_tensor \<EE> kraus_family_id) \<tau>) A\<close>
proof -
  have \<open>((\<lambda>a. sandwich_tc id_cblinfun \<rho>) has_sum kraus_family_map kraus_family_id \<rho>) {()}\<close> for \<rho>
    by simp
  with assms have \<open>((\<lambda>(a, b). sandwich_tc (f a \<otimes>\<^sub>o id_cblinfun) \<tau>) has_sum kraus_family_map (kraus_family_tensor \<EE> kraus_family_id) \<tau>) (A \<times> {()})\<close>
    by (rule kraus_map_apply_tensor_has_sum)
  then show ?thesis
    by (simp add: has_sum_reindex inj_on_def o_def flip: image_Pair_const)
qed

lemma image_Pair_const': "(\<lambda>x. (c, x)) ` A = {c} \<times> A"
  by blast

lemma kraus_map_apply_tensor_id_left_has_sum:
  assumes \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum kraus_family_map \<EE> \<rho>) A\<close>
  shows \<open>((\<lambda>a. sandwich_tc (id_cblinfun \<otimes>\<^sub>o f a) \<tau>) has_sum kraus_family_map (kraus_family_tensor kraus_family_id \<EE>) \<tau>) A\<close>
proof -
  have \<open>((\<lambda>a. sandwich_tc id_cblinfun \<rho>) has_sum kraus_family_map kraus_family_id \<rho>) {()}\<close> for \<rho>
    by simp
  from this assms have \<open>((\<lambda>(a, b). sandwich_tc (id_cblinfun \<otimes>\<^sub>o f b) \<tau>) has_sum kraus_family_map (kraus_family_tensor kraus_family_id \<EE>) \<tau>) ({()} \<times> A)\<close>
    by (rule kraus_map_apply_tensor_has_sum)
  then show ?thesis
    by (simp add: has_sum_reindex inj_on_def o_def flip: image_Pair_const')
qed

lemma sgn_ket[simp]: \<open>sgn (ket x) = ket x\<close>
  by (simp add: sgn_div_norm)

lemma measure_first_kraus_map_apply_has_sum:
 \<open>((\<lambda>x. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) \<rho>) has_sum (kraus_family_map measure_first \<rho>)) UNIV\<close>
  using complete_measurement_has_sum[of \<open>range ket\<close>]
  by (auto intro!: kraus_map_apply_tensor_id_right_has_sum 
    simp: measure_first_def has_sum_reindex o_def)


lemma measure_first_kraus_map_apply: \<open>kraus_family_map measure_first \<rho> = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) \<rho>)\<close>
  by (metis (mono_tags, lifting) infsumI measure_first_kraus_map_apply_has_sum)

lemma measure_kraus_map_ket_butterfly: 
  assumes \<open>is_ortho_set B\<close>
  assumes \<open>x \<in> B\<close> and \<open>y \<in> B\<close>
  shows \<open>kraus_family_map (complete_measurement B) (tc_butterfly x y) = 
      of_bool (x=y) *\<^sub>C tc_butterfly x x\<close>
proof -
  from assms have \<open>norm y \<noteq> 0\<close>
    by (auto simp: is_ortho_set_def)
  have *: \<open>sandwich_tc (selfbutter (sgn z)) (tc_butterfly x y) = of_bool (x=y) *\<^sub>C of_bool (x=z) *\<^sub>C tc_butterfly x y\<close> if \<open>z \<in> B\<close> for z
      apply (rule from_trace_class_inject[THEN iffD1])
      using assms
      apply (auto simp add: sandwich_tc_def compose_tcl.rep_eq compose_tcr.rep_eq tc_butterfly.rep_eq
          scaleR_scaleC scaleC_trace_class.rep_eq cdot_square_norm sgn_div_norm power2_eq_square
          is_ortho_set_def)
       apply (smt (verit, ccfv_SIG) \<open>norm y \<noteq> 0\<close> complex_vector.vector_space_assms(3) divideC_field_splits_simps_1(1) of_real_hom.hom_0)
      using that by presburger
  then show ?thesis
    by (auto simp: complete_measurement_apply assms infsum_single[where i=x])
qed


(* lemma measure_kraus_map_idem[simp]: \<open>kraus_family_comp measure_kraus_family measure_kraus_family = measure_kraus_family\<close>
proof (rule kraus_map_apply_inj, rule eq_from_separatingI2, rule separating_set_tc_butterfly_nested[OF separating_set_ket separating_set_ket])
  show \<open>bounded_clinear (kraus_map_apply (kraus_map_comp measure_kraus_family measure_kraus_family))\<close>
    by (intro bounded_linear_intros)
  show \<open>bounded_clinear (kraus_map_apply measure_kraus_family)\<close>
    by (intro bounded_linear_intros)
  fix g h :: \<open>'a ell2\<close> assume \<open>g \<in> range ket\<close> and \<open>h \<in> range ket\<close>
  then obtain x y where g_def: \<open>g = ket x\<close> and h_def: \<open>h = ket y\<close>
    by blast
  show \<open>kraus_map_apply (kraus_map_comp measure_kraus_family measure_kraus_family) (tc_butterfly g h) = kraus_map_apply measure_kraus_family (tc_butterfly g h)\<close>
    by (auto intro!: simp: kraus_map_apply_comp g_def h_def measure_kraus_map_ket_butterfly)
qed *)

(* lemma measure_first_kraus_map_idem[simp]: \<open>kraus_map_comp measure_first_kraus_map measure_first_kraus_map = measure_first_kraus_map\<close>
  by (simp add: measure_first_kraus_map_def flip: kraus_map_tensor_compose_distribute) *)

(* lemma measure_first_kraus_map_apply': \<open>kraus_map_apply measure_first_kraus_map \<rho> = 
  (\<Sum>\<^sub>\<infinity>x. tc_tensor (tc_butterfly (ket x) (ket x)) (sandwich_tc (tensor_ell2_left (ket x)* ) \<rho>))\<close>
  apply (simp add: measure_first_kraus_map_apply)
  apply (rule infsum_cong)
  apply (auto intro!: from_trace_class_inject[THEN iffD1] equal_ket cinner_ket_eqI
      simp: from_trace_class_sandwich_tc tc_tensor.rep_eq tc_butterfly.rep_eq sandwich_apply
      tensor_op_adjoint cblinfun_apply_cblinfun_compose tensor_op_ell2
      simp flip: tensor_ell2_ket)
  by (auto intro!: cinner_ket
      simp: tensor_op_adjoint tensor_op_ell2 cinner_ket
      simp flip: cinner_adj_left) *)

definition \<open>is_cq_operator \<rho> \<longleftrightarrow> \<rho> = kraus_family_map measure_first \<rho>\<close>

lemma is_cq_operator_0[simp]: \<open>is_cq_operator 0\<close>
  by (simp add: is_cq_operator_def)

(* typedef ('a,'b) cq_operator = \<open>Collect is_cq_operator :: (('a\<times>'b) ell2, ('a\<times>'b) ell2) trace_class set\<close>
  apply (rule exI[of _ 0])
  by simp
setup_lifting type_definition_cq_operator *)

definition mk_cq_operator :: \<open>('cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class) \<Rightarrow> (('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) trace_class\<close> where
  \<open>mk_cq_operator f = (if f abs_summable_on UNIV then (\<Sum>\<^sub>\<infinity>x. tc_tensor (tc_butterfly (ket x) (ket x)) (f x)) else 0)\<close>

lemma mk_cq_operator_abs_summable:
  fixes f :: \<open>'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class\<close>
  assumes \<open>f abs_summable_on UNIV\<close>
  shows \<open>(\<lambda>x. tc_tensor (tc_butterfly (ket x) (ket x)) (f x)) abs_summable_on UNIV\<close>
proof -
  have *: \<open>sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) (tc_tensor (tc_butterfly (ket y) (ket y)) (f y))
            = of_bool (y = x) *\<^sub>C tc_tensor (tc_butterfly (ket y) (ket y)) (f y)\<close> for x y
    apply (rule from_trace_class_inject[THEN iffD1])
    by (simp add: from_trace_class_sandwich_tc tc_tensor.rep_eq tc_butterfly.rep_eq sandwich_apply
        comp_tensor_op cinner_ket tensor_op_adjoint)
  show ?thesis
    using assms
    by (simp add: norm_tc_tensor norm_tc_butterfly * infsum_of_bool_scaleC flip: infsum_cblinfun_apply)
qed

(* lemma measure_kraus_map_ket_butterfly: \<open>kraus_map_apply measure_kraus_map *\<^sub>V tc_butterfly (ket x) (ket x) = tc_butterfly (ket x) (ket x)\<close>
proof -
  have *: \<open>sandwich_tc (selfbutter (ket y)) (tc_butterfly (ket x) (ket x)) = of_bool (x=y) *\<^sub>C tc_butterfly (ket x) (ket x)\<close> for y
    apply (rule from_trace_class_inject[THEN iffD1])
    by (simp add: sandwich_tc_def compose_tcl.rep_eq compose_tcr.rep_eq tc_butterfly.rep_eq)
  then show ?thesis
    by (simp add: measure_kraus_map_apply infsum_single[where i=x])
qed *)

lemma closed_is_cq_operator: \<open>closed (Collect is_cq_operator :: (('a \<times> 'b) ell2, _) trace_class set)\<close>
proof (intro closed_sequential_limits[THEN iffD2] allI impI CollectI, elim conjE)
  fix f :: \<open>nat \<Rightarrow> _\<close> and l :: \<open>(('a \<times> 'b) ell2, ('a \<times> 'b) ell2) trace_class\<close> 
  assume \<open>f \<longlonglongrightarrow> l\<close>
  assume f_is_cq: \<open>\<forall>n. f n \<in> Collect is_cq_operator\<close>
  from \<open>f \<longlonglongrightarrow>l\<close>
  have \<open>(\<lambda>n. kraus_map_apply measure_first_kraus_map (f n)) \<longlonglongrightarrow> kraus_map_apply measure_first_kraus_map l\<close>
    apply (rule isCont_tendsto_compose[rotated])
    by (intro clinear_continuous_at bounded_linear_intros)
  moreover have \<open>kraus_map_apply measure_first_kraus_map (f n) = f n\<close> for n
    by (metis f_is_cq is_cq_operator_def mem_Collect_eq)
  ultimately have \<open>f \<longlonglongrightarrow> kraus_map_apply measure_first_kraus_map l\<close>
    by simp
  with \<open>f \<longlonglongrightarrow>l\<close>
  have \<open>kraus_map_apply measure_first_kraus_map l = l\<close>
    by (simp add: LIMSEQ_unique)
  then show \<open>is_cq_operator l\<close>
    by (simp add: is_cq_operator_def)
qed

lemma is_cq_operator_scaleC: \<open>is_cq_operator (c *\<^sub>C t)\<close> if \<open>is_cq_operator t\<close>
  using that
  by (simp add: is_cq_operator_def clinear.scaleC bounded_clinear.clinear kraus_map_apply_bounded_clinear)

lemma is_cq_operator_plus: \<open>is_cq_operator (t + u)\<close> if \<open>is_cq_operator t\<close> and \<open>is_cq_operator u\<close>
  using that
  by (simp add: is_cq_operator_def complex_vector.linear_add bounded_clinear.clinear kraus_map_apply_bounded_clinear)

lemma is_cq_operator_butterfly[iff]: \<open>is_cq_operator (tc_tensor (tc_butterfly (ket x) (ket x)) t)\<close>
  by (simp add: is_cq_operator_def measure_first_kraus_map_def kraus_map_tensor measure_kraus_map_ket_butterfly)

lemma csubspace_is_cq_operator[iff]: \<open>csubspace (Collect is_cq_operator :: (('a \<times> 'b) ell2, _) trace_class set)\<close>
  by (auto intro!: complex_vector.subspaceI simp: is_cq_operator_plus is_cq_operator_scaleC)

lemma mk_cq_operator_is_cq_operator: \<open>is_cq_operator (mk_cq_operator f)\<close>
  for f :: \<open>'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class\<close>
proof (cases \<open>f abs_summable_on UNIV\<close>)
  case True
  have \<open>(\<Sum>\<^sub>\<infinity>x. tc_tensor (tc_butterfly (ket x) (ket x)) (f x)) \<in> Collect is_cq_operator\<close>
    apply (rule infsum_in_closed_csubspaceI)
    by (auto intro!: csubspace_is_cq_operator closed_is_cq_operator simp: closed_csubspace_def)
  then show ?thesis
    by (simp add: mk_cq_operator_def)
next
  case False
  then show ?thesis
    by (simp add: mk_cq_operator_def)
qed

(* (* lift_definition mk_cq_operator :: \<open>('cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class) \<Rightarrow> ('cl, 'qu) cq_operator\<close> is
  \<open>\<lambda>f. if f abs_summable_on UNIV then (\<Sum>\<^sub>\<infinity>x. tc_tensor (tc_butterfly (ket x) (ket x)) (f x)) else 0\<close> *)
proof -
  (* have *: \<open>sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) (tc_tensor (tc_butterfly (ket y) (ket y)) (f y))
            = of_bool (y = x) *\<^sub>C tc_tensor (tc_butterfly (ket y) (ket y)) (f y)\<close> for x y
    apply (rule from_trace_class_inject[THEN iffD1])
    by (simp add: from_trace_class_sandwich_tc tc_tensor.rep_eq tc_butterfly.rep_eq sandwich_apply
        comp_tensor_op cinner_ket tensor_op_adjoint)
  then have **: \<open>tc_tensor (tc_butterfly (ket x) (ket x)) (f x) =
         kraus_map_apply (kraus_map_tensor measure_kraus_map kraus_map_id) (\<Sum>\<^sub>\<infinity>y. tc_tensor (tc_butterfly (ket y) (ket y)) (f y))\<close> 
    if \<open>f abs_summable_on UNIV\<close> for x
    apply (subst infsum_bounded_linear[where f=\<open>sandwich_tc _\<close>, symmetric])
    by (auto intro!: bounded_linear_intros mk_cq_operator_abs_summable[THEN abs_summable_summable] that
        simp: o_def infsum_of_bool_scaleC) *)


  have **: \<open>kraus_map_apply (kraus_map_tensor measure_kraus_map kraus_map_id) (\<Sum>\<^sub>\<infinity>y. tc_tensor (tc_butterfly (ket y) (ket y)) (f y))
     = (\<Sum>\<^sub>\<infinity>y. tc_tensor (tc_butterfly (ket y) (ket y)) (f y))\<close> if \<open>f abs_summable_on UNIV\<close>
  proof -
    have sum: \<open>(\<lambda>y. tc_tensor (tc_butterfly (ket y) (ket y)) (f y)) summable_on UNIV\<close>
      apply (rule abs_summable_summable)
      by (intro mk_cq_operator_abs_summable that)
    have \<open>kraus_map_apply (kraus_map_tensor measure_kraus_map kraus_map_id) (\<Sum>\<^sub>\<infinity>y. tc_tensor (tc_butterfly (ket y) (ket y)) (f y))
        = (\<Sum>\<^sub>\<infinity>y. kraus_map_apply (kraus_map_tensor measure_kraus_map kraus_map_id) (tc_tensor (tc_butterfly (ket y) (ket y)) (f y)))\<close>
      by (auto intro!: infsum_cblinfun_apply[symmetric] sum)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>y. tc_tensor (kraus_map_apply measure_kraus_map (tc_butterfly (ket y) (ket y))) (f y))\<close>
      by (metis (no_types, lifting) kraus_map_id_apply kraus_map_tensor)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>y. tc_tensor (tc_butterfly (ket y) (ket y)) (f y))\<close>
      by (simp add: measure_kraus_map_ket_butterfly)
    finally show ?thesis
      by -
  qed
  show ?thesis
    by (auto intro!: infsum_cong simp: is_cq_operator_def measure_first_kraus_map_def mk_cq_operator_def 
      abs_summable_summable norm_tc_tensor norm_tc_butterfly mk_cq_operator_abs_summable ** )
qed *)


definition cq_operator_at :: \<open>(('cl \<times> 'qu) ell2, ('cl \<times> 'qu) ell2) trace_class \<Rightarrow> 'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class\<close> where
  \<open>cq_operator_at \<rho> c = sandwich_tc (tensor_ell2_left (ket c)*) \<rho>\<close>

(* lift_definition cq_operator_at :: \<open>('cl, 'qu) cq_operator \<Rightarrow> 'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class\<close> is cq_operator_at0. *)


lemma cq_operator_at_mk_cq_operator:
  assumes \<open>f abs_summable_on UNIV\<close>
  shows \<open>cq_operator_at (mk_cq_operator f) = f\<close>
proof -
  have [simp]: \<open>(\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o from_trace_class (f x)) summable_on UNIV\<close>
    apply (rule abs_summable_summable)
    using assms by (simp add: tensor_op_norm norm_butterfly from_trace_class_abs_summable)
  have [simp]: \<open>(\<lambda>xa. X o\<^sub>C\<^sub>L (selfbutter (ket xa) \<otimes>\<^sub>o from_trace_class (f xa))) summable_on UNIV\<close> for X
    by (auto intro!: summable_cblinfun_compose_left)
  have [simp]: \<open>(\<lambda>x. tc_tensor (tc_butterfly (ket x) (ket x)) (f x)) summable_on UNIV\<close>
    apply (rule abs_summable_summable)
    using assms by (simp add: norm_tc_tensor norm_tc_butterfly)
  have 1: \<open>from_trace_class (\<Sum>\<^sub>\<infinity>x. tc_tensor (tc_butterfly (ket x) (ket x)) (f x)) = 
      (\<Sum>\<^sub>\<infinity>x. selfbutter (ket x) \<otimes>\<^sub>o from_trace_class (f x))\<close>
    apply (subst from_trace_class_infsum)
    by (simp_all add: tc_tensor.rep_eq tc_butterfly.rep_eq)
  have 2: \<open>tensor_ell2_left (ket x)* o\<^sub>C\<^sub>L selfbutter (ket y) \<otimes>\<^sub>o from_trace_class (f y) o\<^sub>C\<^sub>L tensor_ell2_left (ket x)
      = of_bool (y=x) *\<^sub>C from_trace_class (f y)\<close> for x y
    by (auto intro!: equal_ket simp: tensor_op_ell2)
  show ?thesis
    apply (rule ext)
    apply (rule from_trace_class_inject[THEN iffD1])
    by (simp add: cq_operator_at_def mk_cq_operator_def assms 1 2
        infsum_of_bool_scaleC sandwich_tc_def compose_tcl.rep_eq compose_tcr.rep_eq
        flip: infsum_cblinfun_compose_left infsum_cblinfun_compose_right)
qed

lemma cq_operator_at_abs_summable[iff]: \<open>cq_operator_at \<rho> abs_summable_on UNIV\<close>
proof -
  define \<rho>' where \<open>\<rho>' = sandwich_tc swap_ell2 \<rho>\<close>
  have *: \<open>sandwich_tc (tensor_ell2_left (ket x)*) \<rho> = sandwich_tc (tensor_ell2_right (ket x)*) \<rho>'\<close> for x
    by (auto intro!: equal_ket cinner_ket_eqI from_trace_class_inject[THEN iffD1]
        simp: \<rho>'_def from_trace_class_sandwich_tc sandwich_apply
        simp flip: cinner_adj_left)
  have \<open>(\<lambda>x. sandwich_tc (tensor_ell2_right (ket x)*) \<rho>') abs_summable_on UNIV\<close>
    using partial_trace_abs_summable[of \<rho>']
    by (simp add: sandwich_apply sandwich_tc_def)
  then have \<open>(\<lambda>x. sandwich_tc (tensor_ell2_left (ket x)*) \<rho>) abs_summable_on UNIV\<close>
    by (simp add: * )
  then show ?thesis
    by (simp add: cq_operator_at_def)
qed

lemma mk_cq_operator_cq_operator_at: 
  assumes \<open>is_cq_operator \<rho>\<close>
  shows  \<open>mk_cq_operator (cq_operator_at \<rho>) = \<rho>\<close>
proof -
  have 1: \<open>tc_tensor (tc_butterfly (ket x) (ket x)) (sandwich_tc (tensor_ell2_left (ket x)*) \<rho>)
        = sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) \<rho>\<close> for x
    apply (auto intro!: from_trace_class_inject[THEN iffD1] equal_ket cinner_ket_eqI
        simp: tc_tensor.rep_eq from_trace_class_sandwich_tc
        tc_butterfly.rep_eq sandwich_apply cblinfun_apply_cblinfun_compose tensor_op_ell2
        tensor_op_adjoint cinner_ket
        simp flip: tensor_ell2_ket)
    by (simp_all add: tensor_op_adjoint tensor_op_ell2 cinner_ket flip: cinner_adj_left)

  have \<open>mk_cq_operator (cq_operator_at \<rho>) = (\<Sum>\<^sub>\<infinity>x. tc_tensor (tc_butterfly (ket x) (ket x)) (cq_operator_at \<rho> x))\<close>
    by (simp add: mk_cq_operator_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. tc_tensor (tc_butterfly (ket x) (ket x)) (sandwich_tc (tensor_ell2_left (ket x)*) \<rho>))\<close>
    by (simp add: cq_operator_at_def)
  also have \<open>\<dots> = kraus_map_apply measure_first_kraus_map \<rho>\<close>
    by (simp add: measure_first_kraus_map_apply 1)
  also have \<open>\<dots> = \<rho>\<close>
    using assms is_cq_operator_def by force
  finally show ?thesis
    by -
qed

(*
(* TODO move *)
lemma infsum_tc_norm_bounded_abs_summable': (* TODO replace infsum_tc_norm_bounded_abs_summable *)
  fixes A :: \<open>'a \<Rightarrow> ('b::chilbert_space, 'b::chilbert_space) trace_class\<close>
  assumes bound_B: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> M \<Longrightarrow> norm (\<Sum>x\<in>F. A x) \<le> B\<close>
  shows \<open>A abs_summable_on M\<close>
proof -
  wlog A_pos: \<open>\<forall>x. A x \<ge> 0\<close> generalizing A
  proof -
    obtain A1 A2 A3 A4 where A_decomp: \<open>A x = A1 x - A2 x + \<i> *\<^sub>C A3 x - \<i> *\<^sub>C A4 x\<close>
      and pos: \<open>A1 x \<ge> 0\<close> \<open>A2 x \<ge> 0\<close> \<open>A3 x \<ge> 0\<close> \<open>A4 x \<ge> 0\<close> for x
      apply atomize_elim
      apply (auto intro!: choice4' simp: simp flip: all_conj_distrib)
      using trace_class_decomp_4pos'[of \<open>A _\<close>] by blast


    have \<open>norm (of_nat (\<EE> x) *\<^sub>C sandwich_tc x A) 
      \<le> norm (of_nat (\<EE> x) *\<^sub>C sandwich_tc x A1)
      + norm (of_nat (\<EE> x) *\<^sub>C sandwich_tc x A2)
      + norm (of_nat (\<EE> x) *\<^sub>C sandwich_tc x A3)
      + norm (of_nat (\<EE> x) *\<^sub>C sandwich_tc x A4)\<close> 
      (is \<open>_ \<le> ?S x\<close>) for x
      by (auto simp add: A_decomp cblinfun.add_right cblinfun.diff_right cblinfun.scaleC_right
          scaleC_add_right scaleC_diff_right norm_mult
          intro!: norm_triangle_le norm_triangle_le_diff)
    then have *: \<open>norm (of_nat (\<EE> x) *\<^sub>C sandwich_tc x A) \<le> norm (?S x)\<close> for x
      by force
    show ?thesis
      apply (rule abs_summable_on_comparison_test[OF _ *])
      by (intro abs_summable_on_add abs_summable_norm abs_summable_on_scaleC_right hypothesis pos)
  qed

  define  *)

(*lemma is_cq_operator_compose:
  assumes \<open>is_cq_operator a\<close>
  assumes \<open>is_cq_operator b\<close>
  shows \<open>is_cq_operator (tc_compose a b)\<close>
proof -
  have asum: \<open>a = kraus_map_apply measure_first_kraus_map a\<close>
    by (metis assms(1) is_cq_operator_def)
  have bsum: \<open>b = kraus_map_apply measure_first_kraus_map b\<close>
    by (metis assms(2) is_cq_operator_def)
  have [simp]: \<open>bounded_linear
          (\<lambda>xa. tc_tensor (tc_butterfly (ket x) (ket x)) (sandwich_tc (tensor_ell2_left (ket x)* ) *\<^sub>V xa))\<close> for x
    by (auto intro!: bounded_clinear.bounded_linear bounded_linear_intros simp: )
  have [simp]: \<open>(\<lambda>x. tc_tensor (tc_butterfly (ket x) (ket x))
                      (sandwich_tc (tensor_ell2_left (ket x)* ) *\<^sub>V d)) summable_on UNIV\<close> for d
  proof -
    wlog d_pos: \<open>d \<ge> 0\<close> generalizing d
    proof -
    obtain d1 d2 d3 d4 where d_decomp: \<open>d = d1 - d2 + \<i> *\<^sub>C d3 - \<i> *\<^sub>C d4\<close>
      and pos: \<open>d1 \<ge> 0\<close> \<open>d2 \<ge> 0\<close> \<open>d3 \<ge> 0\<close> \<open>d4 \<ge> 0\<close>
      apply atomize_elim using trace_class_decomp_4pos'[of d] by blast
    show ?thesis
      by (auto intro!: 
          summable_on_diff summable_on_add hypothesis pos
          simp: d_decomp cblinfun.add_right cblinfun.diff_right cblinfun.scaleC_right
          scaleC_add_right scaleC_diff_right
          bounded_cbilinear.add_right[OF bounded_cbilinear_tc_tensor]
          bounded_cbilinear.diff_right[OF bounded_cbilinear_tc_tensor]
          bounded_cbilinear.scaleC_right[OF bounded_cbilinear_tc_tensor])
  qed
  fix d :: \<open>(('c \<times> 'd) ell2, ('c \<times> 'd) ell2) trace_class\<close>
  assume \<open>d \<ge> 0\<close>
  show \<open>(\<lambda>x. tc_tensor (tc_butterfly (ket x) (ket x)) (sandwich_tc (tensor_ell2_left (ket x)* ) *\<^sub>V d)) summable_on UNIV\<close>
    apply (rule abs_summable_summable)
    apply (rule infsum_tc_norm_bounded_abs_summable)
     apply (auto intro!: tc_tensor_pos sandwich_tc_pos \<open>d \<ge> 0\<close> simp: )
    thm infsum_tc_norm_bounded_abs_summable
    by -x
    apply (rule abs_summable_summable)
    apply (auto intro!: simp: norm_tc_tensor norm_tc_butterfly)
    apply (rule infsum_tc_norm_bounded_abs_summable)
(* TODO can infsum_tc_norm_bounded_abs_summable be generalized to drop the posititivy condition?
from bound_B, bound_B also follows for hermitian and anti-herm part.
from those, bound_B follows for pos + neg part
then conclusion follows for each of the parts via existing lemma
then conclusion follows.

OR: decompose d into four positive parts

 *)
    by x
  have [simp]: \<open>(\<lambda>x. tc_tensor (tc_butterfly (ket x) (ket x))
          (tc_compose (sandwich_tc (tensor_ell2_left (ket x)* ) *\<^sub>V a)
            (sandwich_tc (tensor_ell2_left (ket x)* ) *\<^sub>V b))) summable_on UNIV\<close>
    by xxx



  have **: \<open>sandwich_tc (tensor_ell2_left (ket x)* ) *\<^sub>V
           tc_tensor (tc_butterfly (ket y) (ket y)) b =
of_bool (y=x) *\<^sub>C b
\<close> for x y b
    apply (rule from_trace_class_inject[THEN iffD1])
    by (auto intro!: equal_ket 
        simp add: from_trace_class_sandwich_tc sandwich_apply tc_tensor.rep_eq tc_butterfly.rep_eq
        tensor_op_ell2
        simp flip: tensor_ell2_ket)    
    
    have *: \<open>tc_compose a b = (\<Sum>\<^sub>\<infinity>x.
       tc_tensor (tc_butterfly (ket x) (ket x))
        (tc_compose (sandwich_tc (tensor_ell2_left (ket x)* ) *\<^sub>V a)
          (sandwich_tc (tensor_ell2_left (ket x)* ) *\<^sub>V b)))\<close>
    apply (subst asum, subst bsum)
    apply (simp add: measure_first_kraus_map_apply')
    apply (subst infsum_bounded_linear[symmetric, where f=\<open>\<lambda>x. tc_compose _ x\<close>])
      apply (auto intro!: bounded_clinear_tc_compose_right bounded_clinear.bounded_linear
        simp: o_def)
    apply (subst infsum_bounded_linear[symmetric, where f=\<open>\<lambda>x. tc_compose x _\<close>])
      apply (auto intro!: bounded_clinear_tc_compose_left bounded_clinear_tc_compose_right 
        bounded_clinear.bounded_linear bounded_cbilinear_tc_compose 
        simp: o_def comp_tc_tensor tc_tensor_scaleC_left cinner_ket infsum_of_bool_scaleC)
    by -

  have \<open>\<dots> = kraus_map_apply measure_first_kraus_map *\<^sub>V \<dots>\<close>
    apply (simp add: measure_first_kraus_map_apply')
    apply (subst infsum_bounded_linear[symmetric, where f=\<open>\<lambda>x. tc_tensor _ (sandwich_tc _ x)\<close>])
    by (auto intro!: simp: o_def ** tc_tensor_scaleC_right infsum_of_bool_scaleC)

  then show ?thesis
    by (simp add: is_cq_operator_def * )
qed
*)

lemma mk_cq_operator_tc_compose: 
  assumes \<open>is_cq_operator a\<close> and \<open>is_cq_operator b\<close>
  shows \<open>mk_cq_operator (\<lambda>c. tc_compose (cq_operator_at a c) (cq_operator_at b c)) = tc_compose a b\<close> (is \<open>?lhs = _\<close>)
proof -
  define a' b' where \<open>a' = cq_operator_at a\<close> and \<open>b' = cq_operator_at b\<close>
  have a'sum: \<open>a' abs_summable_on UNIV\<close>
    by (simp add: a'_def cq_operator_at_abs_summable)
  have b'sum: \<open>b' abs_summable_on UNIV\<close>
    by (simp add: b'_def cq_operator_at_abs_summable)
  have sum1: \<open>(\<lambda>x. tc_tensor (tc_butterfly (ket x) (ket x)) (a' x)) summable_on UNIV\<close>
    using a'sum abs_summable_summable mk_cq_operator_abs_summable by fastforce
  have sum2: \<open>(\<lambda>y. tc_tensor (tc_butterfly (ket y) (ket y)) (b' y)) summable_on UNIV\<close>
    using b'sum abs_summable_summable mk_cq_operator_abs_summable by fastforce

  have \<open>(\<lambda>x. norm (norm (a' x)) * norm (norm (b' x))) abs_summable_on UNIV\<close>
    apply (rule abs_summable_product')
    using a'sum b'sum by auto
  then have \<open>(\<lambda>x. tc_compose (a' x) (b' x)) abs_summable_on UNIV\<close>
    apply (rule abs_summable_on_comparison_test)
    by (simp add: norm_tc_compose)
  then have summable: \<open>(\<lambda>x. tc_compose (a' x) (b' x)) abs_summable_on UNIV\<close>
    by simp

  have \<open>?lhs = (\<Sum>\<^sub>\<infinity>x. tc_tensor (tc_butterfly (ket x) (ket x)) (tc_compose (a' x) (b' x)))\<close>
    by (simp add: summable mk_cq_operator_def flip: a'_def b'_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. tc_compose (tc_tensor (tc_butterfly (ket x) (ket x)) (a' x))
                                    (tc_tensor (tc_butterfly (ket x) (ket x)) (b' x)))\<close>
    by (simp add: comp_tc_tensor)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. of_bool (y=x) *\<^sub>C tc_compose (tc_tensor (tc_butterfly (ket x) (ket x)) (a' x))
                                    (tc_tensor (tc_butterfly (ket x) (ket x)) (b' x)))\<close>
    by (auto intro!: infsum_cong simp: infsum_of_bool_scaleC)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. tc_compose (tc_tensor (tc_butterfly (ket x) (ket x)) (a' x))
                                          (tc_tensor (tc_butterfly (ket y) (ket y)) (b' y)))\<close>
    by (auto intro!: infsum_cong simp: comp_tc_tensor comp_tc_butterfly cinner_ket)
  also have \<open>\<dots> = tc_compose (\<Sum>\<^sub>\<infinity>x. tc_tensor (tc_butterfly (ket x) (ket x)) (a' x))
                             (\<Sum>\<^sub>\<infinity>y. tc_tensor (tc_butterfly (ket y) (ket y)) (b' y))\<close>
    apply (subst infsum_bounded_linear[symmetric, where f=\<open>\<lambda>x. tc_compose x _\<close>, unfolded o_def])
      apply ((intro bounded_linear_intros sum1)+)[2]
    apply (subst infsum_bounded_linear[symmetric, where f=\<open>\<lambda>x. tc_compose _ x\<close>, unfolded o_def])
      apply ((intro bounded_linear_intros sum2)+)[2]
    by rule
  also have \<open>\<dots> = tc_compose (mk_cq_operator a') (mk_cq_operator b')\<close>
    by (simp add: mk_cq_operator_def a'sum b'sum)
  also have \<open>\<dots> = tc_compose a b\<close>
    by (simp add: mk_cq_operator_cq_operator_at a'_def b'_def assms)
  finally show ?thesis
    by -
qed

(* instantiation cq_operator :: (type,type) complex_algebra begin
lift_definition zero_cq_operator :: \<open>('a,'b) cq_operator\<close> is 0
  by auto
lift_definition plus_cq_operator :: \<open>('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator\<close> is
  plus
  by (simp add: is_cq_operator_def cblinfun.add_right)
lift_definition minus_cq_operator :: \<open>('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator\<close> is
  minus
  by (simp add: is_cq_operator_def cblinfun.diff_right)
lift_definition uminus_cq_operator :: \<open>('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator\<close> is
  uminus
  by (simp add: is_cq_operator_def cblinfun.minus_right)
lift_definition scaleC_cq_operator :: \<open>complex \<Rightarrow> ('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator\<close> is
  scaleC
  by (simp add: cblinfun.scaleC_right is_cq_operator_def)
lift_definition scaleR_cq_operator :: \<open>real \<Rightarrow> ('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator\<close> is
  scaleR
  by (metis Abs_cq_operator_inverse Rep_cq_operator scaleC_cq_operator.rep_eq scaleR_scaleC)
lift_definition times_cq_operator :: \<open>('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator \<Rightarrow> ('a,'b) cq_operator\<close> is
  (* \<open>\<lambda>a b x. tc_compose (a x) (b x)\<close> *)
(* proof -
  fix a b :: \<open>'a \<Rightarrow> ('b ell2, 'b ell2) trace_class\<close>
  assume asum: \<open>a abs_summable_on UNIV\<close>
  assume bsum: \<open>b abs_summable_on UNIV\<close>
  have \<open>(\<lambda>x. norm (norm (a x)) * norm (norm (b x))) abs_summable_on UNIV\<close>
    apply (rule abs_summable_product')
    using asum bsum by auto
  then have \<open>(\<lambda>x. tc_compose (a x) (b x)) abs_summable_on UNIV\<close>
    apply (rule abs_summable_on_comparison_test)
    by (simp add: norm_tc_compose)
  then show \<open>(\<lambda>x. tc_compose (a x) (b x)) abs_summable_on UNIV\<close>
    by simp
qed *)
  tc_compose
proof -
  fix a b :: \<open>(('a \<times> 'b) ell2, ('a \<times> 'b) ell2) trace_class\<close>
  assume \<open>a \<in> Collect is_cq_operator\<close>
  then obtain a' where a': \<open>a = Rep_cq_operator a'\<close>
    using Rep_cq_operator_cases by blast
  assume \<open>b \<in> Collect is_cq_operator\<close>
  then obtain b' where b': \<open>b = Rep_cq_operator b'\<close>
    using Rep_cq_operator_cases by blast
  have *: \<open>tc_compose a b =
    Rep_cq_operator (mk_cq_operator
     (\<lambda>c. tc_compose (cq_operator_at a' c) (cq_operator_at b' c)))\<close>
    by (simp add: mk_cq_operator_tc_compose a' b')
  have \<open>is_cq_operator (tc_compose a b)\<close>
    apply (simp add: * )
    using Rep_cq_operator by blast
  then show \<open>tc_compose a b \<in> Collect is_cq_operator\<close>
    by simp
qed

instance
proof intro_classes
  fix a b c :: \<open>('a, 'b) cq_operator\<close>
  show \<open>(( *\<^sub>R) r :: ('a, 'b) cq_operator \<Rightarrow> _) = ( *\<^sub>C) (complex_of_real r)\<close> for r :: real
    apply (rule ext)
    apply transfer
    by (simp add: scaleR_scaleC)
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer
    by auto
  show \<open>a + b = b + a\<close>
    apply transfer
    by auto
  show \<open>0 + a = a\<close>
    apply transfer
    by auto
  show \<open>- a + a = 0\<close>
    apply transfer
    by auto
  show \<open>a - b = a + - b\<close>
    apply transfer
    by auto
  show \<open>s *\<^sub>C (a + b) = s *\<^sub>C a + s *\<^sub>C b\<close> for s :: complex
    apply transfer
    by (simp add: complex_vector.vector_space_assms(1))
  show \<open>(s + t) *\<^sub>C a = s *\<^sub>C a + t *\<^sub>C a\<close> for s t :: complex
    apply transfer
    by (simp add: complex_vector.vector_space_assms(2))
  show \<open>s *\<^sub>C t *\<^sub>C a = (s * t) *\<^sub>C a\<close> for s t :: complex
    apply transfer
    by auto
  show \<open>1 *\<^sub>C a = a\<close>
    apply transfer
    by auto
  show \<open>a * b * c = a * (b * c)\<close>
    apply transfer
    apply (thin_tac _)+
    apply transfer
    by (simp add: cblinfun_compose_assoc)
  show \<open>(a + b) * c = a * c + b * c\<close>
    apply transfer
    apply (thin_tac _)+
    apply transfer
    using cblinfun_compose_add_left by blast
  show \<open>a * (b + c) = a * b + a * c\<close>
    apply transfer
    apply (thin_tac _)+
    apply transfer
    by (meson cblinfun_compose_add_right)
  show \<open>s *\<^sub>C a * b = s *\<^sub>C (a * b)\<close> for s :: complex
    apply transfer
    apply (thin_tac _)+
    apply transfer
    by simp
  show \<open>a * s *\<^sub>C b = s *\<^sub>C (a * b)\<close> for s :: complex
    apply transfer
    apply (thin_tac _)+
    apply transfer
    by simp
qed
end *)

(* instantiation cq_operator :: (type,type) complex_normed_vector begin
lift_definition norm_cq_operator :: \<open>('a, 'b) cq_operator \<Rightarrow> real\<close> is norm.
  (* \<open>\<lambda>a. \<Sum>\<^sub>\<infinity>x. norm (a x)\<close>. *)
definition \<open>sgn_cq_operator a = a /\<^sub>R norm a\<close> for a :: \<open>('a, 'b) cq_operator\<close>
definition \<open>dist_cq_operator a b = norm (a - b)\<close> for a b :: \<open>('a, 'b) cq_operator\<close>
definition [code del]: "uniformity_cq_operator = (INF e\<in>{0<..}. principal {(x::('a,'b) cq_operator, y). dist x y < e})"
definition [code del]: "open_cq_operator U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e\<in>{0<..}. principal {(x, y). dist x y < e}. x' = x \<longrightarrow> y \<in> U)"
  for U :: "('a,'b) cq_operator set"
instance
proof intro_classes
  fix a b c :: \<open>('a, 'b) cq_operator\<close>
  show \<open>dist a b = norm (a - b)\<close>
    by (simp add: dist_cq_operator_def)
  show \<open>sgn a = a /\<^sub>R norm a\<close>
    by (simp add: sgn_cq_operator_def)
  show \<open>uniformity = (INF e\<in>{0<..}. principal {(x::('a,'b) cq_operator, y). dist x y < e})\<close>
    using uniformity_cq_operator_def by force
  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)\<close>
    for U :: "('a,'b) cq_operator set"
    by (simp add: open_cq_operator_def uniformity_cq_operator_def)
  show \<open>norm a = 0 \<longleftrightarrow> a = 0\<close>
    apply transfer
    by simp
(*   proof (transfer, rule iffI)
    fix a :: \<open>'a \<Rightarrow> ('b ell2, 'b ell2) trace_class\<close>
    assume summable: \<open>(\<lambda>x. a x) abs_summable_on UNIV\<close>
    assume \<open>(\<Sum>\<^sub>\<infinity>x. norm (a x)) = 0\<close>
    then have \<open>norm (a x) = 0\<close> for x
      using summable nonneg_infsum_le_0D by force
    then show \<open>a = (\<lambda>_. 0)\<close>
      using norm_eq_zero by blast
  next
    fix a :: \<open>'a \<Rightarrow> ('b ell2, 'b ell2) trace_class\<close>
    assume \<open>a = (\<lambda>_. 0)\<close>
    then show \<open>(\<Sum>\<^sub>\<infinity>x. norm (a x)) = 0\<close>
      by simp
  qed *)
  show \<open>norm (a + b) \<le> norm a + norm b\<close>
    apply transfer
    by (simp add: norm_triangle_ineq)
(*   proof transfer
    fix a b :: \<open>'a \<Rightarrow> ('b ell2, 'b ell2) trace_class\<close>
    assume asummable: \<open>(\<lambda>x. a x) abs_summable_on UNIV\<close>
    assume bsummable: \<open>(\<lambda>x. b x) abs_summable_on UNIV\<close>
    have \<open>(\<Sum>\<^sub>\<infinity>x. norm (a x + b x)) \<le> (\<Sum>\<^sub>\<infinity>x. norm (a x) + norm (b x))\<close>
      apply (rule infsum_mono)
      using abs_summable_add asummable bsummable apply blast
      using asummable bsummable summable_on_add apply blast
      by (simp add: norm_triangle_ineq)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. norm (a x)) + (\<Sum>\<^sub>\<infinity>x. norm (b x))\<close>
      using asummable bsummable by (rule infsum_add)
    finally show \<open>(\<Sum>\<^sub>\<infinity>x. norm (a x + b x)) \<le> (\<Sum>\<^sub>\<infinity>x. norm (a x)) + (\<Sum>\<^sub>\<infinity>x. norm (b x))\<close>
      by -
  qed *)
  show \<open>norm (r *\<^sub>R a) = \<bar>r\<bar> * norm a\<close> for r :: real
    apply transfer
    by (simp add: infsum_cmult_right')
  show \<open>norm (s *\<^sub>C a) = cmod s * norm a\<close> for s :: complex
    apply transfer
    by (simp add: infsum_cmult_right')
qed
end *)

(* lemma transfer_Cauchy_cq_operator[transfer_rule]:
  includes lifting_syntax
  shows \<open>(((=) ===> cr_cq_operator) ===> (\<longleftrightarrow>)) Cauchy Cauchy\<close>
  unfolding Cauchy_def dist_norm
  by transfer_prover *)

(* lemma tendsto_preserves_cq_operator: 
  assumes \<open>\<forall>\<^sub>F x in F. is_cq_operator (f x)\<close>
  assumes \<open>(f \<longlongrightarrow> L) F\<close>
  assumes \<open>F \<noteq> \<bottom>\<close>
  shows \<open>is_cq_operator L\<close>
proof -
  have 1: \<open>((\<lambda>x. kraus_map_apply measure_first_kraus_map (f x)) \<longlongrightarrow> L) F\<close>
    using assms(2) apply (rule Lim_transform_eventually)
    using assms(1) by (simp add: is_cq_operator_def)
  from assms(2)
  have 2: \<open>((\<lambda>x. kraus_map_apply measure_first_kraus_map (f x)) \<longlongrightarrow> kraus_map_apply measure_first_kraus_map L) F\<close>
    by (simp add: cblinfun.tendsto)
  from assms(3) 2 1
  have \<open>kraus_map_apply measure_first_kraus_map L = L\<close>
    by (rule tendsto_unique)
  then show ?thesis
    by (simp add: is_cq_operator_def)
qed *)

(* lemma transfer_convergent_cq_operator[transfer_rule]:
  includes lifting_syntax
  shows \<open>(((=) ===> cr_cq_operator) ===> (\<longleftrightarrow>)) convergent convergent\<close>
proof (rule rel_funI)
  fix x :: \<open>nat \<Rightarrow> (('a \<times> 'b) ell2, ('a \<times> 'b) ell2) trace_class\<close> and y :: \<open>nat \<Rightarrow> ('a, 'b) cq_operator\<close>
  assume [transfer_rule]: \<open>((=) ===> cr_cq_operator) x y\<close>
  then have x_cq: \<open>is_cq_operator (x n)\<close> for n
    by (metis Rep_cq_operator cr_cq_operator_def mem_Collect_eq rel_fun_eq_rel)
  show \<open>convergent x \<longleftrightarrow> convergent y\<close>
  proof (rule iffI)
    assume \<open>convergent x\<close>
    then obtain L where \<open>x \<longlonglongrightarrow> L\<close>
      using convergentD by blast
    then have \<open>is_cq_operator L\<close>
      apply (rule tendsto_preserves_cq_operator[rotated])
      by (simp_all add: x_cq)
    then obtain L' where [transfer_rule]: \<open>cr_cq_operator L L'\<close>
      by (metis Abs_cq_operator_inverse cr_cq_operator_def mem_Collect_eq)
    from \<open>x \<longlonglongrightarrow> L\<close>
    have \<open>y \<longlonglongrightarrow> L'\<close>
      apply (simp add: LIMSEQ_def dist_norm)
      by transfer
    then show \<open>convergent y\<close>
      using convergentI by blast
  next
    assume \<open>convergent y\<close>
    then obtain L where \<open>y \<longlonglongrightarrow> L\<close>
      using convergentD by blast
    then obtain L' where [transfer_rule]: \<open>cr_cq_operator L' L\<close>
      by (metis cr_cq_operator_def)
    from \<open>y \<longlonglongrightarrow> L\<close>
    have \<open>x \<longlonglongrightarrow> L'\<close>
      apply (simp add: LIMSEQ_def dist_norm)
      by transfer
    then show \<open>convergent x\<close>
      using convergentI by blast
  qed
qed *)


(* TODO name *)
(* lemma TODO_Cauchy[transfer_rule]:
  includes lifting_syntax
  shows \<open>(((=) ===> cr_trace_class\<inverse>\<inverse>) ===> (\<longrightarrow>)) Cauchy Cauchy\<close>
 *)  (* by xxx *)
(* proof (rule rel_funI) *)
  (* by xxx *)
(* proof -
  fix x y
  have *: \<open>(((=) ===> (=)) ===> (\<lambda>a b. a \<longrightarrow> b)) All All\<close>
    by x
  show ?thesis
  unfolding Cauchy_def dist_norm
  apply transfer_prover_start
                apply transfer_step+
  using *[transfer_rule] apply fail?
                apply transfer_step

  term Cauchy
 *)

(* instance cq_operator :: (type,type) cbanach
  apply intro_classes
  apply transfer
  using Cauchy_convergent by blast
  (* TODO make transfer rules for Cauchy and convergent *)
  (* by xxx *)
(* proof intro_classes
  fix F :: \<open>nat \<Rightarrow> ('a, 'b) cq_operator\<close>
  define f where \<open>f n x = cq_operator_at (F n) x\<close> for x n
  assume \<open>Cauchy F\<close>
  have cauchy_sum_f: \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>S. finite S \<longrightarrow> (\<Sum>x\<in>S. norm (f m x - f n x)) < e\<close> if \<open>e > 0\<close> for e
  proof -
    from \<open>Cauchy F\<close> that obtain M where cauchy_X: \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. norm (F m - F n) < e\<close>
      by (auto simp: Cauchy_iff)
    have \<open>(\<Sum>x\<in>S. norm (f m x - f n x)) < e\<close> if \<open>m \<ge> M\<close> and \<open>n \<ge> M\<close> and \<open>finite S\<close> for m n S
    proof -
      from cauchy_X have \<open>norm (F m - F n) < e\<close>
        using that by auto
      then have *: \<open>(\<Sum>\<^sub>\<infinity>x. norm (f m x - f n x)) < e\<close>
        unfolding f_def apply (transfer fixing: n m M) using that by auto
      have \<open>(\<Sum>x\<in>S. norm (f m x - f n x)) \<le> (\<Sum>\<^sub>\<infinity>x. norm (f m x - f n x))\<close>
        apply (rule finite_sum_le_infsum)
          apply (smt (verit, del_insts) f_def cq_operator_at mem_Collect_eq minus_cq_operator.rep_eq summable_on_cong)
        by (simp_all add: that)
      also have \<open>\<dots> < e\<close>
        using "*" by blast
      finally show ?thesis
        by -
    qed
    then show ?thesis
      by auto
  qed

  have cauchy_f: \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm (f m x - f n x) < e\<close> if \<open>e > 0\<close> for e
  proof -
    from cauchy_sum_f[OF \<open>e > 0\<close>]
    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. (\<Sum>x\<in>{x}. norm (f m x - f n x)) < e\<close>
      apply (rule ex_mono[rule_format, rotated])
      by blast
    then show ?thesis
      by simp
  qed

  have \<open>Cauchy (\<lambda>n. f n x)\<close> for x
    apply (rule CauchyI)
    using cauchy_f 
    by meson
  then have \<open>convergent (\<lambda>n. f n x)\<close> for x
    using Cauchy_convergent by blast
  then obtain l where f_l: \<open>(\<lambda>n. f n x) \<longlonglongrightarrow> l x\<close> for x
    apply atomize_elim apply (rule choice)
    using convergent_def by blast
  have X_l_conv: \<open>\<exists>M. \<forall>n\<ge>M. ((\<lambda>x. f n x - l x) abs_summable_on UNIV) \<and> (\<Sum>\<^sub>\<infinity>x. norm (f n x - l x)) < e\<close> if \<open>e > 0\<close> for e
  proof -
    define d where \<open>d = e/2\<close>
    then have \<open>d > 0\<close>
      using half_gt_zero that by blast
    from cauchy_sum_f[OF this] obtain M where f_sum_d: \<open>(\<Sum>x\<in>S. norm (f m x - f n x)) < d\<close> 
      if \<open>m\<ge>M\<close> and \<open>n\<ge>M\<close> and \<open>finite S\<close> for m n S
      by auto
    have \<open>(\<lambda>n. \<Sum>x\<in>S. norm (f m x - f n x)) \<longlonglongrightarrow> (\<Sum>x\<in>S. norm (f m x - l x))\<close> if \<open>m \<ge> M\<close> and \<open>finite S\<close> for m S
      by (intro tendsto_sum tendsto_norm tendsto_diff tendsto_const f_l)
    then have *: \<open>(\<Sum>x\<in>S. norm (f m x - l x)) \<le> d\<close> if \<open>m \<ge> M\<close> and \<open>finite S\<close> for m S
      apply (rule Lim_bounded[where M=M])
      using f_sum_d[OF \<open>m \<ge> M\<close> _ \<open>finite S\<close>] that
      using less_imp_le by auto
    then have **: \<open>(\<lambda>x. f m x - l x) abs_summable_on UNIV\<close> if \<open>m \<ge> M\<close> for m
      apply (subst abs_summable_iff_bdd_above)
      using that by fastforce
    then have \<open>(\<Sum>\<^sub>\<infinity>x. norm (f m x - l x)) \<le> d\<close> if \<open>m \<ge> M\<close> for m
      apply (rule infsum_le_finite_sums)
      using that * by auto
    then have \<open>(\<Sum>\<^sub>\<infinity>x. norm (f m x - l x)) < e\<close> if \<open>m \<ge> M\<close> for m
      using that \<open>0 < e\<close> by (fastforce simp: d_def)
    with ** show ?thesis
      by (auto intro!: exI[of _ M])
  qed

  have l_sum: \<open>(\<lambda>x. l x) abs_summable_on UNIV\<close>
  proof -
    from X_l_conv obtain M where \<open>((\<lambda>x. f M x - l x) abs_summable_on UNIV)\<close>
      by (meson gt_ex order_refl)
    moreover have \<open>f M abs_summable_on UNIV\<close>
      using f_def[abs_def] cq_operator_at by blast
    ultimately have \<open>(\<lambda>x. f M x - (f M x - l x)) abs_summable_on UNIV\<close>
      apply (rule_tac abs_summable_minus) by auto
    then show ?thesis
      by auto
  qed
  define L where \<open>L = Abs_cq_operator l\<close>
  have Ll: \<open>cq_operator_at L = l\<close>
    by (simp add: L_def l_sum Abs_cq_operator_inverse)
  have \<open>F \<longlonglongrightarrow> L\<close>
    apply (rule LIMSEQ_I)
    apply (simp add: norm_cq_operator.rep_eq minus_cq_operator.rep_eq Ll flip: f_def)
    using X_l_conv by fast
  then show \<open>convergent F\<close>
    using convergent_def by blast
qed *) *)

(* instantiation cq_operator :: (type,type) order begin
lift_definition less_eq_cq_operator :: \<open>('a, 'b) cq_operator \<Rightarrow> ('a, 'b) cq_operator \<Rightarrow> bool\<close> is less_eq.
  (* \<open>\<lambda>a b. \<forall>x. a x \<le> b x\<close>. *)
lift_definition less_cq_operator :: \<open>('a, 'b) cq_operator \<Rightarrow> ('a, 'b) cq_operator \<Rightarrow> bool\<close> is less.
  (* \<open>less_cq_operator a b \<longleftrightarrow> a \<le> b \<and> \<not> (b \<le> a)\<close> *)
instance
proof intro_classes
  fix x y z :: \<open>('a, 'b) cq_operator\<close>
  show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
    apply transfer
    by auto
  show \<open>x \<le> x\<close>
    by (simp add: less_eq_cq_operator.rep_eq)
  show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
    by (simp add: less_eq_cq_operator.rep_eq)
  show \<open>x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
    apply transfer
    by simp
qed
end *)

(* definition cq_operator_cases :: \<open>('cin \<Rightarrow> ('qin ell2, 'qin ell2) trace_class \<Rightarrow> ('cout,'qout) cq_operator)
                                    \<Rightarrow> ('cin,'qin) cq_operator \<Rightarrow> ('cout,'qout) cq_operator\<close> where
  \<open>cq_operator_cases f cqin = mk_cq_operator (\<lambda>cout. (\<Sum>\<^sub>\<infinity>cin. cq_operator_at (f cin (cq_operator_at cqin cin)) cout))\<close> *)

(* lift_definition cq_operator_cases :: \<open>('cin \<Rightarrow> ('qin ell2, 'qin ell2) trace_class \<Rightarrow> ('cout,'qout) cq_operator)
                                    \<Rightarrow> ('cin,'qin) cq_operator \<Rightarrow> ('cout,'qout) cq_operator\<close> is
\<open>\<lambda>(f::'cin \<Rightarrow> ('qin ell2, 'qin ell2) trace_class \<Rightarrow> ('cout \<Rightarrow> ('qout ell2, 'qout ell2) trace_class))
 (cqin::'cin \<Rightarrow> ('qin ell2, 'qin ell2) trace_class) 
 (cout::'cout). (\<Sum>\<^sub>\<infinity>cin::'cin. f cin (cqin cin) cout)\<close>
proof -
  fix f :: \<open>'cin \<Rightarrow> ('qin ell2, 'qin ell2) trace_class \<Rightarrow> ('cout \<Rightarrow> ('qout ell2, 'qout ell2) trace_class)\<close>
  fix cqin :: \<open>'cin \<Rightarrow> ('qin ell2, 'qin ell2) trace_class\<close>
  assume \<open>f cin qin abs_summable_on UNIV\<close> for cin qin
  assume \<open>cqin abs_summable_on UNIV\<close>
  have \<open>(\<lambda>(cout,cin). f cin (cqin cin) cout) abs_summable_on UNIV \<times> UNIV\<close>
    (* by x *)
    
  then show \<open>(\<lambda>cout. \<Sum>\<^sub>\<infinity>cin. f cin (cqin cin) cout) abs_summable_on UNIV\<close>
    unfolding abs_summable_on_Sigma_iff
    apply auto
    
qed *)

(* definition cq_from_distrib :: \<open>'c distr \<Rightarrow> ('q ell2, 'q ell2) trace_class \<Rightarrow> ('c,'q) cq_operator\<close> where
  \<open>cq_from_distrib \<mu> \<rho> = mk_cq_operator (\<lambda>x. prob \<mu> x *\<^sub>R \<rho>)\<close> *)

(* lift_definition cq_from_distrib :: \<open>'c distr \<Rightarrow> ('q ell2, 'q ell2) trace_class \<Rightarrow> ('c,'q) cq_operator\<close> is
  \<open>\<lambda>(\<mu>::'c distr) (\<rho>::('q ell2, 'q ell2) trace_class) x. prob \<mu> x *\<^sub>R \<rho>\<close>
  by (intro Extra_Vector_Spaces.abs_summable_on_scaleR_left prob_abs_summable) *)

(* lift_definition deterministic_cq :: \<open>'c \<Rightarrow> ('q ell2, 'q ell2) trace_class \<Rightarrow> ('c,'q) cq_operator\<close> is
  \<open>\<lambda>(x::'c) (\<rho>::('q ell2, 'q ell2) trace_class) y. of_bool (x=y) *\<^sub>R \<rho>\<close>
proof (rename_tac c \<rho>)
  fix c :: 'c and \<rho> :: \<open>('q ell2, 'q ell2) trace_class\<close>
  show \<open>(\<lambda>x. of_bool (c = x) *\<^sub>R \<rho>) abs_summable_on UNIV\<close>
    apply (rule summable_on_cong_neutral[where T=\<open>{c}\<close>, THEN iffD2])
    by auto
qed *)


(* definition \<open>kraus_map_is_cq E \<longleftrightarrow> kraus_map_apply E = from_cq_operator o to_cq_operator o kraus_map_apply E o from_cq_operator o to_cq_operator\<close> *)
definition \<open>kraus_map_is_cq E \<longleftrightarrow> kraus_map_comp measure_first_kraus_map (kraus_map_comp E measure_first_kraus_map) = E\<close>

(* definition \<open>cq_kraus_map_from_kraus_map_raw E c1 c2 = 
  kraus_map_comp (kraus_map_of_op (tensor_ell2_left (ket c2)* )) (kraus_map_comp E (kraus_map_of_op (tensor_ell2_left (ket c1))))\<close> *)

(* (* TODO wrong definition:
For example, if E is a projective measurement, the sum diverges
 *)
definition valid_cq_kraus_map :: \<open>('cl1 \<Rightarrow> 'cl2 \<Rightarrow> ('qu1 ell2, 'qu2 ell2) kraus_map) \<Rightarrow> bool\<close> where
  \<open>valid_cq_kraus_map E \<longleftrightarrow> (\<forall>c1. (\<lambda>c2. kraus_map_norm (E c1 c2)) summable_on UNIV)\<close> *)

(* lemma valid_cq_kraus_map_0: \<open>valid_cq_kraus_map (\<lambda>_ _. 0)\<close>
  by (simp add: valid_cq_kraus_map_def) *)

lemma kraus_map_comp_0_left[simp]: \<open>kraus_map_comp 0 \<EE> = 0\<close>
  by (auto intro!: kraus_map_apply_inj ext simp: kraus_map_apply_comp)

lemma kraus_map_comp_0_right[simp]: \<open>kraus_map_comp \<EE> 0 = 0\<close>
  by (auto intro!: kraus_map_apply_inj ext simp: kraus_map_apply_comp)

lemma kraus_map_is_cq_0[simp]: \<open>kraus_map_is_cq 0\<close>
  by (simp add: kraus_map_is_cq_def)

(* typedef ('cl1,'qu1,'cl2,'qu2) cq_kraus_map = \<open>Collect kraus_map_is_cq :: (('cl1\<times>'qu1) ell2, ('cl2\<times>'qu2) ell2) kraus_map set\<close>
  apply (rule exI[of _ 0])
  by simp
setup_lifting type_definition_cq_kraus_map

instantiation cq_kraus_map :: (type,type,type,type) zero begin
lift_definition zero_cq_kraus_map :: \<open>('a,'b,'c,'d) cq_kraus_map\<close> is 0
  by simp
instance..
end *)

lemma measure_first_kraus_map_is_cq[simp]: \<open>kraus_map_is_cq measure_first_kraus_map\<close>
  by (simp add: kraus_map_is_cq_def)

(* lift_definition cq_kraus_map_id :: \<open>('cl,'qu,'cl,'qu) cq_kraus_map\<close> is \<open>measure_first_kraus_map\<close>
  by auto *)

(* lift_definition cq_kraus_map_from_kraus_map :: \<open>(('cl1 \<times> 'qu1) ell2, ('cl2 \<times> 'qu2) ell2) kraus_map \<Rightarrow> ('cl1, 'qu1, 'cl2, 'qu2) cq_kraus_map\<close> is
  cq_kraus_map_from_kraus_map_raw
  by auto *)

lemma kraus_map_is_cq_comp: \<open>kraus_map_is_cq E \<Longrightarrow> kraus_map_is_cq F \<Longrightarrow> kraus_map_is_cq (kraus_map_comp E F)\<close>
proof (unfold kraus_map_is_cq_def)
  write kraus_map_comp (infixr "ooo" 80)
  write measure_first_kraus_map ("M")
  assume assms: \<open>M ooo E ooo M = E\<close> \<open>M ooo F ooo M = F\<close>
  have \<open>E ooo F = ((M ooo M) ooo E ooo M) ooo (M ooo F ooo (M ooo M))\<close>
    by (simp add: assms)
  also have \<open>\<dots> = M ooo ((M ooo E ooo M) ooo (M ooo F ooo M)) ooo M\<close>
    by (simp add: kraus_map_comp_assoc del: measure_first_kraus_map_idem)
  also have \<open>\<dots> = M ooo (E ooo F) ooo M\<close>
    by (simp add: assms)
  finally show \<open>M ooo (E ooo F) ooo M = E ooo F\<close>
    by simp
qed


(* lift_definition cq_kraus_map_comp :: \<open>('cl2,'qu2,'cl3,'qu3) cq_kraus_map \<Rightarrow> ('cl1,'qu1,'cl2,'qu2) cq_kraus_map \<Rightarrow> ('cl1,'qu1,'cl3,'qu3) cq_kraus_map\<close> is
  (* \<open>\<lambda>E F c1 c3. (\<Sum>\<^sub>\<infinity>c2::'cl2. kraus_map_comp (E c2 c3) (F c1 c2))\<close> *)
  kraus_map_comp
  by (simp add: kraus_map_is_cq_comp)
(*   apply (auto intro!: simp: valid_cq_kraus_map_def)
  apply (rule abs_summable_summable) *)
 *)

lift_definition cq_operator_cases :: \<open>('cin \<Rightarrow> (('cin\<times>'qin) ell2,('cout\<times>'qout) ell2) kraus_map)
                              \<Rightarrow> (('cin\<times>'qin) ell2, ('cout\<times>'qout) ell2) kraus_map\<close> is
  \<open>\<lambda>\<EE> :: ('cin \<Rightarrow> (('cin\<times>'qin) ell2,('cout\<times>'qout) ell2, unit) kraus_family).
  if (\<exists>B. \<forall>x. kraus_family_norm (\<EE> x) \<le> B) then
        kraus_family_flatten (kraus_family_comp_dependent (\<lambda>(_,_,x,_). \<EE> x)
            (kraus_family_tensor measure_kraus_family (kraus_family_of_op id_cblinfun))) else {}\<close>
proof (intro kraus_equivalent_def[THEN iffD2] conjI; rename_tac \<EE> \<FF>)
  fix \<EE> \<FF> :: \<open>'cin \<Rightarrow> (('cin \<times> 'qin) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('cout \<times> 'qout) ell2 \<times> unit) set\<close>
  assume equiv: \<open>kraus_equivalent (\<EE> x) (\<FF> x)\<close> for x
  show \<open>kraus_family (if \<exists>B. \<forall>x. kraus_family_norm (\<EE> x) \<le> B then
          kraus_family_flatten (kraus_family_comp_dependent \<EE> measure_first_kraus_family) else {})\<close>
    using equiv by (auto intro!: kraus_family_kraus_family_flatten kraus_family_kraus_family_comp_dependent
        kraus_family_measure_first_kraus_family simp: kraus_equivalent_def)
  show \<open>kraus_family (if \<exists>B. \<forall>x. kraus_family_norm (\<FF> x) \<le> B then
          kraus_family_flatten (kraus_family_comp_dependent \<FF> measure_first_kraus_family) else {})\<close>
    using equiv by (auto intro!: kraus_family_kraus_family_flatten kraus_family_kraus_family_comp_dependent
        kraus_family_measure_first_kraus_family simp: kraus_equivalent_def)
  consider (bounded) B where \<open>\<And>x. kraus_family_norm (\<EE> x) \<le> B\<close> \<open>\<And>x. kraus_family_norm (\<FF> x) \<le> B\<close>
         | (unbounded) \<open>\<nexists>B. \<forall>x. kraus_family_norm (\<EE> x) \<le> B\<close> \<open>\<nexists>B. \<forall>x. kraus_family_norm (\<FF> x) \<le> B\<close>
    using kraus_family_norm_welldefined[OF equiv] by auto
  then show \<open>kraus_family_map
            (if \<exists>B. \<forall>x. kraus_family_norm (\<EE> x) \<le> B
             then kraus_family_flatten (kraus_family_comp_dependent \<EE> measure_first_kraus_family) else {}) =
           kraus_family_map
            (if \<exists>B. \<forall>x. kraus_family_norm (\<FF> x) \<le> B
             then kraus_family_flatten (kraus_family_comp_dependent \<FF> measure_first_kraus_family) else {})\<close>
  proof cases
    case bounded
    have [simp]: \<open>kraus_family (\<EE> x)\<close> for x
      using equiv kraus_equivalent_def by blast
    have [simp]: \<open>kraus_family (\<FF> x)\<close> for x
      using equiv kraus_equivalent_def by blast
    have [simp]: \<open>kraus_family (kraus_family_comp_dependent \<EE> measure_first_kraus_family)\<close>
      \<open>kraus_family (kraus_family_comp_dependent \<FF> measure_first_kraus_family)\<close>
      using bounded
      by (auto intro!: kraus_family_kraus_family_comp_dependent simp: kraus_equivalent_def kraus_family_measure_first_kraus_family)
    have \<open>kraus_family_map (kraus_family_comp_dependent \<EE> measure_first_kraus_family)
        = kraus_family_map (kraus_family_comp_dependent \<FF> measure_first_kraus_family)\<close>
      apply (rule ext)
      apply (subst kraus_family_comp_dependent_apply)
         apply (auto intro!: kraus_family_measure_first_kraus_family bounded)[3]
      apply (subst kraus_family_comp_dependent_apply)
         apply (auto intro!: kraus_family_measure_first_kraus_family bounded)
      using equiv by (simp add: kraus_equivalent_def)
    then have \<open>kraus_family_map (kraus_family_flatten (kraus_family_comp_dependent \<EE> measure_first_kraus_family))
        = kraus_family_map (kraus_family_flatten (kraus_family_comp_dependent \<FF> measure_first_kraus_family))\<close>
      by (auto intro!: simp: kraus_family_flatten_same_map)
    with bounded show ?thesis
      by force
  next
    case unbounded
    then show ?thesis 
      by auto
  qed
qed

lift_definition cq_operator_cases :: \<open>('cin \<Rightarrow> ('cin, 'qin, 'cout, 'qout) cq_kraus_map)
                              \<Rightarrow> ('cin, 'qin, 'cout, 'qout) cq_kraus_map\<close> is
  cq_operator_cases0
proof (unfold mem_Collect_eq)
  fix \<EE> :: \<open>'cin \<Rightarrow> (('cin \<times> 'qin) ell2, ('cout \<times> 'qout) ell2) kraus_map\<close>
  assume \<open>kraus_map_is_cq (\<EE> x)\<close> for x
  show \<open>kraus_map_is_cq (cq_operator_cases0 \<EE>)\<close>
  proof (cases \<open>\<exists>B. \<forall>x. kraus_map_norm (\<EE> x) \<le> B\<close>)
    case True
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed

definition cq_map_from_distr0 :: \<open>'c distr \<Rightarrow> (('d\<times>'q) ell2, ('c\<times>'q) ell2, 'd\<times>'c) kraus_family\<close> where
  \<open>cq_map_from_distr0 \<mu> = range (\<lambda>(x,y). (sqrt (prob \<mu> x) *\<^sub>R (butterfly (ket x) (ket y) \<otimes>\<^sub>o id_cblinfun), (y,x)))\<close>

lemma kraus_family_cq_map_from_distr0: \<open>kraus_family (cq_map_from_distr0 \<mu>)\<close>
proof (intro kraus_familyI bdd_aboveI2, rename_tac F)
  fix M :: \<open>(('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'b) ell2 \<times> ('a\<times>'c)) set\<close>
  assume \<open>M \<in> {M. finite M \<and> M \<subseteq> cq_map_from_distr0 \<mu>}\<close>
  then obtain N where \<open>finite N\<close> and M_def: \<open>M = (\<lambda>(x,y). (sqrt (prob \<mu> x) *\<^sub>R (butterfly (ket x) (ket y) \<otimes>\<^sub>o id_cblinfun), (y,x))) ` N\<close>
    apply atomize_elim
    apply (auto intro!: simp: cq_map_from_distr0_def case_prod_unfold )
    by (meson finite_subset_image)
  define N1 N2 where \<open>N1 = fst ` N\<close> and \<open>N2 = snd ` N\<close>
  then have [simp]: \<open>finite N1\<close> \<open>finite N2\<close>
    using \<open>finite N\<close> by auto
  have \<open>(\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) = (\<Sum>(x,y)\<in>N. prob \<mu> x *\<^sub>R ((butterfly (ket x) (ket y) \<otimes>\<^sub>o id_cblinfun)* o\<^sub>C\<^sub>L (butterfly (ket x) (ket y) \<otimes>\<^sub>o id_cblinfun)))\<close>
    unfolding M_def
    apply (subst sum.reindex)
    by (auto intro!: inj_onI simp: case_prod_beta scaleR_adj)
  also have \<open>\<dots> = (\<Sum>(x,y)\<in>N. prob \<mu> x *\<^sub>R (butterfly (ket y) (ket y) \<otimes>\<^sub>o id_cblinfun))\<close>
    by (simp add: tensor_op_adjoint comp_tensor_op)
  also have \<open>\<dots> \<le> (\<Sum>(x,y)\<in>N1\<times>N2. prob \<mu> x *\<^sub>R (butterfly (ket y) (ket y) \<otimes>\<^sub>o id_cblinfun))\<close>
    apply (rule sum_mono2)
    using \<open>finite N\<close>  
      apply (auto intro!: scaleR_nonneg_nonneg tensor_op_pos simp add: N1_def N2_def)
    by force+
  also have \<open>\<dots> = (\<Sum>x\<in>N1. \<Sum>y\<in>N2. prob \<mu> x *\<^sub>R (butterfly (ket y) (ket y) \<otimes>\<^sub>o id_cblinfun))\<close>
    by (smt (verit) N1_def N2_def \<open>finite N\<close> finite_imageI sum.Sigma sum.cong)
  also have \<open>\<dots> = (\<Sum>x\<in>N1. prob \<mu> x *\<^sub>R (\<Sum>y\<in>N2. butterfly (ket y) (ket y) \<otimes>\<^sub>o id_cblinfun))\<close>
    by (metis (mono_tags, lifting) scaleR_right.sum sum.cong)
  also have \<open>\<dots> \<le> (\<Sum>x\<in>N1. prob \<mu> x *\<^sub>R id_cblinfun)\<close>
    by (auto intro!: sum_mono scaleR_left_mono is_Proj_leq_id is_Proj_tensor_op is_Proj_butterfly_ket
          simp: simp flip: tensor_op_cbilinear.sum_left simp:)
  also have \<open>\<dots> = (\<Sum>x\<in>N1. prob \<mu> x) *\<^sub>R id_cblinfun\<close>
    by (metis scaleR_left.sum)
  also have \<open>\<dots> \<le> weight \<mu> *\<^sub>R id_cblinfun\<close>
    by (auto intro!: scaleR_right_mono Prob_mono simp: simp flip: infsum_finite Prob.rep_eq)
  finally show \<open>(\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> weight \<mu> *\<^sub>R id_cblinfun\<close>
    by -
qed

lift_definition cq_map_from_distr1 :: \<open>'c distr \<Rightarrow> (('d\<times>'q) ell2, ('c\<times>'q) ell2) kraus_map\<close> is
  \<open>\<lambda>\<mu>. kraus_family_flatten (cq_map_from_distr0 \<mu>)\<close>
  by (simp add: kraus_equivalent_reflI kraus_family_cq_map_from_distr0 kraus_family_kraus_family_flatten)
(* 
  (* \<open>\<lambda>\<mu> :: 'c distr. kraus_family_flatten (range (\<lambda>y. (butterfly (Abs_ell2 (\<lambda>x. sqrt (prob \<mu> x))) (ket y) \<otimes>\<^sub>o id_cblinfun, y)))\<close> *)
proof (rule kraus_equivalent_reflI)
  fix \<mu> :: \<open>'c distr\<close>
  define \<psi> and B :: \<open>('d \<times> 'q) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('d \<times> 'q) ell2\<close>
    where \<open>\<psi> = Abs_ell2 (\<lambda>x. complex_of_real (sqrt (prob \<mu> x)))\<close>
      and \<open>B = (\<psi> \<bullet>\<^sub>C \<psi>) *\<^sub>C id_cblinfun\<close>
  have *: \<open>(\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) < B\<close> if \<open>finite M\<close>
    and \<open>M \<subseteq> range (\<lambda>y. (butterfly \<psi> (ket y) \<otimes>\<^sub>o
                      id_cblinfun, y))\<close>
  for M :: \<open>(('d \<times> 'q) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'q) ell2 \<times> 'd) set\<close>
  proof -
    from that obtain N where \<open>finite N\<close> and
      M_def: \<open>M = (\<lambda>y. (butterfly \<psi> (ket y)
               \<otimes>\<^sub>o id_cblinfun, y)) ` N\<close>
      by -
    have [simp]: \<open>is_Proj (\<Sum>x\<in>N. selfbutter (ket x))\<close>
      apply (subst sum.reindex[of ket N, unfolded o_def, symmetric])
      by (auto intro!: sum_butterfly_is_Proj simp add: inj_on_def)
    have \<open>(\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) = (\<Sum>x\<in>N.
       (butterfly \<psi> (ket x) \<otimes>\<^sub>o id_cblinfun)* o\<^sub>C\<^sub>L butterfly \<psi> (ket x) \<otimes>\<^sub>o id_cblinfun)\<close>
      by (simp add: inj_on_def sum.reindex M_def)
    also have \<open>\<dots> = (\<psi> \<bullet>\<^sub>C \<psi>) *\<^sub>C (\<Sum>x\<in>N. selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun)\<close>
      by (simp add: tensor_op_adjoint comp_tensor_op tensor_op_scaleC_left flip: scaleC_sum_right)
    also have \<open>\<dots> \<le> B\<close>
      by (auto intro!: scaleC_left_mono is_Proj_leq_id is_Proj_tensor_op
          simp: B_def simp flip: tensor_op_cbilinear.sum_left)
    finally show ?thesis
      by -
  qed
  show \<open>kraus_family (kraus_family_flatten (range (\<lambda>y. (butterfly \<psi> (ket y)
           \<otimes>\<^sub>o id_cblinfun, y)) :: (('d \<times> 'q) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'q) ell2 \<times> 'd) set))\<close>
    using *  
    apply (intro kraus_family_kraus_family_flatten kraus_familyI bdd_aboveI2[where M=B])
    by fastforce
qed
 *)

(* lemma rank1_comp_right: \<open>rank1 (a o\<^sub>C\<^sub>L b)\<close> if \<open>rank1 b\<close>
  by (metis Compact_Operators.rank1_def cblinfun_comp_butterfly that)
lemma rank1_comp_left: \<open>rank1 (a o\<^sub>C\<^sub>L b)\<close> if \<open>rank1 a\<close>
  by (metis Compact_Operators.rank1_def butterfly_comp_cblinfun that) *)

(* lemma hilbert_schmidt_minus: \<open>hilbert_schmidt (a - b)\<close> if \<open>hilbert_schmidt a\<close> and \<open>hilbert_schmidt b\<close>
  for a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  using hilbert_schmidt_plus hilbert_schmidt_uminus that by fastforce *)

(* lemma (* NOT TRUE *)
  assumes \<open>trace_class x\<close>
  assumes \<open>S \<subseteq> Collect trace_class\<close>
  shows \<open>continuous (at x within S) Abs_trace_class\<close>
proof (intro continuous_within_eps_delta[THEN iffD2] allI ballI impI exI conjI)
  fix e :: real
  assume \<open>e > 0\<close>
  then show \<open>e > 0\<close>
    by -
  fix y
  assume \<open>y \<in> S\<close>
  then have \<open>trace_class y\<close>
try0
sledgehammer [dont_slice]
  using assms(2) by blast
by -
  assume \<open>dist y x < e\<close>
 *)

(* (* TODO move *)
lemma finite_rank_dense_trace_class:
  fixes A :: \<open>'a::chilbert_space set\<close> and B :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_onb A\<close> \<open>is_onb B\<close>
  shows \<open>closure (cspan ((\<lambda>(\<xi>,\<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))) = UNIV\<close>
proof -
  have \<open>x \<in> closure (cspan ((\<lambda>(\<xi>,\<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B)))\<close> for x
  proof (rule closure_sequential[THEN iffD2])
    have \<open>compact_op (from_trace_class x)\<close>
      by (simp add: trace_class_compact)
    with assms have \<open>from_trace_class x \<in> closure (cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B)))\<close>
      apply (subst finite_rank_dense_compact)
      by simp_all
    then obtain f where f_range: \<open>f n \<in> cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B))\<close> 
      and f_lim: \<open>f \<longlonglongrightarrow> from_trace_class x\<close> for n
      using closure_sequential by blast
    define f' where \<open>f' n = Abs_trace_class (f n)\<close> for n
    have [simp]: \<open>trace_class (f n)\<close> for n
    proof -
      note f_range[of n]
      also have \<open>cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B)) \<subseteq> cspan (Collect trace_class)\<close>
        by (auto intro!: complex_vector.span_mono simp: )
      also have \<open>\<dots> = Collect trace_class\<close>
        by (simp add: cspan_trace_class)
      finally show ?thesis
        by simp
    qed
    have f_f': \<open>f n = from_trace_class (f' n)\<close> for n
      by (simp add: f'_def Abs_trace_class_inverse)
    have f'_range: \<open>f' n \<in> cspan ((\<lambda>(\<xi>,\<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))\<close> for n
    proof -
      have \<open>from_trace_class (f' n) \<in> from_trace_class ` cspan ((\<lambda>(\<xi>,\<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))\<close> for n
        using f_range
        by (simp add: image_image case_prod_unfold tc_butterfly.rep_eq 
            flip: f_f' complex_vector.linear_span_image)
      then show ?thesis
        by (metis (no_types, lifting) from_trace_class_inverse image_iff)
    qed
    thm from_trace_class_inject
    have f'_limit: \<open>f' \<longlonglongrightarrow> x\<close>
      unfolding f'_def
      apply (subst from_trace_class_inverse[symmetric, of x])
      apply (rule continuous_within_tendsto_compose'[where f=Abs_trace_class and S=\<open>Collect trace_class\<close>])
        apply (auto intro!: f_lim simp: )
(* NOT TRUE! *)
      by -
    from f'_range f'_limit
    show \<open>\<exists>f'. (\<forall>n. f' n \<in> cspan ((\<lambda>(\<xi>, \<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))) \<and> f' \<longlonglongrightarrow> x\<close>
      by auto
  qed
  then show ?thesis
    by auto
qed *)

lemma cq_map_from_distr0_apply:
  fixes \<mu> :: \<open>'c distr\<close> and \<rho> :: \<open>(('d\<times>'q) ell2, ('d\<times>'q) ell2) trace_class\<close>
  shows \<open>kraus_family_map (cq_map_from_distr0 \<mu>) \<rho>
          = tc_tensor (diagonal_operator_tc (prob \<mu>)) (partial_trace (sandwich_tc swap_ell2 \<rho>))\<close>
proof (rule from_trace_class_inject[THEN iffD1], rule equal_ket, rule cinner_ket_eqI, rename_tac x y)
  fix x y :: \<open>'c \<times> 'q\<close>
  obtain x1 x2 y1 y2 where x: \<open>x = (x1,x2)\<close> and y: \<open>y = (y1,y2)\<close>
    by fastforce
  have [simp]: \<open>prob \<mu> summable_on UNIV\<close>
    by (simp add: prob_summable)
  then have [simp]: \<open>bdd_above (range (\<lambda>x. prob \<mu> x))\<close>
    by (rule summable_on_bdd_above_real)

  from kraus_family_map_summable[OF kraus_family_cq_map_from_distr0, of \<rho> \<mu>]
  have sum1: \<open>(\<lambda>(w,z). sandwich_tc (sqrt (prob \<mu> w) *\<^sub>R 
          (butterfly (ket w) (ket z) \<otimes>\<^sub>o id_cblinfun)) \<rho>) summable_on UNIV\<close>
    by (auto intro!: simp: cq_map_from_distr0_def case_prod_unfold
        kraus_family_map_def summable_on_reindex inj_def o_def)

  have \<open>ket y \<bullet>\<^sub>C (from_trace_class (kraus_family_map (cq_map_from_distr0 \<mu>) \<rho>) *\<^sub>V ket x)
    = ket (y1, y2) \<bullet>\<^sub>C (from_trace_class
     (\<Sum>\<^sub>\<infinity>(w,z). sandwich_tc (sqrt (prob \<mu> w) *\<^sub>R (butterfly (ket w) (ket z) \<otimes>\<^sub>o id_cblinfun)) \<rho>) *\<^sub>V ket (x1, x2))\<close>
    by (simp add: x y kraus_family_map_def cq_map_from_distr0_def infsum_reindex inj_def o_def
        case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(w,z). ket (y1, y2) \<bullet>\<^sub>C ((sandwich (sqrt (prob \<mu> w) *\<^sub>R
            (butterfly (ket w) (ket z) \<otimes>\<^sub>o id_cblinfun)) *\<^sub>V
              from_trace_class \<rho>) *\<^sub>V ket (x1, x2)))\<close>
    apply (subst infsum_bounded_linear[where f=\<open>\<lambda>a. ket (y1, y2) \<bullet>\<^sub>C (from_trace_class a *\<^sub>V ket (x1, x2))\<close>, symmetric])
    using sum1 by (auto intro!: bounded_clinear.bounded_linear bounded_linear_intros
        simp: o_def case_prod_unfold from_trace_class_sandwich_tc)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(w, z).
       prob \<mu> w *
       ((of_bool (w = y1) *\<^sub>C ket z \<otimes>\<^sub>s ket y2) \<bullet>\<^sub>C
        (from_trace_class \<rho> *\<^sub>V of_bool (w = x1) *\<^sub>C ket z \<otimes>\<^sub>s ket x2)))\<close>
    apply (simp add: sandwich_apply cblinfun.scaleR_left tensor_op_adjoint tensor_op_ell2
        flip: tensor_ell2_ket)
    by (simp add: tensor_op_adjoint tensor_op_ell2  cinner_ket flip: cinner_adj_left)
  also have \<open>\<dots> = of_bool (x1=y1) *\<^sub>C (\<Sum>\<^sub>\<infinity>(w, z)\<in>{x1}\<times>UNIV.
       prob \<mu> x1 * ((ket z \<otimes>\<^sub>s ket y2) \<bullet>\<^sub>C (from_trace_class \<rho> *\<^sub>V ket z \<otimes>\<^sub>s ket x2)))\<close>
    apply (auto intro!: infsum_cong_neutral infsum_0)
    using complex_vector.scale_eq_0_iff by fastforce
  also have \<open>\<dots> = of_bool (x1=y1) *\<^sub>C (\<Sum>\<^sub>\<infinity>z.
       prob \<mu> x1 * ((ket z \<otimes>\<^sub>s ket y2) \<bullet>\<^sub>C (from_trace_class \<rho> *\<^sub>V ket z \<otimes>\<^sub>s ket x2)))\<close>
    apply (rewrite at \<open>{x1}\<times>UNIV\<close> to \<open>range (\<lambda>z. (x1,z))\<close> DEADID.rel_mono_strong)
    by (auto intro!: simp: infsum_reindex inj_def o_def)
  also have \<open>\<dots> = prob \<mu> x1 * of_bool (x1=y1) *\<^sub>C (\<Sum>\<^sub>\<infinity>z.
       ((ket z \<otimes>\<^sub>s ket y2) \<bullet>\<^sub>C (from_trace_class \<rho> *\<^sub>V ket z \<otimes>\<^sub>s ket x2)))\<close>
    by (simp add: infsum_cmult_right')
  also have \<open>\<dots> = prob \<mu> x1 * of_bool (x1=y1) *\<^sub>C 
      (\<Sum>\<^sub>\<infinity>z. ((ket y2 \<otimes>\<^sub>s ket z) \<bullet>\<^sub>C (from_trace_class (sandwich_tc swap_ell2 \<rho>) *\<^sub>V (ket x2 \<otimes>\<^sub>s ket z))))\<close>
    apply (rule arg_cong[where f=\<open>%x. _ * _ *\<^sub>C x\<close>])
    apply (rule infsum_cong)
    by (simp add: from_trace_class_sandwich_tc sandwich_apply flip: cinner_adj_left)
  also have \<open>\<dots> = prob \<mu> x1 * of_bool (y1 = x1) *
    (ket y2 \<bullet>\<^sub>C (from_trace_class (partial_trace (sandwich_tc swap_ell2 \<rho>)) *\<^sub>V ket x2))\<close>
    by (simp add: vector_sandwich_partial_trace)
  also have \<open>\<dots> = ket y \<bullet>\<^sub>C (from_trace_class
             (tc_tensor (diagonal_operator_tc (\<lambda>x. complex_of_real (prob \<mu> x)))
               (partial_trace (sandwich_tc swap_ell2 \<rho>))) *\<^sub>V ket x)\<close>
    by (simp add: x y tc_tensor.rep_eq tensor_op_ell2 diagonal_operator_tc.rep_eq diagonal_operator_ket
        flip: tensor_ell2_ket)
  finally show \<open>ket y \<bullet>\<^sub>C (from_trace_class (kraus_family_map (cq_map_from_distr0 \<mu>) \<rho>) *\<^sub>V ket x) =
           ket y \<bullet>\<^sub>C
           (from_trace_class
             (tc_tensor (diagonal_operator_tc (\<lambda>x. complex_of_real (prob \<mu> x)))
               (partial_trace (sandwich_tc swap_ell2 \<rho>))) *\<^sub>V
            ket x)\<close>
    by -
qed

lemma cq_map_from_distr1_apply:
  fixes \<mu> :: \<open>'c distr\<close> and \<rho> :: \<open>(('d\<times>'q) ell2, ('d\<times>'q) ell2) trace_class\<close>
  (* defines \<open>\<psi> \<equiv> Abs_ell2 (\<lambda>x. sqrt (prob \<mu> x))\<close> *)
  shows \<open>kraus_map_apply (cq_map_from_distr1 \<mu>) \<rho> = tc_tensor (diagonal_operator_tc (\<lambda>x. complex_of_real (prob \<mu> x)))
            (partial_trace (sandwich_tc swap_ell2 \<rho>))\<close>
  apply (transfer' fixing: \<mu> \<rho>)
  by (simp add: cq_map_from_distr0_apply kraus_family_flatten_same_map kraus_family_cq_map_from_distr0)

(* (* TODO move *)
lemma kraus_equivalent_flatten_left[simp]: 
  assumes \<open>kraus_family F\<close>
  shows \<open>kraus_equivalent (kraus_family_flatten F) G \<longleftrightarrow> kraus_equivalent F G\<close>
  by (simp add: assms kraus_equivalent_def kraus_family_flatten_same_map kraus_family_kraus_family_flatten)
(* TODO move *)
lemma kraus_equivalent_flatten_right[simp]: 
  assumes \<open>kraus_family G\<close>
  shows \<open>kraus_equivalent F (kraus_family_flatten G) \<longleftrightarrow> kraus_equivalent F G\<close>
  by (simp add: assms kraus_equivalent_def kraus_family_flatten_same_map kraus_family_kraus_family_flatten) *)


(* TODO: put near *) thm infsum_scaleC_right
lemma has_sum_scaleC_right:
  fixes f :: \<open>'a \<Rightarrow> 'b :: complex_normed_vector\<close>
  assumes \<open>(f has_sum x) A\<close>
  shows   \<open>((\<lambda>x. c *\<^sub>C f x) has_sum c *\<^sub>C x) A\<close>
  by -
  

(* TODO move *)
lemma partial_trace_scaleC: \<open>partial_trace (c *\<^sub>C t) = c *\<^sub>C partial_trace t\<close>
proof -
  from partial_trace_has_sum[of t]
  have \<open>((\<lambda>j. c *\<^sub>C compose_tcl (compose_tcr (tensor_ell2_right (ket j)*) t) (tensor_ell2_right (ket j))) has_sum
           c *\<^sub>C partial_trace t) UNIV\<close> (is \<open>(?f has_sum _) _\<close>)
    by (rule has_sum_scaleC_right)
  moreover have \<open>?f j = compose_tcl (compose_tcr (tensor_ell2_right (ket j)*) (c *\<^sub>C t)) (tensor_ell2_right (ket j))\<close> (is \<open>?f j = ?g j\<close>) for j
    by (simp add: compose_tcl.scaleC_left compose_tcr.scaleC_right)
  ultimately have \<open>(?g has_sum c *\<^sub>C partial_trace t) UNIV\<close>
    by simp
  moreover have \<open>(?g has_sum partial_trace (c *\<^sub>C t)) UNIV\<close>
    by (simp add: partial_trace_has_sum)
  ultimately show ?thesis
    using has_sum_unique by blast
qed


(* lemma bounded_clinear_partial_trace[bounded_clinear]: \<open>bounded_clinear partial_trace\<close>
  apply (rule bounded_clinearI[where K=1])
  by (simp_all add: partial_trace_plus partial_trace_scaleC partial_trace_norm_reducing) *)

(* TODO move *)
(* lemma partial_trace_of_sandwich_sum:
  \<open>(\<Sum>\<^sub>\<infinity>x. partial_trace (sandwich_tc (id_cblinfun \<otimes>\<^sub>o selfbutter (ket x)) t)) = partial_trace t\<close>
  by - *)

lemma kraus_map_is_cq_cq_map_from_distr1:
  \<open>kraus_map_is_cq (cq_map_from_distr1 \<mu> :: (('b \<times> 'c) ell2, ('a \<times> 'c) ell2) kraus_map)\<close>
  for \<mu> :: \<open>'a distr\<close>
  apply (auto intro!: kraus_map_is_cq_def[THEN iffD2] kraus_map_apply_inj
      cblinfun_eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor]
      simp: measure_first_kraus_map_def kraus_map_apply_comp kraus_map_tensor
)
  by x
(* proof -
(* TODO: Probably easier now because we can just evaluate the map on tensors. Rewrite proof? *)
  write kraus_equivalent (infix "~" 55)
  note kraus_family_cq_map_from_distr0[iff]
    kraus_family_kraus_family_flatten[iff]
    kraus_family_flatten_same_map[simp]

  have \<open>kraus_map_comp (cq_map_from_distr1 \<mu>) measure_first_kraus_map = cq_map_from_distr1 \<mu>\<close>
  proof (transfer fixing: \<mu>)
    show \<open>kraus_family_flatten (kraus_family_comp (kraus_family_flatten (cq_map_from_distr0 \<mu>)) (kraus_family_flatten measure_first_kraus_family))
        ~ kraus_family_flatten (cq_map_from_distr0 \<mu>)\<close> (is \<open>?lhs ~ ?rhs\<close>)
    proof -
      have \<open>?lhs ~ kraus_family_comp (kraus_family_flatten (cq_map_from_distr0 \<mu>)) (kraus_family_flatten measure_first_kraus_family)\<close> (is \<open>?lhs ~ _\<close>)
        apply (rule kraus_equivalent_kraus_family_flatten_left)
        by (auto intro!: kraus_family_kraus_family_comp simp: )
      also have \<open>\<dots> ~ kraus_family_comp (cq_map_from_distr0 \<mu>) measure_first_kraus_family\<close>
        apply (rule kraus_family_comp_cong)
        by (auto intro!: kraus_equivalent_kraus_family_flatten_left kraus_equivalent_reflI simp: )
      also have \<open>\<dots> ~ cq_map_from_distr0 \<mu>\<close>
      proof (intro kraus_equivalent_def[THEN iffD2] conjI ext)
        show \<open>kraus_family (cq_map_from_distr0 \<mu>)\<close>
          by fast
        show \<open>kraus_family (kraus_family_comp (cq_map_from_distr0 \<mu>) measure_first_kraus_family)\<close>
          by fast
        fix \<rho> :: \<open>(('f \<times> 'g) ell2, ('f \<times> 'g) ell2) trace_class\<close>
        show \<open>kraus_family_map (kraus_family_comp (cq_map_from_distr0 \<mu>) measure_first_kraus_family) \<rho> =
              kraus_family_map (cq_map_from_distr0 \<mu>) \<rho>\<close> (is \<open>?lhs = _\<close>)
        proof -
          define \<rho>' where \<open>\<rho>' = sandwich_tc swap_ell2 \<rho>\<close>
          have *: \<open>sandwich_tc swap_ell2 (sandwich_tc (U \<otimes>\<^sub>o id_cblinfun) \<rho>)
                = sandwich_tc (id_cblinfun \<otimes>\<^sub>o U) \<rho>'\<close> for U :: \<open>'f ell2 \<Rightarrow>\<^sub>C\<^sub>L 'y ell2\<close>
            by (metis (no_types, lifting) \<rho>'_def cblinfun_apply_cblinfun_compose sandwich_tc_compose swap_ell2_commute_tensor_op) x

          have \<open>?lhs = kraus_family_map (cq_map_from_distr0 \<mu>) (kraus_family_map measure_first_kraus_family \<rho>)\<close>
            by (simp add: kraus_family_comp_apply)
          also have \<open>\<dots> = tc_tensor (diagonal_operator_tc (prob \<mu>))
               (partial_trace (sandwich_tc swap_ell2 (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) \<rho>)))\<close>
            by (simp add: cq_map_from_distr0_apply measure_first_kraus_family_apply)
          also have \<open>\<dots> = tc_tensor (diagonal_operator_tc (prob \<mu>))
               (\<Sum>\<^sub>\<infinity>x. partial_trace (sandwich_tc swap_ell2 (sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) \<rho>)))\<close>
            apply (subst infsum_bounded_linear[where f=\<open>\<lambda>x. partial_trace (sandwich_tc swap_ell2 x)\<close>, symmetric, unfolded o_def])
            by (intro bounded_clinear.bounded_linear bounded_linear_intros
                measure_first_kraus_family_apply_summable refl)+
          also have \<open>\<dots> = tc_tensor (diagonal_operator_tc (prob \<mu>))
               (\<Sum>\<^sub>\<infinity>x. partial_trace (sandwich_tc (id_cblinfun \<otimes>\<^sub>o selfbutter (ket x)) \<rho>'))\<close>
            by (simp add: * )
          also have \<open>\<dots> = tc_tensor (diagonal_operator_tc (prob \<mu>)) (partial_trace \<rho>')\<close>
            by (simp add: partial_trace_of_sandwich_sum)
          also have \<open>\<dots> = kraus_family_map (cq_map_from_distr0 \<mu>) \<rho>\<close>
            by (simp add: cq_map_from_distr0_apply \<rho>'_def)
          finally show ?thesis
            by -
        qed
      qed
      also have \<open>\<dots> ~ ?rhs\<close>
        by (simp add: kraus_equivalent_kraus_family_flatten_right)
      finally show ?thesis
        by -
    qed
  qed

  moreover have \<open>kraus_map_comp measure_first_kraus_map (cq_map_from_distr1 \<mu>) = cq_map_from_distr1 \<mu>\<close> (is \<open>?lhs = _\<close>)
  proof (transfer fixing: \<mu>)
    show \<open>kraus_family_flatten (kraus_family_comp (kraus_family_flatten measure_first_kraus_family) (kraus_family_flatten (cq_map_from_distr0 \<mu>))) ~
          kraus_family_flatten (cq_map_from_distr0 \<mu>)\<close> (is \<open>?lhs ~ ?rhs\<close>)
    proof -
      have \<open>?lhs ~ kraus_family_comp (kraus_family_flatten measure_first_kraus_family) (kraus_family_flatten (cq_map_from_distr0 \<mu>))\<close>
        apply (rule kraus_equivalent_kraus_family_flatten_left)
        by auto
      also have \<open>\<dots> ~ kraus_family_comp measure_first_kraus_family (cq_map_from_distr0 \<mu>)\<close>
        apply (rule kraus_family_comp_cong)
        by (simp_all add: kraus_equivalent_kraus_family_flatten_left)
      also have \<open>\<dots> ~ cq_map_from_distr0 \<mu>\<close>
      proof (intro kraus_equivalent_def[THEN iffD2] conjI ext)
        show \<open>kraus_family (kraus_family_comp measure_first_kraus_family (cq_map_from_distr0 \<mu>))\<close>
          by (simp add: kraus_family_kraus_family_comp)
        show \<open>kraus_family (cq_map_from_distr0 \<mu>)\<close>
          by simp
        fix \<rho> :: \<open>(('h \<times> 'i) ell2, ('h \<times> 'i) ell2) trace_class\<close>
        define \<rho>' where \<open>\<rho>' = partial_trace (sandwich_tc swap_ell2 \<rho>)\<close>
        have \<open>kraus_family_map (kraus_family_comp measure_first_kraus_family (cq_map_from_distr0 \<mu>)) \<rho>
              = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun)
                     (tc_tensor (diagonal_operator_tc (\<lambda>x. complex_of_real (prob \<mu> x))) \<rho>'))\<close>
          by (simp add: kraus_family_comp_apply cq_map_from_distr0_apply measure_first_kraus_family_apply \<rho>'_def)
        also have \<open>\<dots> = tc_tensor (diagonal_operator_tc (\<lambda>x. complex_of_real (prob \<mu> x))) \<rho>'\<close>
          by -
        also have \<open>\<dots> = kraus_family_map (cq_map_from_distr0 \<mu>) \<rho>\<close>
          by (simp add: cq_map_from_distr0_apply \<rho>'_def)
        finally show \<open>kraus_family_map (kraus_family_comp measure_first_kraus_family (cq_map_from_distr0 \<mu>)) \<rho>
            = kraus_family_map (cq_map_from_distr0 \<mu>) \<rho>\<close>
          by -
      qed
      also have \<open>\<dots> ~ ?rhs\<close>
        by (simp add: kraus_equivalent_kraus_family_flatten_right)
      finally show ?thesis
        by -
    qed
  qed

  ultimately show ?thesis
    by (smt (verit, del_insts) kraus_map_is_cq_def)
qed
 *)



lift_definition cq_map_from_distr :: \<open>'c distr \<Rightarrow> ('d, 'q, 'c, 'q) cq_kraus_map\<close> is cq_map_from_distr1
  apply (transfer' fixing: )
  by (simp add: kraus_map_is_cq_cq_map_from_distr1)


definition deterministic_cq :: \<open>'c \<Rightarrow> ('q ell2, 'q ell2) trace_class \<Rightarrow> ('c,'q) cq_operator\<close> where
  \<open>deterministic_cq c \<rho> = mk_cq_operator (\<lambda>d. of_bool (c=d) *\<^sub>R \<rho>)\<close>

lemma cq_from_distrib_point_distr: \<open>cq_map_apply (cq_map_from_distr (point_distr x)) \<rho> = deterministic_cq x \<rho>\<close>
  apply (simp add: cq_from_distrib_def deterministic_cq_def)
  by (metis (mono_tags, opaque_lifting) of_bool_eq_0_iff)
(*   
  apply (rule cq_operator_at_inject[THEN iffD1])
  by (auto simp add: cq_from_distrib.rep_eq deterministic_cq.rep_eq) *)

(* definition kraus_family_from_cq_kraus_map :: \<open>('cl1 \<Rightarrow> 'cl2 \<Rightarrow> ('qu1 ell2, 'qu2 ell2) kraus_family) \<Rightarrow> 
  (('cl1\<times>'qu1) ell2, ('cl2\<times>'qu2)) kraus_family\<close> where
\<open>xxx\<close> *)



end
