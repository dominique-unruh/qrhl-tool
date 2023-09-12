theory CQ_Operators
  imports Tensor_Product.Trace_Class Registers2.Missing_Bounded_Operators Discrete_Distributions Kraus_Maps
    Tensor_Product.Partial_Trace
begin



(* lemma choice4':
  assumes \<open>\<forall>x. \<exists>a b c d. P x a b c d\<close>
  shows \<open>\<exists>a b c d. \<forall>x. P x (a x) (b x) (c x) (d x)\<close>
proof -
  from assms have \<open>\<forall>x. \<exists>abcd. P x ((\<lambda>(a,b,c,d). a) abcd) ((\<lambda>(a,b,c,d). b) abcd)
                                  ((\<lambda>(a,b,c,d). c) abcd) ((\<lambda>(a,b,c,d). d) abcd)\<close>
    by auto
  then have \<open>\<exists>abcd. \<forall>x. P x ((\<lambda>(a,b,c,d). a) (abcd x)) ((\<lambda>(a,b,c,d). b) (abcd x)) ((\<lambda>(a,b,c,d). c) (abcd x)) ((\<lambda>(a,b,c,d). d) (abcd x))\<close>
    by (rule choice)
  then show ?thesis
    by fast
qed *)



(* TODO move *)
lemma infsum_of_bool_scaleC: \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. of_bool (x=y) *\<^sub>C f x) = of_bool (y\<in>X) *\<^sub>C f y\<close> for f :: \<open>_ \<Rightarrow> _::complex_vector\<close>
  apply (cases \<open>y\<in>X\<close>)
   apply (subst infsum_cong_neutral[where T=\<open>{y}\<close> and g=f])
      apply auto[4]
  apply (subst infsum_cong_neutral[where T=\<open>{}\<close> and g=f])
  by auto

(* TODO move *)
lemma of_nat_indicator: \<open>of_nat (indicator E x) = indicator E x\<close>
  by (metis indicator_eq_0_iff indicator_eq_1_iff of_nat_1 semiring_1_class.of_nat_simps(1))

(* TODO move *)
lemma inj_selfbutter_ket:
  assumes "selfbutter (ket x) = selfbutter (ket y)"
  shows "x = y"
proof -
  have \<open>1 = norm (selfbutter (ket x) *\<^sub>V ket x)\<close>
    by auto
  also have \<open>\<dots> = norm (selfbutter (ket y) *\<^sub>V ket x)\<close>
    using assms by simp
  also have \<open>\<dots> = of_bool (x=y)\<close>
    by (simp add: cinner_ket)
  finally show ?thesis
    by simp
qed

(* TODO: generalize original is_ortho_set_ket to this *) thm is_ortho_set_ket 
lemma is_ortho_set_ket[simp]: \<open>is_ortho_set (ket ` A)\<close>
  using is_ortho_set_def by fastforce

lemma is_Proj_butterfly_ket: \<open>is_Proj (\<Sum>x\<in>M. selfbutter (ket x))\<close>
  apply (subst sum.reindex[symmetric, unfolded o_def, of ket])
  by (auto intro!: inj_onI sum_butterfly_is_Proj simp: )

(* TODO move *)
lemma infsum_cblinfun_compose_left:
  assumes \<open>b summable_on X\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. a o\<^sub>C\<^sub>L b x) = a o\<^sub>C\<^sub>L (\<Sum>\<^sub>\<infinity>x\<in>X. b x)\<close>
  apply (subst infsum_bounded_linear[symmetric, where g=b and S=X and f=\<open>\<lambda>b. a o\<^sub>C\<^sub>L b\<close>])
  by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_right simp add: assms o_def)
lemma infsum_cblinfun_compose_right:
  assumes \<open>a summable_on X\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. a x o\<^sub>C\<^sub>L b) = (\<Sum>\<^sub>\<infinity>x\<in>X. a x) o\<^sub>C\<^sub>L b\<close>
  apply (subst infsum_bounded_linear[symmetric, where g=a and S=X and f=\<open>\<lambda>a. a o\<^sub>C\<^sub>L b\<close>])
  by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left simp add: assms o_def)

(* TODO move *)
lemma summable_cblinfun_compose_left:
  assumes \<open>b summable_on X\<close>
  shows \<open>(\<lambda>x. a o\<^sub>C\<^sub>L b x) summable_on X\<close>
  apply (rule Infinite_Sum.summable_on_bounded_linear[where h=\<open>\<lambda>b. a o\<^sub>C\<^sub>L b\<close>])
  by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_right simp add: assms o_def)
lemma summable_cblinfun_compose_right:
  assumes \<open>a summable_on X\<close>
  shows \<open>(\<lambda>x. a x o\<^sub>C\<^sub>L b) summable_on X\<close>
  apply (rule Infinite_Sum.summable_on_bounded_linear[where h=\<open>\<lambda>a. a o\<^sub>C\<^sub>L b\<close>])
  by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left simp add: assms o_def)


(* TODO move *)
lemma from_trace_class_abs_summable: \<open>f abs_summable_on X \<Longrightarrow> (\<lambda>x. from_trace_class (f x)) abs_summable_on X\<close>
    apply (rule abs_summable_on_comparison_test[where g=\<open>f\<close>])
    by (simp_all add: Unsorted_HSTP.norm_leq_trace_norm norm_trace_class.rep_eq)

(* TODO move *)
lemma from_trace_class_summable: \<open>f summable_on X \<Longrightarrow> (\<lambda>x. from_trace_class (f x)) summable_on X\<close>
  apply (rule Infinite_Sum.summable_on_bounded_linear[where h=from_trace_class])
  by (simp_all add: bounded_clinear.bounded_linear bounded_clinear_from_trace_class)

(* TODO move *)
lemma from_trace_class_infsum: 
  assumes \<open>f summable_on UNIV\<close>
  shows \<open>from_trace_class (\<Sum>\<^sub>\<infinity>x. f x) = (\<Sum>\<^sub>\<infinity>x. from_trace_class (f x))\<close>
  apply (rule infsum_bounded_linear_strong[symmetric])
  using assms
  by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_from_trace_class from_trace_class_summable)


(* TODO move *)
lemma is_Proj_leq_id: \<open>is_Proj P \<Longrightarrow> P \<le> id_cblinfun\<close>
  by (metis diff_ge_0_iff_ge is_Proj_algebraic is_Proj_complement positive_cblinfun_squareI)

definition measure_first_kraus_family :: \<open>(('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2, 'cl) kraus_family\<close> where
  \<open>measure_first_kraus_family = range (\<lambda>x. (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun, x))\<close>

(* TODO move *)
lemma sum_butterfly_ket_leq_id: \<open>(\<Sum>i\<in>X. butterfly (ket i) (ket i)) \<le> id_cblinfun\<close>
proof -
  have \<open>is_Proj (\<Sum>\<psi>\<in>ket ` X. butterfly \<psi> \<psi>)\<close>
    apply (rule sum_butterfly_is_Proj)
    by auto
  then have \<open>is_Proj (\<Sum>i\<in>X. butterfly (ket i) (ket i))\<close>
    by (simp add: inj_on_def sum.reindex)
  then show ?thesis
    by (auto intro!: is_Proj_leq_id)
qed

lemma kraus_family_measure_first_kraus_family: \<open>kraus_family measure_first_kraus_family\<close>
proof (unfold kraus_family_def, rule bdd_aboveI[where M=id_cblinfun])
  fix A :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
  assume \<open>A \<in> sum (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> measure_first_kraus_family}\<close>
  then obtain F where \<open>finite F\<close> and \<open>F \<subseteq> range (\<lambda>x. (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun, x))\<close>
    and AF: \<open>A = (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close>
    by (auto simp add: measure_first_kraus_family_def)
  then obtain F' where FF': \<open>F = (\<lambda>x. (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun, x)) ` F'\<close> and \<open>finite F'\<close>
    by (meson finite_subset_image)
  have \<open>A = (\<Sum>x\<in>F'. selfbutter (ket x)) \<otimes>\<^sub>o id_cblinfun\<close>
    unfolding AF FF'
    apply (subst sum.reindex)
    by (auto intro!: inj_onI simp: tensor_op_adjoint comp_tensor_op clinear.linear linear_sum[where f=\<open>\<lambda>x. x \<otimes>\<^sub>o id_cblinfun\<close>, symmetric])
  then have \<open>is_Proj A\<close>
    using sum_butterfly_is_Proj[where E=\<open>ket ` F'\<close>]
    apply (auto intro!: is_Proj_tensor_op simp:)
    by (metis (mono_tags, lifting) imageE inj_on_def ket_injective norm_ket o_def sum.cong sum.reindex)
  then show \<open>A \<le> id_cblinfun\<close>
    by (simp add: is_Proj_leq_id)
qed

lift_definition measure_first_kraus_map :: \<open>(('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) kraus_map\<close> is
  \<open>kraus_family_flatten measure_first_kraus_family\<close>
  by (auto intro!: kraus_equivalent_reflI kraus_family_measure_first_kraus_family kraus_family_kraus_family_flatten)

lemma measure_first_kraus_family_apply_has_sum: \<open>((\<lambda>x. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<rho>) has_sum kraus_family_map measure_first_kraus_family \<rho>) UNIV\<close>
proof -
  have inj: \<open>inj_on (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) UNIV\<close>
    using inj_selfbutter_ket inj_tensor_left[of id_cblinfun]
    apply (auto simp: inj_on_def)
    by force
  define \<rho>' where \<open>\<rho>' = kraus_family_map measure_first_kraus_family \<rho>\<close>
  have \<open>((\<lambda>(E,x). sandwich_tc E *\<^sub>V \<rho>) has_sum \<rho>') measure_first_kraus_family\<close>
    by (metis (no_types, lifting) \<rho>'_def has_sum_cong kraus_family_map_has_sum kraus_family_measure_first_kraus_family split_def)
  then show \<open>((\<lambda>x. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<rho>) has_sum \<rho>') UNIV\<close>
    unfolding measure_first_kraus_family_def
    apply (subst (asm) has_sum_reindex)
    by (auto simp add: inj_def o_def)
qed

lemma measure_first_kraus_family_apply: \<open>kraus_family_map measure_first_kraus_family \<rho> = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<rho>)\<close>
  using measure_first_kraus_family_apply_has_sum
  by (metis (mono_tags, lifting) infsumI)

lemma measure_first_kraus_map_apply: \<open>kraus_map_apply measure_first_kraus_map \<rho> = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<rho>)\<close>
  apply (transfer' fixing: \<rho>)
  by (simp add: measure_first_kraus_family_apply kraus_family_flatten_same_map kraus_family_measure_first_kraus_family)

lemma measure_first_kraus_map_idem[simp]: \<open>kraus_map_comp measure_first_kraus_map measure_first_kraus_map = measure_first_kraus_map\<close>
proof (intro kraus_map_apply_inj cblinfun_eqI)
  fix \<rho> :: \<open>(('a \<times> 'b) ell2, ('a \<times> 'b) ell2) trace_class\<close>

  from measure_first_kraus_family_apply_has_sum
  have sum1: \<open>(\<lambda>y. sandwich_tc (selfbutter (ket y) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<rho>) summable_on UNIV\<close>
    using summable_on_def by blast

  have \<open>kraus_map_apply (kraus_map_comp measure_first_kraus_map measure_first_kraus_map) *\<^sub>V \<rho>
          = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V
               (\<Sum>\<^sub>\<infinity>y. sandwich_tc (selfbutter (ket y) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<rho>))\<close>
    by (simp add: measure_first_kraus_map_apply kraus_map_apply_comp)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. (\<Sum>\<^sub>\<infinity>y. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V sandwich_tc (selfbutter (ket y) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<rho>))\<close>
    by (auto intro!: infsum_cong simp: sum1 simp flip: infsum_cblinfun_apply)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. (\<Sum>\<^sub>\<infinity>y. of_bool (y=x) *\<^sub>C sandwich_tc (selfbutter (ket y) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<rho>))\<close>
    by (auto intro!: infsum_cong simp: lift_cblinfun_comp[OF sandwich_tc_compose[symmetric]] comp_tensor_op cinner_ket)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<rho>)\<close>
    by (simp add: infsum_of_bool_scaleC)
  also have \<open>\<dots> = kraus_map_apply measure_first_kraus_map *\<^sub>V \<rho>\<close>
    by (simp add: measure_first_kraus_map_apply kraus_map_apply_comp)
  finally show \<open>kraus_map_apply (kraus_map_comp measure_first_kraus_map measure_first_kraus_map) *\<^sub>V \<rho>
                   = kraus_map_apply measure_first_kraus_map *\<^sub>V \<rho>\<close>
    by -
qed

lemma measure_first_kraus_map_apply': \<open>kraus_map_apply measure_first_kraus_map \<rho> = 
  (\<Sum>\<^sub>\<infinity>x. tc_tensor (tc_butterfly (ket x) (ket x)) (sandwich_tc (tensor_ell2_left (ket x)*) *\<^sub>V \<rho>))\<close>
  apply (simp add: measure_first_kraus_map_apply)
  apply (rule infsum_cong)
  apply (auto intro!: from_trace_class_inject[THEN iffD1] equal_ket cinner_ket_eqI
      simp: from_trace_class_sandwich_tc tc_tensor.rep_eq tc_butterfly.rep_eq sandwich_apply
      tensor_op_adjoint cblinfun_apply_cblinfun_compose tensor_op_ell2
      simp flip: tensor_ell2_ket)
  by (auto intro!: cinner_ket
      simp: tensor_op_adjoint tensor_op_ell2 cinner_ket
      simp flip: cinner_adj_left)

definition \<open>is_cq_operator \<rho> \<longleftrightarrow> \<rho> = kraus_map_apply measure_first_kraus_map \<rho>\<close>

lemma is_cq_operator_0[simp]: \<open>is_cq_operator 0\<close>
  by (simp add: is_cq_operator_def)

typedef ('a,'b) cq_operator = \<open>Collect is_cq_operator :: (('a\<times>'b) ell2, ('a\<times>'b) ell2) trace_class set\<close>
  apply (rule exI[of _ 0])
  by simp

(* typedef ('a,'b) cq_operator = \<open>{f :: 'a \<Rightarrow> ('b ell2, 'b ell2) trace_class. f abs_summable_on UNIV}\<close>
  morphisms cq_operator_at Abs_cq_operator
  apply (rule exI[of _ \<open>\<lambda>_. 0\<close>])
  by auto *)
setup_lifting type_definition_cq_operator

lemma mk_cq_operator_abs_summable:
  fixes f :: \<open>'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class\<close>
  assumes \<open>f abs_summable_on UNIV\<close>
  shows \<open>(\<lambda>x. tc_tensor (tc_butterfly (ket x) (ket x)) (f x)) abs_summable_on UNIV\<close>
proof -
  have *: \<open>sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V
                tc_tensor (tc_butterfly (ket y) (ket y)) (f y)
            = of_bool (y = x) *\<^sub>C tc_tensor (tc_butterfly (ket y) (ket y)) (f y)\<close> for x y
    apply (rule from_trace_class_inject[THEN iffD1])
    by (simp add: from_trace_class_sandwich_tc tc_tensor.rep_eq tc_butterfly.rep_eq sandwich_apply
        comp_tensor_op cinner_ket tensor_op_adjoint)
  show ?thesis
    using assms
    by (simp add: norm_tc_tensor norm_tc_butterfly * infsum_of_bool_scaleC flip: infsum_cblinfun_apply)
qed

lift_definition mk_cq_operator :: \<open>('cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class) \<Rightarrow> ('cl, 'qu) cq_operator\<close> is
  \<open>\<lambda>f. if f abs_summable_on UNIV then (\<Sum>\<^sub>\<infinity>x. tc_tensor (tc_butterfly (ket x) (ket x)) (f x)) else 0\<close>
proof -
  fix f :: \<open>'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class\<close>
  have *: \<open>sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V
                tc_tensor (tc_butterfly (ket y) (ket y)) (f y)
            = of_bool (y = x) *\<^sub>C tc_tensor (tc_butterfly (ket y) (ket y)) (f y)\<close> for x y
    apply (rule from_trace_class_inject[THEN iffD1])
    by (simp add: from_trace_class_sandwich_tc tc_tensor.rep_eq tc_butterfly.rep_eq sandwich_apply
        comp_tensor_op cinner_ket tensor_op_adjoint)
  show \<open>(if f abs_summable_on UNIV
            then \<Sum>\<^sub>\<infinity>x. tc_tensor (tc_butterfly (ket x) (ket x)) (f x) else 0)
           \<in> Collect is_cq_operator\<close>
    by (auto simp: is_cq_operator_def measure_first_kraus_map_apply 
      abs_summable_summable norm_tc_tensor norm_tc_butterfly infsum_of_bool_scaleC * mk_cq_operator_abs_summable
      simp flip: infsum_cblinfun_apply)
qed


lift_definition cq_operator_at0 :: \<open>(('cl \<times> 'qu) ell2, ('cl \<times> 'qu) ell2) trace_class \<Rightarrow> 'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class\<close> is
  \<open>\<lambda>\<rho> c. tensor_ell2_left (ket c)* o\<^sub>C\<^sub>L \<rho> o\<^sub>C\<^sub>L tensor_ell2_left (ket c)\<close>
  by (simp add: trace_class_comp_left trace_class_comp_right)

lift_definition cq_operator_at :: \<open>('cl, 'qu) cq_operator \<Rightarrow> 'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class\<close> is cq_operator_at0.


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
    by (simp add: cq_operator_at.rep_eq cq_operator_at0.rep_eq mk_cq_operator.rep_eq assms 1 2
        infsum_of_bool_scaleC
        flip: infsum_cblinfun_compose_left infsum_cblinfun_compose_right)
qed

lemma cq_operator_at0_summable: \<open>cq_operator_at0 \<rho> abs_summable_on UNIV\<close>
proof -
  define \<rho>' where \<open>\<rho>' = sandwich_tc swap_ell2 \<rho>\<close>
  have *: \<open>sandwich_tc (tensor_ell2_left (ket x)*) \<rho> = sandwich_tc (tensor_ell2_right (ket x)*) \<rho>'\<close> for x
    by (auto intro!: equal_ket cinner_ket_eqI from_trace_class_inject[THEN iffD1]
        simp: \<rho>'_def from_trace_class_sandwich_tc sandwich_apply
        simp flip: cinner_adj_left)
  have \<open>(\<lambda>x. sandwich_tc (tensor_ell2_right (ket x)*) \<rho>') abs_summable_on UNIV\<close>
    using partial_trace_abs_summable[of \<rho>']
    by (simp add: sandwich_apply sandwich_tc_apply)
  then have \<open>(\<lambda>x. sandwich_tc (tensor_ell2_left (ket x)*) \<rho>) abs_summable_on UNIV\<close>
    by (simp add: * )
  then show ?thesis
    by (simp add: norm_trace_class.rep_eq cq_operator_at0.rep_eq
    from_trace_class_sandwich_tc sandwich_apply)
qed

lemma cq_operator_at_summable: \<open>cq_operator_at \<rho> abs_summable_on UNIV\<close>
  apply transfer by (rule cq_operator_at0_summable)

lemma mk_cq_operator_cq_operator_at: \<open>mk_cq_operator (cq_operator_at \<rho>) = \<rho>\<close>
proof -
  have *: \<open>tc_tensor (tc_butterfly (ket x) (ket x))
                 (sandwich_tc (tensor_ell2_left (ket x)*) *\<^sub>V \<rho>)
        = tc_tensor (tc_butterfly (ket x) (ket x)) (cq_operator_at0 \<rho> x)\<close> for \<rho> x
    apply (rule from_trace_class_inject[THEN iffD1])
    by (simp add: tc_tensor.rep_eq from_trace_class_sandwich_tc cq_operator_at0.rep_eq sandwich_apply)
  show ?thesis
    apply transfer
    by (simp add: * cq_operator_at0_summable is_cq_operator_def measure_first_kraus_map_apply')
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

lemma tc_tensor_0_left[simp]: \<open>tc_tensor 0 x = 0\<close>
  apply transfer' by simp
lemma tc_tensor_0_right[simp]: \<open>tc_tensor x 0 = 0\<close>
  apply transfer' by simp

lemma mk_cq_operator_tc_compose: \<open>Rep_cq_operator
    (mk_cq_operator (\<lambda>c. tc_compose (cq_operator_at a c) (cq_operator_at b c)))
        = tc_compose (Rep_cq_operator a) (Rep_cq_operator b)\<close> (is \<open>?lhs = _\<close>)
proof -
  define a' b' where \<open>a' = cq_operator_at a\<close> and \<open>b' = cq_operator_at b\<close>
  have a'sum: \<open>a' abs_summable_on UNIV\<close>
    by (simp add: a'_def cq_operator_at_summable)
  have b'sum: \<open>b' abs_summable_on UNIV\<close>
    by (simp add: b'_def cq_operator_at_summable)
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
    by (simp add: summable mk_cq_operator.rep_eq flip: a'_def b'_def)
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
  also have \<open>\<dots> = tc_compose (Rep_cq_operator (mk_cq_operator a'))
                             (Rep_cq_operator (mk_cq_operator b'))\<close>
    by (simp add: mk_cq_operator.rep_eq a'sum b'sum)
  also have \<open>\<dots> = tc_compose (Rep_cq_operator a) (Rep_cq_operator b)\<close>
    by (simp add: mk_cq_operator_cq_operator_at a'_def b'_def)
  finally show ?thesis
    by -
qed

instantiation cq_operator :: (type,type) complex_algebra begin
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
  show \<open>((*\<^sub>R) r :: ('a, 'b) cq_operator \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> for r :: real
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
end

instantiation cq_operator :: (type,type) complex_normed_vector begin
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
end

lemma transfer_Cauchy_cq_operator[transfer_rule]:
  includes lifting_syntax
  shows \<open>(((=) ===> cr_cq_operator) ===> (\<longleftrightarrow>)) Cauchy Cauchy\<close>
  unfolding Cauchy_def dist_norm
  by transfer_prover

lemma tendsto_preserves_cq_operator: 
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
qed

lemma transfer_convergent_cq_operator[transfer_rule]:
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
qed


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

instance cq_operator :: (type,type) cbanach
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
qed *)

instantiation cq_operator :: (type,type) order begin
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
end

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

lemma kraus_map_is_cq_0[simp]: \<open>kraus_map_is_cq 0\<close>
  by (simp add: kraus_map_is_cq_def)

typedef ('cl1,'qu1,'cl2,'qu2) cq_kraus_map = \<open>Collect kraus_map_is_cq :: (('cl1\<times>'qu1) ell2, ('cl2\<times>'qu2) ell2) kraus_map set\<close>
  apply (rule exI[of _ 0])
  by simp
setup_lifting type_definition_cq_kraus_map

instantiation cq_kraus_map :: (type,type,type,type) zero begin
lift_definition zero_cq_kraus_map :: \<open>('a,'b,'c,'d) cq_kraus_map\<close> is 0
  by simp
instance..
end

lemma measure_first_kraus_map_is_cq[simp]: \<open>kraus_map_is_cq measure_first_kraus_map\<close>
  by (simp add: kraus_map_is_cq_def)

lift_definition cq_kraus_map_id :: \<open>('cl,'qu,'cl,'qu) cq_kraus_map\<close> is \<open>measure_first_kraus_map\<close>
  by auto

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


lift_definition cq_kraus_map_comp :: \<open>('cl2,'qu2,'cl3,'qu3) cq_kraus_map \<Rightarrow> ('cl1,'qu1,'cl2,'qu2) cq_kraus_map \<Rightarrow> ('cl1,'qu1,'cl3,'qu3) cq_kraus_map\<close> is
  (* \<open>\<lambda>E F c1 c3. (\<Sum>\<^sub>\<infinity>c2::'cl2. kraus_map_comp (E c2 c3) (F c1 c2))\<close> *)
  kraus_map_comp
  by (simp add: kraus_map_is_cq_comp)
(*   apply (auto intro!: simp: valid_cq_kraus_map_def)
  apply (rule abs_summable_summable) *)

lift_definition cq_operator_cases0 :: \<open>('cin \<Rightarrow> (('cin\<times>'qin) ell2,('cout\<times>'qout) ell2) kraus_map)
                              \<Rightarrow> (('cin\<times>'qin) ell2, ('cout\<times>'qout) ell2) kraus_map\<close> is
  \<open>\<lambda>\<EE> :: ('cin \<Rightarrow> (('cin\<times>'qin) ell2,('cout\<times>'qout) ell2, unit) kraus_family).
  if (\<exists>B. \<forall>x. kraus_family_norm (\<EE> x) \<le> B) then
        kraus_family_flatten (kraus_family_comp_dependent \<EE> measure_first_kraus_family) else {}\<close>
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

interpretation tensor_op_cbilinear: bounded_cbilinear tensor_op
  by simp

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

lemma finite_rank_comp_right: \<open>finite_rank (a o\<^sub>C\<^sub>L b)\<close> if \<open>finite_rank b\<close>
by -
lemma finite_rank_comp_left: \<open>finite_rank (a o\<^sub>C\<^sub>L b)\<close> if \<open>finite_rank a\<close>
by -

lemma compact_op_comp_right: \<open>compact_op (a o\<^sub>C\<^sub>L b)\<close> if \<open>compact_op b\<close>
proof -
  from that have \<open>b \<in> closure (Collect finite_rank)\<close>
  using compact_op_def by blast
  then have \<open>a o\<^sub>C\<^sub>L b \<in> cblinfun_compose a ` closure (Collect finite_rank)\<close>
    by blast
  also have \<open>\<dots> \<subseteq> closure (cblinfun_compose a ` Collect finite_rank)\<close>
    by (auto intro!: closure_bounded_linear_image_subset bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_right)
  also have \<open>\<dots> \<subseteq> closure (Collect finite_rank)\<close>
    by (auto intro!: closure_mono finite_rank_comp_right)
  finally show \<open>compact_op (a o\<^sub>C\<^sub>L b)\<close>
    using compact_op_def by blast
qed

lemma compact_op_comp_left: \<open>compact_op (a o\<^sub>C\<^sub>L b)\<close> if \<open>compact_op a\<close>
proof -
  from that have \<open>a \<in> closure (Collect finite_rank)\<close>
  using compact_op_def by blast
  then have \<open>a o\<^sub>C\<^sub>L b \<in> (\<lambda>a. a o\<^sub>C\<^sub>L b) ` closure (Collect finite_rank)\<close>
    by blast
  also have \<open>\<dots> \<subseteq> closure ((\<lambda>a. a o\<^sub>C\<^sub>L b) ` Collect finite_rank)\<close>
    by (auto intro!: closure_bounded_linear_image_subset bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left)
  also have \<open>\<dots> \<subseteq> closure (Collect finite_rank)\<close>
    by (auto intro!: closure_mono finite_rank_comp_left)
  finally show \<open>compact_op (a o\<^sub>C\<^sub>L b)\<close>
    using compact_op_def by blast
qed

lemma norm_cblinfun_bound_unit: "norm f \<le> b"
  if \<open>0 \<le> b\<close> and \<open>\<And>x. norm x = 1 \<Longrightarrow> norm (f *\<^sub>V x) \<le> b\<close>
proof (rule norm_cblinfun_bound)
  show \<open>0 \<le> b\<close> by (fact that)
  show \<open>norm (f *\<^sub>V x) \<le> b * norm x\<close> for x
  proof (cases \<open>x = 0\<close>)
    case True
    then show ?thesis by simp
  next
    case False
    then have \<open>norm (f *\<^sub>V x) = norm (f *\<^sub>V sgn x) * norm x\<close>
      by (simp add: sgn_div_norm cblinfun.scaleR_right)
    also have \<open>\<dots> \<le> b * norm x\<close>
      by (auto intro!: mult_right_mono that simp: False norm_sgn)
    finally show ?thesis
      by -
  qed
qed

lemma hilbert_schmidt_norm_geq_norm:
(* TODO cite conway operators, Prop 18.6(c) *)
  assumes \<open>hilbert_schmidt a\<close>
  shows \<open>norm a \<le> hilbert_schmidt_norm a\<close>
proof -
  have \<open>norm (a x) \<le> hilbert_schmidt_norm a\<close> if \<open>norm x = 1\<close> for x
  proof -
    obtain B where \<open>x \<in> B\<close> and \<open>is_onb B\<close>
      using orthonormal_basis_exists[of \<open>{x}\<close>] \<open>norm x = 1\<close>
      by force
    have \<open>(norm (a x))\<^sup>2 = (\<Sum>\<^sub>\<infinity>x\<in>{x}. (norm (a x))\<^sup>2)\<close>
      by simp
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a x))\<^sup>2)\<close>
      apply (rule infsum_mono_neutral)
      by (auto intro!: summable_hilbert_schmidt_norm_square \<open>is_onb B\<close> assms \<open>x \<in> B\<close>)
    also have \<open>\<dots> = (hilbert_schmidt_norm a)\<^sup>2\<close>
      using infsum_hilbert_schmidt_norm_square[OF \<open>is_onb B\<close> assms]
      by -
    finally show ?thesis
      by force
  qed
  then show ?thesis
    by (auto intro!: norm_cblinfun_bound_unit)
qed

(* lemma hilbert_schmidt_minus: \<open>hilbert_schmidt (a - b)\<close> if \<open>hilbert_schmidt a\<close> and \<open>hilbert_schmidt b\<close>
  for a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  using hilbert_schmidt_plus hilbert_schmidt_uminus that by fastforce *)

lemma rank1_trace_class: \<open>trace_class a\<close> if \<open>rank1 a\<close>
  for a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  using Compact_Operators.rank1_def that by force

lemma finite_rank_trace_class: \<open>trace_class a\<close> if \<open>finite_rank a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof -
  from \<open>finite_rank a\<close> obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> Collect rank1\<close>
    and a_def: \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
    by (smt (verit, ccfv_threshold) complex_vector.span_explicit finite_rank_def mem_Collect_eq)
  then show \<open>trace_class a\<close>
    unfolding a_def
    apply induction
    by (auto intro!: trace_class_plus trace_class_scaleC intro: rank1_trace_class)
qed

lemma trace_class_hilbert_schmidt: \<open>hilbert_schmidt a\<close> if \<open>trace_class a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (auto intro!: trace_class_comp_right that simp: hilbert_schmidt_def)

lemma finite_rank_hilbert_schmidt: \<open>hilbert_schmidt a\<close> if \<open>finite_rank a\<close>
  using finite_rank_comp_right finite_rank_trace_class hilbert_schmidtI that by blast

lemma hilbert_schmidt_compact: \<open>compact_op a\<close> if \<open>hilbert_schmidt a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  \<comment> \<open>(* TODO cite: conway operators *), Corollary 18.7.
      (Only the second part. The first part is stated inside the proof though.)\<close>
proof -
  have \<open>\<exists>b. finite_rank b \<and> hilbert_schmidt_norm (b - a) < \<epsilon>\<close> if \<open>\<epsilon> > 0\<close> for \<epsilon>
  proof -
    have \<open>\<epsilon>\<^sup>2 > 0\<close>
      using that by force
    obtain B :: \<open>'a set\<close> where \<open>is_onb B\<close>
      using is_onb_some_chilbert_basis by blast
    with \<open>hilbert_schmidt a\<close> have a_sum_B: \<open>(\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) summable_on B\<close>
      by (auto intro!: summable_hilbert_schmidt_norm_square)
    then have \<open>((\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) has_sum (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2)) B\<close>
      using has_sum_infsum by blast
    from tendsto_iff[THEN iffD1, rule_format, OF this[unfolded has_sum_def] \<open>\<epsilon>\<^sup>2 > 0\<close>]
    obtain F where [simp]: \<open>finite F\<close> and \<open>F \<subseteq> B\<close>
      and Fbound: \<open>dist (\<Sum>x\<in>F. (norm (a *\<^sub>V x))\<^sup>2) (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2) < \<epsilon>\<^sup>2\<close>
      apply atomize_elim
      by (auto intro!: simp: eventually_finite_subsets_at_top)
    define p b where \<open>p = (\<Sum>x\<in>F. selfbutter x)\<close> and \<open>b = a o\<^sub>C\<^sub>L p\<close>
    have [simp]: \<open>p x = x\<close> if \<open>x \<in> F\<close> for x
      apply (simp add: p_def cblinfun.sum_left)
      apply (subst sum_single[where i=x])
      using \<open>F \<subseteq> B\<close> that \<open>is_onb B\<close>
      by (auto intro!: simp:  cnorm_eq_1 is_onb_def is_ortho_set_def)
    have [simp]: \<open>p x = 0\<close> if \<open>x \<in> B - F\<close> for x
      using \<open>F \<subseteq> B\<close> that \<open>is_onb B\<close>
      apply (auto intro!: sum.neutral simp add: p_def cblinfun.sum_left is_onb_def is_ortho_set_def)
      by auto
    have \<open>finite_rank p\<close>
      by (simp add: finite_rank_sum p_def)
    then have \<open>finite_rank b\<close>
      by (simp add: b_def finite_rank_comp_right)
    with \<open>hilbert_schmidt a\<close> have \<open>hilbert_schmidt (b - a)\<close>
      by (auto intro!: hilbert_schmidt_minus intro: finite_rank_hilbert_schmidt)
    then have \<open>(hilbert_schmidt_norm (b - a))\<^sup>2 = (\<Sum>\<^sub>\<infinity>x\<in>B. (norm ((b - a) *\<^sub>V x))\<^sup>2)\<close>
      by (simp add: infsum_hilbert_schmidt_norm_square \<open>is_onb B\<close>)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B-F. (norm (a *\<^sub>V x))\<^sup>2)\<close>
      by (auto intro!: infsum_cong_neutral
          simp: b_def cblinfun.diff_left)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2) - (\<Sum>x\<in>F. (norm (a *\<^sub>V x))\<^sup>2)\<close>
      apply (subst infsum_Diff)
      using \<open>F \<subseteq> B\<close> a_sum_B by auto
    also have \<open>\<dots> < \<epsilon>\<^sup>2\<close>
      using Fbound
      by (simp add: dist_norm)
    finally show ?thesis
      using \<open>finite_rank b\<close>
      using power_less_imp_less_base that by fastforce
  qed
  then have \<open>\<exists>b. finite_rank b \<and> dist b a < \<epsilon>\<close> if \<open>\<epsilon> > 0\<close> for \<epsilon>
    apply (rule ex_mono[rule_format, rotated])
     apply (auto intro!: that simp: dist_norm)
    using hilbert_schmidt_minus \<open>hilbert_schmidt a\<close> finite_rank_hilbert_schmidt hilbert_schmidt_norm_geq_norm
    by fastforce
  then show ?thesis
    by (simp add: compact_op_def closure_approachable)
qed

lemma trace_class_compact: \<open>compact_op a\<close> if \<open>trace_class a\<close> 
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (simp add: hilbert_schmidt_compact that trace_class_hilbert_schmidt)


lemma cspan_tc_transfer[transfer_rule]: 
  includes lifting_syntax
  shows \<open>(rel_set cr_trace_class ===> rel_set cr_trace_class) cspan cspan\<close>
proof (intro rel_funI rel_setI)
  fix B :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close> and C
  assume \<open>rel_set cr_trace_class B C\<close>
  then have BC: \<open>B = from_trace_class ` C\<close>
    by (auto intro!: simp: cr_trace_class_def image_iff rel_set_def)
      (*     then have tc_B: \<open>B \<subseteq> Collect trace_class\<close> (* TODO used? *)
      by auto *)

  show \<open>\<exists>t\<in>cspan C. cr_trace_class a t\<close> if \<open>a \<in> cspan B\<close> for a
  proof -
    from that obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> B\<close> and a_sum: \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
      by (auto simp: complex_vector.span_explicit)
    from \<open>F \<subseteq> B\<close>
    obtain F' where \<open>F' \<subseteq> C\<close> and FF': \<open>F = from_trace_class ` F'\<close>
      by (auto elim!: subset_imageE simp: BC)
    define t where \<open>t = (\<Sum>x\<in>F'. f (from_trace_class x) *\<^sub>C x)\<close>
    have \<open>a = from_trace_class t\<close>
      by (simp add: a_sum t_def from_trace_class_sum scaleC_trace_class.rep_eq FF'
          sum.reindex o_def from_trace_class_inject inj_on_def)
    moreover have \<open>t \<in> cspan C\<close>
      by (metis (no_types, lifting) \<open>F' \<subseteq> C\<close> complex_vector.span_clauses(4) complex_vector.span_sum complex_vector.span_superset subsetD t_def)
    ultimately show \<open>\<exists>t\<in>cspan C. cr_trace_class a t\<close>
      by (auto simp: cr_trace_class_def)
  qed

  show \<open>\<exists>a\<in>cspan B. cr_trace_class a t\<close> if \<open>t \<in> cspan C\<close> for t
  proof -
    from that obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> C\<close> and t_sum: \<open>t = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
      by (auto simp: complex_vector.span_explicit)
    define a where \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C from_trace_class x)\<close>
    then have \<open>a = from_trace_class t\<close>
      by (simp add: t_sum a_def from_trace_class_sum scaleC_trace_class.rep_eq)
    moreover have \<open>a \<in> cspan B\<close>
      using BC \<open>F \<subseteq> C\<close> 
      by (auto intro!: complex_vector.span_base complex_vector.span_sum complex_vector.span_scale simp: a_def)
    ultimately show ?thesis
      by (auto simp: cr_trace_class_def)
  qed
qed

(* lemma
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

(* TODO move *)
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
      by x
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
        apply (auto intro!: simp: )
      by -
    from f'_range f'_limit
    show \<open>\<exists>f'. (\<forall>n. f' n \<in> cspan ((\<lambda>(\<xi>, \<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))) \<and> f' \<longlonglongrightarrow> x\<close>
      by auto
  qed
  then show ?thesis
    by auto
qed

definition diagonal_operator where \<open>diagonal_operator f = 
  (if bdd_above (range (\<lambda>x. cmod (f x))) then explicit_cblinfun (\<lambda>x y. of_bool (x=y) * f x) else 0)\<close>

lemma diagonal_operator_exists:
  assumes \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  shows \<open>explicit_cblinfun_exists (\<lambda>x y. of_bool (x = y) * f x)\<close>
  by x

lemma diagonal_operator_ket:
  assumes \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  shows \<open>diagonal_operator f (ket x) = f x *\<^sub>C ket x\<close>
proof -
  have [simp]: \<open>has_ell2_norm (\<lambda>b. of_bool (b = x) * f b)\<close>
    by (auto intro!: finite_nonzero_values_imp_summable_on simp: has_ell2_norm_def)
  have \<open>Abs_ell2 (\<lambda>b. of_bool (b = x) * f b) = f x *\<^sub>C ket x\<close>
    apply (rule Rep_ell2_inject[THEN iffD1])
    by (auto simp: Abs_ell2_inverse scaleC_ell2.rep_eq ket.rep_eq)
  then show ?thesis
    by (auto intro!: simp: diagonal_operator_def assms explicit_cblinfun_ket diagonal_operator_exists)
qed

lemma diagonal_operator_invalid:
  assumes \<open>\<not> bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  shows \<open>diagonal_operator f = 0\<close>
  by (simp add: assms diagonal_operator_def)

lemma diagonal_operator_comp:
  assumes \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  assumes \<open>bdd_above (range (\<lambda>x. cmod (g x)))\<close>
  shows \<open>diagonal_operator f o\<^sub>C\<^sub>L diagonal_operator g = diagonal_operator (\<lambda>x. (f x * g x))\<close>
proof -
  have \<open>bdd_above (range (\<lambda>x. cmod (f x * g x)))\<close>
  proof -
    from assms(1) obtain F where \<open>cmod (f x) \<le> F\<close> for x
      by (auto simp: bdd_above_def)
    moreover from assms(2) obtain G where \<open>cmod (g x) \<le> G\<close> for x
      by (auto simp: bdd_above_def)
    ultimately have \<open>cmod (f x * g x) \<le> F * G\<close> for x
      by (smt (verit, del_insts) mult_right_mono norm_ge_zero norm_mult ordered_comm_semiring_class.comm_mult_left_mono)
    then show ?thesis
      by fast
  qed
  then show ?thesis
    by (auto intro!: equal_ket simp: diagonal_operator_ket assms cblinfun.scaleC_right)
qed

lemma diagonal_operator_adj: \<open>diagonal_operator f* = diagonal_operator (\<lambda>x. cnj (f x))\<close>
  apply (cases \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>)
  by (auto intro!: equal_ket cinner_ket_eqI 
      simp: diagonal_operator_ket cinner_adj_right diagonal_operator_invalid)

(* TODO move *)
lemma complex_of_real_cmod: \<open>complex_of_real (cmod x) = abs x\<close>
  by (simp add: abs_complex_def)

lemma diagonal_operator_pos:
  assumes \<open>\<And>x. f x \<ge> 0\<close>
  shows \<open>diagonal_operator f \<ge> 0\<close>
proof (cases \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>)
  case True
  have [simp]: \<open>csqrt (f x) = sqrt (cmod (f x))\<close> for x
    by (simp add: Extra_Ordered_Fields.complex_of_real_cmod assms of_real_sqrt)
  have bdd: \<open>bdd_above (range (\<lambda>x. sqrt (cmod (f x))))\<close>
  proof -
    from True obtain B where \<open>cmod (f x) \<le> B\<close> for x
      by (auto simp: bdd_above_def)
    then show ?thesis
      by (auto intro!: bdd_aboveI[where M=\<open>sqrt B\<close>] simp: )
  qed
  show ?thesis
    apply (rule positive_cblinfun_squareI[where B=\<open>diagonal_operator (\<lambda>x. csqrt (f x))\<close>])
    by (simp add: assms diagonal_operator_adj diagonal_operator_comp bdd complex_of_real_cmod abs_pos
        flip: of_real_mult)
next
  case False
  then show ?thesis
    by (simp add: diagonal_operator_invalid)
qed



lemma abs_op_diagonal_operator: 
  \<open>abs_op (diagonal_operator f) = diagonal_operator (\<lambda>x. abs (f x))\<close>
proof (cases \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>)
  case True
  show ?thesis
    apply (rule abs_opI[symmetric])
    by (auto intro!: diagonal_operator_pos abs_nn simp: True diagonal_operator_adj diagonal_operator_comp cnj_x_x)
next
  case False
  then show ?thesis
    by (simp add: diagonal_operator_invalid)
qed

lift_definition diagonal_operator_tc :: \<open>('a \<Rightarrow> complex) \<Rightarrow> ('a ell2, 'a ell2) trace_class\<close> is
  \<open>\<lambda>f. if f abs_summable_on UNIV then diagonal_operator f else 0\<close>
proof (rule CollectI)
  fix f :: \<open>'a \<Rightarrow> complex\<close>
  show \<open>trace_class (if f abs_summable_on UNIV then diagonal_operator f else 0)\<close>
  proof (cases \<open>f abs_summable_on UNIV\<close>)
    case True
    have bdd: \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
    proof (rule bdd_aboveI2)
      fix x
      have \<open>cmod (f x) = (\<Sum>\<^sub>\<infinity>x\<in>{x}. cmod (f x))\<close>
        by simp
      also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x. cmod (f x))\<close>
        apply (rule infsum_mono_neutral)
        by (auto intro!: True)
      finally show \<open>cmod (f x) \<le> (\<Sum>\<^sub>\<infinity>x. cmod (f x))\<close>
        by -
    qed
    have \<open>trace_class (diagonal_operator f)\<close>
      by (auto intro!: trace_classI[OF is_onb_ket] summable_on_reindex[THEN iffD2] True
          simp: abs_op_diagonal_operator o_def diagonal_operator_ket bdd)
    with True show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by simp
  qed
qed

lemma from_trace_class_diagonal_operator_tc:
  assumes \<open>f abs_summable_on UNIV\<close>
  shows \<open>from_trace_class (diagonal_operator_tc f) = diagonal_operator f\<close>
  apply (transfer fixing: f)
  using assms by simp

lemma summable_on_bdd_above_real: \<open>bdd_above (f ` M)\<close> if \<open>f summable_on M\<close> for f :: \<open>'a \<Rightarrow> real\<close>
proof -
  from that have \<open>f abs_summable_on M\<close>
    unfolding summable_on_iff_abs_summable_on_real[symmetric]
    by -
  then have \<open>bdd_above (sum (\<lambda>x. norm (f x)) ` {F. F \<subseteq> M \<and> finite F})\<close>
    unfolding abs_summable_iff_bdd_above by simp
  then have \<open>bdd_above (sum (\<lambda>x. norm (f x)) ` (\<lambda>x. {x}) ` M)\<close>
    apply (rule bdd_above_mono)
    by auto
  then have \<open>bdd_above ((\<lambda>x. norm (f x)) ` M)\<close>
    by (simp add: image_image)
  then show ?thesis
    by (simp add: bdd_above_mono2)
qed

lemma vector_sandwich_partial_trace_has_sum:
  \<open>((\<lambda>z. ((x \<otimes>\<^sub>s ket z) \<bullet>\<^sub>C (from_trace_class \<rho> *\<^sub>V (y \<otimes>\<^sub>s ket z))))
      has_sum x \<bullet>\<^sub>C (from_trace_class (partial_trace \<rho>) *\<^sub>V y)) UNIV\<close>
proof -
  define x\<rho>y where \<open>x\<rho>y = x \<bullet>\<^sub>C (from_trace_class (partial_trace \<rho>) *\<^sub>V y)\<close>
  have \<open>((\<lambda>j. Abs_trace_class (tensor_ell2_right (ket j)* o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L tensor_ell2_right (ket j))) 
        has_sum partial_trace \<rho>) UNIV\<close>
    using partial_trace_has_sum by force
  then have \<open>((\<lambda>j. x \<bullet>\<^sub>C (from_trace_class (Abs_trace_class (tensor_ell2_right (ket j)* o\<^sub>C\<^sub>L 
                          from_trace_class \<rho> o\<^sub>C\<^sub>L tensor_ell2_right (ket j))) *\<^sub>V y))
        has_sum x\<rho>y) UNIV\<close>
    unfolding x\<rho>y_def
    apply (rule Infinite_Sum.has_sum_bounded_linear[rotated])
    by (intro bounded_clinear.bounded_linear bounded_linear_intros)
  then have \<open>((\<lambda>j. x \<bullet>\<^sub>C (tensor_ell2_right (ket j)* *\<^sub>V from_trace_class \<rho> *\<^sub>V y \<otimes>\<^sub>s ket j)) has_sum
     x\<rho>y) UNIV\<close>
    by (simp add: x\<rho>y_def Abs_trace_class_inverse trace_class_comp_left trace_class_comp_right)
  then show ?thesis
    by (metis (no_types, lifting) cinner_adj_right has_sum_cong tensor_ell2_right_apply x\<rho>y_def)
qed

lemma vector_sandwich_partial_trace:
  \<open>x \<bullet>\<^sub>C (from_trace_class (partial_trace \<rho>) *\<^sub>V y) =
      (\<Sum>\<^sub>\<infinity>z. ((x \<otimes>\<^sub>s ket z) \<bullet>\<^sub>C (from_trace_class \<rho> *\<^sub>V (y \<otimes>\<^sub>s ket z))))\<close>
  by (metis (mono_tags, lifting) infsumI vector_sandwich_partial_trace_has_sum)


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
          (butterfly (ket w) (ket z) \<otimes>\<^sub>o id_cblinfun)) *\<^sub>V \<rho>) summable_on UNIV\<close>
    by (auto intro!: simp: cq_map_from_distr0_def case_prod_unfold
        kraus_family_map_def summable_on_reindex inj_def o_def)

  have \<open>ket y \<bullet>\<^sub>C (from_trace_class (kraus_family_map (cq_map_from_distr0 \<mu>) \<rho>) *\<^sub>V ket x)
    = ket (y1, y2) \<bullet>\<^sub>C (from_trace_class
     (\<Sum>\<^sub>\<infinity>(w,z). sandwich_tc (sqrt (prob \<mu> w) *\<^sub>R 
          (butterfly (ket w) (ket z) \<otimes>\<^sub>o id_cblinfun)) *\<^sub>V \<rho>) *\<^sub>V ket (x1, x2))\<close>
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
      (\<Sum>\<^sub>\<infinity>z. ((ket y2 \<otimes>\<^sub>s ket z) \<bullet>\<^sub>C (from_trace_class (sandwich_tc swap_ell2 *\<^sub>V \<rho>) *\<^sub>V (ket x2 \<otimes>\<^sub>s ket z))))\<close>
    apply (rule arg_cong[where f=\<open>%x. _ * _ *\<^sub>C x\<close>])
    apply (rule infsum_cong)
    by (simp add: from_trace_class_sandwich_tc sandwich_apply flip: cinner_adj_left)
  also have \<open>\<dots> = prob \<mu> x1 * of_bool (y1 = x1) *
    (ket y2 \<bullet>\<^sub>C (from_trace_class (partial_trace (sandwich_tc swap_ell2 *\<^sub>V \<rho>)) *\<^sub>V ket x2))\<close>
    by (simp add: vector_sandwich_partial_trace)
  also have \<open>\<dots> = ket y \<bullet>\<^sub>C (from_trace_class
             (tc_tensor (diagonal_operator_tc (\<lambda>x. complex_of_real (prob \<mu> x)))
               (partial_trace (sandwich_tc swap_ell2 *\<^sub>V \<rho>))) *\<^sub>V ket x)\<close>
    by (simp add: x y tc_tensor.rep_eq tensor_op_ell2 diagonal_operator_tc.rep_eq diagonal_operator_ket
        flip: tensor_ell2_ket)
  finally show \<open>ket y \<bullet>\<^sub>C (from_trace_class (kraus_family_map (cq_map_from_distr0 \<mu>) \<rho>) *\<^sub>V ket x) =
           ket y \<bullet>\<^sub>C
           (from_trace_class
             (tc_tensor (diagonal_operator_tc (\<lambda>x. complex_of_real (prob \<mu> x)))
               (partial_trace (sandwich_tc swap_ell2 *\<^sub>V \<rho>))) *\<^sub>V
            ket x)\<close>
    by -
qed

lemma cq_map_from_distr1_apply:
  fixes \<mu> :: \<open>'c distr\<close> and \<rho> :: \<open>(('d\<times>'q) ell2, ('d\<times>'q) ell2) trace_class\<close>
  (* defines \<open>\<psi> \<equiv> Abs_ell2 (\<lambda>x. sqrt (prob \<mu> x))\<close> *)
  shows \<open>kraus_map_apply (cq_map_from_distr1 \<mu>) \<rho> = tc_tensor (diagonal_operator_tc (\<lambda>x. complex_of_real (prob \<mu> x)))
            (partial_trace (sandwich_tc swap_ell2 *\<^sub>V \<rho>))\<close>
  apply (transfer' fixing: \<mu> \<rho>)
  by (simp add: cq_map_from_distr0_apply kraus_family_flatten_same_map kraus_family_cq_map_from_distr0)

lift_definition cq_map_from_distr :: \<open>'c distr \<Rightarrow> ('d, 'q, 'c, 'q) cq_kraus_map\<close> is
  cq_map_from_distr1
  apply (transfer' fixing: )
  apply (auto intro!: simp: )
  by -
(* proof (rule CollectI)
  fix \<mu> :: \<open>'c distr\<close>
  have \<open>kraus_map_apply (kraus_map_comp measure_first_kraus_map
            (kraus_map_comp (cq_map_from_distr0 \<mu>) measure_first_kraus_map)) *\<^sub>V \<rho> =
         kraus_map_apply (cq_map_from_distr0 \<mu>) *\<^sub>V \<rho>\<close> for \<rho> :: \<open>(('d\<times>'q) ell2, _) trace_class\<close>
  proof -

    show ?thesis
      by x
  qed
  then show \<open>kraus_map_is_cq (cq_map_from_distr0 \<mu> :: (('d\<times>'q) ell2, ('c\<times>'q) ell2) kraus_map)\<close>
    by (auto intro!: ext kraus_map_apply_inj cblinfun_eqI simp: kraus_map_is_cq_def)
qed *)

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
