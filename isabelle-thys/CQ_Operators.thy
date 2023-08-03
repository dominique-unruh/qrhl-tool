theory CQ_Operators
  imports Tensor_Product.Trace_Class Registers2.Missing_Bounded_Operators Discrete_Distributions Kraus_Maps
    Tensor_Product.Partial_Trace
begin

(* TODO move *)
lift_definition tc_tensor :: \<open>('a ell2, 'b ell2) trace_class \<Rightarrow> ('c ell2, 'd ell2) trace_class \<Rightarrow> 
      (('a \<times> 'c) ell2, ('b \<times> 'd) ell2) trace_class\<close> is
  tensor_op
  by (auto intro!: trace_class_tensor)


lemma infsum_product:
  fixes f :: \<open>'a \<Rightarrow> 'c :: {topological_semigroup_mult,division_ring,banach}\<close>
  assumes \<open>(\<lambda>(x, y). f x * g y) summable_on X \<times> Y\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. f x) * (\<Sum>\<^sub>\<infinity>y\<in>Y. g y) = (\<Sum>\<^sub>\<infinity>(x,y)\<in>X\<times>Y. f x * g y)\<close>
  using assms
  by (simp add: infsum_cmult_right' infsum_cmult_left' flip: infsum_Sigma'_banach)

lemma infsum_product':
  fixes f :: \<open>'a \<Rightarrow> 'c :: {banach,times,real_normed_algebra}\<close> and g :: \<open>'b \<Rightarrow> 'c\<close>
  assumes \<open>f abs_summable_on X\<close>
  assumes \<open>g abs_summable_on Y\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. f x) * (\<Sum>\<^sub>\<infinity>y\<in>Y. g y) = (\<Sum>\<^sub>\<infinity>(x,y)\<in>X\<times>Y. f x * g y)\<close>
  using assms
  by (simp add: abs_summable_times infsum_cmult_right infsum_cmult_left abs_summable_summable flip: infsum_Sigma'_banach)

(* TODO move *)
lemma trace_norm_tensor: \<open>trace_norm (a \<otimes>\<^sub>o b) = trace_norm a * trace_norm b\<close>
  apply (rule of_real_hom.injectivity[where 'a=complex])
  by (simp add: abs_op_tensor trace_tensor flip: trace_abs_op)


(* TODO move *)
lemma bounded_cbilinear_tc_tensor: \<open>bounded_cbilinear tc_tensor\<close>
  unfolding bounded_cbilinear_def
  apply transfer
  by (auto intro!: exI[of _ 1]
      simp: trace_norm_tensor tensor_op_left_add tensor_op_right_add tensor_op_scaleC_left tensor_op_scaleC_right)
lemmas bounded_clinear_tc_tensor_left[bounded_clinear] = bounded_cbilinear.bounded_clinear_left[OF bounded_cbilinear_tc_tensor]
lemmas bounded_clinear_tc_tensor_right[bounded_clinear] = bounded_cbilinear.bounded_clinear_right[OF bounded_cbilinear_tc_tensor]


(* TODO move *)
lemma bounded_cbilinear_tc_compose: \<open>bounded_cbilinear tc_compose\<close>
  unfolding bounded_cbilinear_def
  apply transfer
  apply (auto intro!: exI[of _ 1] simp: cblinfun_compose_add_left cblinfun_compose_add_right)
  by (meson Unsorted_HSTP.norm_leq_trace_norm dual_order.trans mult_right_mono trace_norm_comp_right trace_norm_nneg)
lemmas bounded_clinear_tc_compose_left[bounded_clinear] = bounded_cbilinear.bounded_clinear_left[OF bounded_cbilinear_tc_compose]
lemmas bounded_clinear_tc_compose_right[bounded_clinear] = bounded_cbilinear.bounded_clinear_right[OF bounded_cbilinear_tc_compose]

(* TODO move *)
lemma tc_tensor_scaleC_left: \<open>tc_tensor (c *\<^sub>C a) b = c *\<^sub>C tc_tensor a b\<close>
  apply transfer'
  by (simp add: tensor_op_scaleC_left)
lemma tc_tensor_scaleC_right: \<open>tc_tensor a (c *\<^sub>C b) = c *\<^sub>C tc_tensor a b\<close>
  apply transfer'
  by (simp add: tensor_op_scaleC_right)
  
(* TODO move *)
lemma comp_tc_tensor: \<open>tc_compose (tc_tensor a b) (tc_tensor c d) = tc_tensor (tc_compose a c) (tc_compose b d)\<close>
  apply transfer'
  by (rule comp_tensor_op)

(* TODO move *)
lift_definition tc_butterfly :: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space \<Rightarrow> ('b,'a) trace_class\<close>
  is butterfly
  by simp

(* TODO move *)
lemma norm_tc_butterfly: \<open>norm (tc_butterfly \<psi> \<phi>) = norm \<psi> * norm \<phi>\<close>
  apply (transfer fixing: \<psi> \<phi>)
  by (simp add: trace_norm_butterfly)

(* TODO move *)
lemma norm_tc_tensor: \<open>norm (tc_tensor a b) = norm a * norm b\<close>
  apply transfer'
  apply (rule of_real_hom.injectivity[where 'a=complex])
  by (simp add: abs_op_tensor trace_tensor flip: trace_abs_op)


lemma comp_tc_butterfly[simp]: \<open>tc_compose (tc_butterfly a b) (tc_butterfly c d) = (b \<bullet>\<^sub>C c) *\<^sub>C tc_butterfly a d\<close>
  apply transfer'
  by simp

lemma choice4':
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
qed

(* TODO move *)
lemma summable_on_diff:
  fixes f g :: "'a \<Rightarrow> 'b::real_normed_vector"  (* Can probably be shown for a much wider type class. *)
  assumes \<open>f summable_on A\<close>
  assumes \<open>g summable_on A\<close>
  shows \<open>(\<lambda>x. f x - g x) summable_on A\<close>
  using summable_on_add[where f=f and g=\<open>\<lambda>x. - g x\<close>] summable_on_uminus[where f=g]
  using assms by auto

lemma tc_tensor_pos: \<open>tc_tensor a b \<ge> 0\<close> if \<open>a \<ge> 0\<close> and \<open>b \<ge> 0\<close>
  for a :: \<open>('a ell2,'a ell2) trace_class\<close> and b :: \<open>('b ell2,'b ell2) trace_class\<close>
  using that apply transfer'
  by (rule tensor_op_pos)

(* TODO move *)
lemma tc_butterfly_pos[simp]: \<open>0 \<le> tc_butterfly \<psi> \<psi>\<close>
  apply transfer
  by simp

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















definition measure_first_kraus_family :: \<open>(('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) kraus_family\<close> where
  \<open>measure_first_kraus_family = indicator (range (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun))\<close>

lemma kraus_family_measure_first_kraus_family: \<open>kraus_family measure_first_kraus_family\<close>
proof -
  have \<open>norm (\<Sum>E\<in>F. indicator (range (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun)) E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> 1\<close>
    if \<open>finite F\<close> for F :: \<open>(('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2) set\<close>
  proof -
    have inj: \<open>inj_on (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) F'\<close> for F' :: \<open>'a set\<close>
      using inj_selfbutter_ket inj_tensor_left[of id_cblinfun]
      apply (auto simp: inj_on_def)
      by force
    define F' where \<open>F' = (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) -` F\<close>
    have proj: \<open>is_Proj (\<Sum>x\<in>F'. selfbutter (ket x))\<close>
      using sum_butterfly_is_Proj[of \<open>ket ` F'\<close>]
      apply auto
      by (metis (mono_tags, lifting) imageE inj_on_def ket_injective norm_ket o_def sum.cong sum.reindex)
    have [simp]: \<open>finite F'\<close>
      using that inj F'_def finite_vimageI by blast
    have \<open>norm (\<Sum>E\<in>F. indicator (range (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun)) E *\<^sub>C (E* o\<^sub>C\<^sub>L E))
        = norm (\<Sum>E\<in>(\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) ` F'. indicator (range (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun)) E *\<^sub>C (E* o\<^sub>C\<^sub>L E)  :: ('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2)\<close>
      apply (rule arg_cong[where f=norm])
      apply (rule sum.mono_neutral_cong_right)
      by (auto intro!: that simp: F'_def)
    also have \<open>\<dots> = norm (\<Sum>x\<in>F'. ((selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun)* o\<^sub>C\<^sub>L (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun)) :: ('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2)\<close>
      apply (rule arg_cong[where f=norm])
      apply (subst sum.reindex)
      by (auto intro!: inj)
    also have \<open>\<dots> \<le> 1\<close>
      by (auto intro!: norm_is_Proj proj simp: tensor_op_adjoint comp_tensor_op tensor_op_norm
          simp flip: complex_vector.linear_sum[where f=\<open>\<lambda>a. a \<otimes>\<^sub>o id_cblinfun\<close>])
    finally show ?thesis
      by -
  qed
  then show ?thesis
    by (auto simp: kraus_family_def measure_first_kraus_family_def of_nat_indicator)
qed

lift_definition measure_first_kraus_map :: \<open>(('cl\<times>'qu) ell2, ('cl\<times>'qu) ell2) kraus_map\<close> is
  measure_first_kraus_family
  by (auto intro!: kraus_equivalent_reflI kraus_family_measure_first_kraus_family)

lemma measure_first_kraus_map_idem[simp]: \<open>kraus_map_comp measure_first_kraus_map measure_first_kraus_map = measure_first_kraus_map\<close>
  by xxx

lemma measure_first_kraus_family_apply: \<open>kraus_family_map measure_first_kraus_family \<rho> = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<rho>)\<close>
proof -
  have inj: \<open>inj_on (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) UNIV\<close>
    using inj_selfbutter_ket inj_tensor_left[of id_cblinfun]
    apply (auto simp: inj_on_def)
    by force
  have \<open>kraus_family_map measure_first_kraus_family \<rho> = (\<Sum>\<^sub>\<infinity>E. indicator (range (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun)) E *\<^sub>C (sandwich_tc E *\<^sub>V \<rho>))\<close>
    by (simp add: kraus_family_map_def measure_first_kraus_family_def of_nat_indicator)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>range (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun). indicator (range (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun)) E *\<^sub>C (sandwich_tc E *\<^sub>V \<rho>))\<close>
    apply (rule infsum_cong_neutral)
    by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<rho>)\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj simp: o_def)
  finally show ?thesis
    by -
qed

lemma measure_first_kraus_map_apply: \<open>kraus_map_apply measure_first_kraus_map \<rho> = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<rho>)\<close>
  apply (transfer' fixing: \<rho>)
  by (fact measure_first_kraus_family_apply)


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

lemma infsum_single: 
  assumes "\<And>j. j \<noteq> i \<Longrightarrow> j\<in>A \<Longrightarrow> f j = 0"
  shows "infsum f A = (if i\<in>A then f i else 0)"
  apply (subst infsum_cong_neutral[where T=\<open>A \<inter> {i}\<close> and g=f])
  using assms by auto

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
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. tc_compose (tc_tensor (tc_butterfly (ket x) (ket x)) (a' x))
                                          (tc_tensor (tc_butterfly (ket y) (ket y)) (b' y)))\<close>
    apply (rewrite at \<open>\<Sum>\<^sub>\<infinity>x. \<hole>\<close>  infsum_single) 
(*     apply (rewrite at \<open>\<Sum>\<^sub>\<infinity>z. \<hole>\<close> to \<open>if z\<in> UNIV
       then _   else 0\<close> infsum_single)
    apply (subst (3) infsum_single)
    thm sum_single *)
    by xxx
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

(* TODO name *)
lemma TODO_Cauchy[transfer_rule]:
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

lemma TODO_convergent[transfer_rule]:
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

lift_definition cq_operator_cases :: \<open>('cin \<Rightarrow> (('cin\<times>'qin) ell2,('cout\<times>'qout) ell2) kraus_map)
                              \<Rightarrow> (('cin\<times>'qin) ell2, ('cout\<times>'qout) ell2) kraus_map\<close> is
  \<open>\<lambda>(\<EE> :: 'cin \<Rightarrow> (('cin\<times>'qin) ell2, ('cout\<times>'qout) ell2) kraus_family).
   \<lambda>F. undefined\<close>


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
    sorry
  then show \<open>(\<lambda>cout. \<Sum>\<^sub>\<infinity>cin. f cin (cqin cin) cout) abs_summable_on UNIV\<close>
    unfolding abs_summable_on_Sigma_iff
    apply auto
    sorry
qed *)

definition cq_from_distrib :: \<open>'c distr \<Rightarrow> ('q ell2, 'q ell2) trace_class \<Rightarrow> ('c,'q) cq_operator\<close> where
  \<open>cq_from_distrib \<mu> \<rho> = mk_cq_operator (\<lambda>x. prob \<mu> x *\<^sub>R \<rho>)\<close>

(* lift_definition cq_from_distrib :: \<open>'c distr \<Rightarrow> ('q ell2, 'q ell2) trace_class \<Rightarrow> ('c,'q) cq_operator\<close> is
  \<open>\<lambda>(\<mu>::'c distr) (\<rho>::('q ell2, 'q ell2) trace_class) x. prob \<mu> x *\<^sub>R \<rho>\<close>
  by (intro Extra_Vector_Spaces.abs_summable_on_scaleR_left prob_abs_summable) *)

definition deterministic_cq :: \<open>'c \<Rightarrow> ('q ell2, 'q ell2) trace_class \<Rightarrow> ('c,'q) cq_operator\<close> where
  \<open>deterministic_cq c \<rho> = mk_cq_operator (\<lambda>d. of_bool (c=d) *\<^sub>R \<rho>)\<close>

(* lift_definition deterministic_cq :: \<open>'c \<Rightarrow> ('q ell2, 'q ell2) trace_class \<Rightarrow> ('c,'q) cq_operator\<close> is
  \<open>\<lambda>(x::'c) (\<rho>::('q ell2, 'q ell2) trace_class) y. of_bool (x=y) *\<^sub>R \<rho>\<close>
proof (rename_tac c \<rho>)
  fix c :: 'c and \<rho> :: \<open>('q ell2, 'q ell2) trace_class\<close>
  show \<open>(\<lambda>x. of_bool (c = x) *\<^sub>R \<rho>) abs_summable_on UNIV\<close>
    apply (rule summable_on_cong_neutral[where T=\<open>{c}\<close>, THEN iffD2])
    by auto
qed *)

lemma cq_from_distrib_point_distr: \<open>cq_from_distrib (point_distr x) \<rho> = deterministic_cq x \<rho>\<close>
  apply (simp add: cq_from_distrib_def deterministic_cq_def)
  by (metis (mono_tags, opaque_lifting) of_bool_eq_0_iff)
(*   
  apply (rule cq_operator_at_inject[THEN iffD1])
  by (auto simp add: cq_from_distrib.rep_eq deterministic_cq.rep_eq) *)

(* definition kraus_family_from_cq_kraus_map :: \<open>('cl1 \<Rightarrow> 'cl2 \<Rightarrow> ('qu1 ell2, 'qu2 ell2) kraus_family) \<Rightarrow> 
  (('cl1\<times>'qu1) ell2, ('cl2\<times>'qu2)) kraus_family\<close> where
\<open>xxx\<close> *)



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

end