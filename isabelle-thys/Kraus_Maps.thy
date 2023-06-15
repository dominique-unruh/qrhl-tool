theory Kraus_Maps
  imports Tensor_Product.Trace_Class Registers2.Missing_Bounded_Operators
begin

unbundle cblinfun_notation

type_synonym ('a,'b) kraus_family = \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> nat\<close>

lemma trace_norm_sandwich: \<open>trace_norm (sandwich e t) \<le> (norm e)^2 * trace_norm t\<close> if \<open>trace_class t\<close>
  apply (simp add: sandwich_apply)
  by (smt (z3) Groups.mult_ac(2) more_arith_simps(11) mult_left_mono norm_adj norm_ge_zero power2_eq_square that trace_class_comp_right trace_norm_comp_left trace_norm_comp_right)

lift_definition sandwich_tc :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> ('a::chilbert_space,'a) trace_class \<Rightarrow>\<^sub>C\<^sub>L ('b::chilbert_space,'b) trace_class\<close> is
  \<open>\<lambda>e t. sandwich e t\<close>
proof (intro relcomppI conjI)
  include lifting_syntax
  fix e :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  have *: \<open>trace_class (sandwich e *\<^sub>V from_trace_class t)\<close> for t
    using trace_class_from_trace_class trace_class_sandwich by blast
  define S where \<open>S e t = Abs_trace_class (sandwich e (from_trace_class t))\<close> for e :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and t :: \<open>('a,'a) trace_class\<close>
  show 1: \<open>(cr_trace_class ===> cr_trace_class) ((*\<^sub>V) (sandwich e)) (S e)\<close>
    by (auto intro!: rel_funI simp add: cr_trace_class_def S_def Abs_trace_class_inverse * )
  show \<open>bounded_clinear (S e)\<close>
    apply (rule bounded_clinearI[where K=\<open>(norm e)^2\<close>])
    apply (simp_all add: S_def
        plus_trace_class.rep_eq scaleC_trace_class.rep_eq 
        cblinfun.add_right cblinfun.scaleC_right
        plus_trace_class.abs_eq scaleC_trace_class.abs_eq norm_trace_class.abs_eq
        eq_onp_def * )
    using trace_norm_sandwich[where e=e, OF trace_class_from_trace_class]
    by (simp add: norm_trace_class.rep_eq ordered_field_class.sign_simps(33))
  show \<open>S e = S e\<close>
    by simp
  show \<open>(cr_trace_class ===> cr_trace_class)\<inverse>\<inverse> (S e) ((*\<^sub>V) (sandwich e))\<close>
    by (intro conversepI 1)
qed

lemma from_trace_class_sandwich_tc:
  \<open>from_trace_class (sandwich_tc e t) = sandwich e (from_trace_class t)\<close>
  apply transfer
  by (rule sandwich_apply)

lemma sandwich_tc_pos: \<open>sandwich_tc e t \<ge> 0\<close> if \<open>t \<ge> 0\<close>
  using that apply (transfer fixing: e)
  by (simp add: sandwich_pos)

definition \<open>kraus_family \<EE> \<longleftrightarrow> (\<exists>B. \<forall>F. finite F \<longrightarrow> norm (\<Sum>E\<in>F. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> B)\<close>
  for \<EE> :: \<open>(_::chilbert_space, _::chilbert_space) kraus_family\<close>
definition \<open>kraus_family_norm \<EE> = (SUP F\<in>Collect finite. norm (\<Sum>E\<in>F. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)))\<close>

definition \<open>kraus_family_map \<EE> \<rho> = (\<Sum>\<^sub>\<infinity>E. of_nat (\<EE> E) *\<^sub>C sandwich_tc E \<rho>)\<close>

lemma kraus_family_map_0[simp]: \<open>kraus_family_map 0 = 0\<close>
  by (auto intro!: ext simp: kraus_family_map_def)

definition \<open>kraus_equivalent \<EE> \<FF> \<longleftrightarrow> kraus_family \<EE> \<and> kraus_family \<FF> \<and> kraus_family_map \<EE> = kraus_family_map \<FF>\<close>

lemma kraus_equivalent_reflI: \<open>kraus_equivalent x x\<close> if \<open>kraus_family x\<close>
  using that by (simp add: kraus_equivalent_def)

lemma kraus_family_zero[simp]: \<open>kraus_family (\<lambda>_. 0)\<close>
  by (auto simp: kraus_family_def)

quotient_type (overloaded) ('a,'b) kraus_map = \<open>('a::chilbert_space, 'b::chilbert_space) kraus_family\<close> / partial: kraus_equivalent
  by (auto intro!: part_equivpI exI[of _ \<open>\<lambda>_. 0\<close>] sympI transpI simp: kraus_equivalent_def)

definition \<open>kraus_family_comp \<EE> \<FF> G = (if G=0 then 0 else \<Sum>(E,F)|(\<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F = G). \<EE> E * \<FF> F)\<close> 
\<comment> \<open>The lemma \<open>kraus_family_comp_finite\<close> below shows that we range over a finite set in the sum.\<close>
  for \<EE> \<FF> :: \<open>(_::chilbert_space, _::chilbert_space) kraus_family\<close>

definition kraus_family_of_op :: \<open>_ \<Rightarrow> (_::chilbert_space,_::chilbert_space) kraus_family\<close> where
  \<open>kraus_family_of_op E F = of_bool (E=F)\<close>

lemma kraus_family_kraus_family_of_op[simp]: \<open>kraus_family (kraus_family_of_op E)\<close>
proof -
  have \<open>(\<Sum>F\<in>M. kraus_family_of_op E F *\<^sub>C (F* o\<^sub>C\<^sub>L F)) = (if E\<in>M then E* o\<^sub>C\<^sub>L E else 0)\<close> if \<open>finite M\<close> for M
    apply (subst sum_single[where i=E])
    using that by (auto simp: kraus_family_of_op_def)
  then show ?thesis
    by (auto simp add: kraus_family_def)
qed

lemma kraus_family_of_op_norm[simp]:
  \<open>kraus_family_norm (kraus_family_of_op E) = (norm E)\<^sup>2\<close>
proof -
  have \<open>kraus_family_norm (kraus_family_of_op E) = 
      (\<Squnion>M\<in>Collect finite. norm (\<Sum>F\<in>M. of_bool (E=F) *\<^sub>C (F* o\<^sub>C\<^sub>L F)))\<close>
    by (simp add: kraus_family_norm_def kraus_family_of_op_def)
  also have \<open>\<dots> = (\<Squnion>M\<in>Collect finite. if E\<in>M then norm (E* o\<^sub>C\<^sub>L E) else 0)\<close>
  proof (rule SUP_cong, simp)
    fix M :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close> assume \<open>M \<in> Collect finite\<close>
    then have [simp]: \<open>finite M\<close> by simp
    show \<open>norm (\<Sum>F\<in>M. of_bool (E = F) *\<^sub>C (F* o\<^sub>C\<^sub>L F)) = (if E \<in> M then norm (E* o\<^sub>C\<^sub>L E) else 0)\<close>
      apply (subst sum_single[where i=E])
      by auto
  qed
  also have \<open>\<dots> = norm (E* o\<^sub>C\<^sub>L E)\<close>
    apply (rule cSup_eq_maximum)
    by auto
  also have \<open>\<dots> = (norm E)\<^sup>2\<close>
    by simp
  finally show ?thesis
    by -
qed

lift_definition kraus_map_of_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> ('a,'b) kraus_map\<close>
  is kraus_family_of_op
  by (simp add: kraus_equivalent_def)

lemma kraus_family_map_bounded:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>norm (kraus_family_map \<EE> \<rho>) \<le> kraus_family_norm \<EE> * norm \<rho>\<close>
  sorry

lemma kraus_family_map_plus_left:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_map \<EE> (x + y) = kraus_family_map \<EE> x + kraus_family_map \<EE> y\<close>
  sorry

lemma kraus_family_map_scaleC:
  shows \<open>kraus_family_map \<EE> (c *\<^sub>C x) = c *\<^sub>C kraus_family_map \<EE> x\<close>
  by (simp add: kraus_family_map_def cblinfun.scaleC_right mult.commute
      flip: infsum_scaleC_right)

lemma kraus_family_map_bounded_clinear:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>bounded_clinear (kraus_family_map \<EE>)\<close>
  apply (rule bounded_clinearI[where K=\<open>kraus_family_norm \<EE>\<close>])
    apply (auto intro!: kraus_family_map_plus_left kraus_family_map_scaleC assms
      mult.commute)
  using kraus_family_map_bounded[OF assms]
  by (simp add: mult.commute)

lemma kraus_family_norm_geq0:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_norm \<EE> \<ge> 0\<close>
  unfolding kraus_family_norm_def
  apply (rule cSUP_upper2[where x=\<open>{}\<close>])
  using assms
  by (simp_all add: bdd_above_def kraus_family_def)

lemma kraus_family_map_abs_summable:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>(\<lambda>E. of_nat (\<EE> E) *\<^sub>C sandwich_tc E \<rho>) abs_summable_on UNIV\<close>
(*
proof -
  wlog \<rho>_pos: \<open>\<rho> \<ge> 0\<close> generalizing \<rho>
  proof -
    have aux: \<open>trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )\<close> 
      for \<rho> :: \<open>('a, 'a) trace_class\<close> and E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      by (simp add: trace_class_comp_left trace_class_comp_right)
    obtain \<rho>1 \<rho>2 \<rho>3 \<rho>4 a1 a2 a3 a4 where \<rho>_decomp: \<open>\<rho> = a1 *\<^sub>C \<rho>1 + a2 *\<^sub>C \<rho>2 + a3 *\<^sub>C \<rho>3 + a4 *\<^sub>C \<rho>4\<close>
      and pos: \<open>\<rho>1 \<ge> 0\<close> \<open>\<rho>2 \<ge> 0\<close> \<open>\<rho>3 \<ge> 0\<close> \<open>\<rho>4 \<ge> 0\<close>
      by -
    have \<open>norm (of_nat (\<EE> x) *\<^sub>C Abs_trace_class (x o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L x* )) 
      \<le> norm (a1 *\<^sub>C of_nat (\<EE> x) *\<^sub>C Abs_trace_class (x o\<^sub>C\<^sub>L from_trace_class \<rho>1 o\<^sub>C\<^sub>L x* ))
      + norm (a2 *\<^sub>C of_nat (\<EE> x) *\<^sub>C Abs_trace_class (x o\<^sub>C\<^sub>L from_trace_class \<rho>2 o\<^sub>C\<^sub>L x* ))
      + norm (a3 *\<^sub>C of_nat (\<EE> x) *\<^sub>C Abs_trace_class (x o\<^sub>C\<^sub>L from_trace_class \<rho>3 o\<^sub>C\<^sub>L x* ))
      + norm (a4 *\<^sub>C of_nat (\<EE> x) *\<^sub>C Abs_trace_class (x o\<^sub>C\<^sub>L from_trace_class \<rho>4 o\<^sub>C\<^sub>L x* ))\<close> 
      (is \<open>_ \<le> ?S x\<close>) for x
      apply (auto intro!: mult_left_mono
          simp add: norm_trace_class.abs_eq eq_onp_def trace_class_plus trace_class_scaleC
          aux trace_class_adj \<rho>_decomp plus_trace_class.rep_eq scaleC_trace_class.rep_eq
          cblinfun_compose_add_right cblinfun_compose_add_left
          scaleC_left_commute[of _ \<open>of_nat (\<EE> x)\<close>]
          simp flip: ring_distribs
          simp del: scaleC_scaleC)
      by (smt (verit) local.aux trace_class_plus trace_class_scaleC trace_norm_scaleC trace_norm_triangle)
    then have *: \<open>norm (of_nat (\<EE> x) *\<^sub>C Abs_trace_class (x o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L x* )) 
      \<le> norm (?S x)\<close> for x
      by force
    show ?thesis
      apply (rule abs_summable_on_comparison_test[OF _ *])
      by (intro abs_summable_on_add abs_summable_norm abs_summable_on_scaleC_right hypothesis pos)
  qed
  have aux: \<open>trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )\<close> 
    for \<rho> :: \<open>('a, 'a) trace_class\<close> and E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    by (simp add: trace_class_comp_left trace_class_comp_right)
  define n\<rho> where \<open>n\<rho> = norm \<rho>\<close>
  have *: \<open>norm (of_nat (\<EE> E) *\<^sub>C Abs_trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* ))
      \<le> norm (norm \<rho> *\<^sub>C of_nat (\<EE> E) *\<^sub>C norm (E* o\<^sub>C\<^sub>L E))\<close> for E
  proof -
    have \<open>norm (Abs_trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )) =
          trace_norm (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )\<close>
      by (simp add: norm_trace_class.abs_eq eq_onp_def aux)
    also have \<open>\<dots> = trace (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )\<close>
      by (metis \<rho>_pos abs_op_def from_trace_class_0 less_eq_trace_class.rep_eq sandwich_apply sandwich_pos sqrt_op_unique trace_abs_op)
    also have \<open>\<dots> = trace (from_trace_class \<rho> o\<^sub>C\<^sub>L (E* o\<^sub>C\<^sub>L E))\<close>
      by (simp add: Misc.lift_cblinfun_comp(2) circularity_of_trace trace_class_comp_left)
    also have \<open>\<dots> \<le> trace_norm (from_trace_class \<rho>) * norm (E* o\<^sub>C\<^sub>L E)\<close>
      by (metis Extra_Ordered_Fields.sign_simps(5) calculation circularity_of_trace cmod_trace_times complex_of_real_cmod complex_of_real_mono complex_of_real_nn_iff norm_ge_zero trace_class_from_trace_class)
    also have \<open>\<dots> = norm \<rho> * norm (E* o\<^sub>C\<^sub>L E)\<close>
      by (simp add: norm_trace_class.rep_eq)
    finally show ?thesis
  sledgehammer
  by X (smt (verit, del_insts) Extra_Ordered_Fields.sign_simps(5) Extra_Ordered_Fields.sign_simps(6)
 \<open>complex_of_real (trace_norm (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )) = trace (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )\<close> 
\<open>norm (Abs_trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )) = trace_norm (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )\<close>
 \<open>trace (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* ) = trace (from_trace_class \<rho> o\<^sub>C\<^sub>L (E* o\<^sub>C\<^sub>L E))\<close> 
cmod_trace_times' mult_left_mono norm_AadjA norm_ge_zero 
norm_mult norm_of_nat norm_of_real norm_trace_class.rep_eq of_real_power trace_class_from_trace_class)
  try0
  by -
qed
  from assms obtain B where B: \<open>norm (\<Sum>E\<in>S. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> B\<close> if \<open>finite S\<close> for S
    by (auto simp: kraus_family_def)

  show ?thesis
    apply (rule abs_summable_on_comparison_test[OF _ *])
    apply (rule abs_summable_on_scaleC_right)
(* TODO: Impossible goal here. E* o E only bounded in Loewner order, not in norm *)
    apply (rule nonneg_bdd_above_summable_on, simp)
    apply (rule bdd_aboveI[where M=B])
    using B' apply safe
  by -



  show \<open>\<rho> \<ge> 0\<close>
  sorry
*)
  sorry

lemma kraus_family_map_summable:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>(\<lambda>E. of_nat (\<EE> E) *\<^sub>C sandwich_tc E \<rho>) summable_on UNIV\<close>
  apply (rule abs_summable_summable)
  unfolding sandwich_apply
  using assms by (rule kraus_family_map_abs_summable)

lemma kraus_family_map_bounded_tight:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_norm \<EE> = (\<Squnion>\<rho>. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close>
proof (rule antisym)
  from assms
  have bounded: \<open>norm (kraus_family_map \<EE> \<rho>) / norm \<rho> \<le> kraus_family_norm \<EE>\<close> for \<rho>
    apply (cases \<open>\<rho> = 0\<close>)
    by (simp_all add: kraus_family_norm_geq0 kraus_family_map_bounded linordered_field_class.pos_divide_le_eq)

  have aux1: \<open>0 \<le> (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C
            sandwich_tc E (Abs_trace_class (selfbutter \<psi>)))\<close> for \<psi> M
    by (auto intro!: sum_nonneg scaleC_nonneg_nonneg of_nat_0_le_iff Abs_trace_class_geq0I
        trace_class_sandwich sandwich_tc_pos)

  show \<open>(\<Squnion>\<rho>. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>) \<le> kraus_family_norm \<EE>\<close>
    apply (rule cSUP_least)
    using bounded by auto
  show \<open>kraus_family_norm \<EE> \<le> (\<Squnion>\<rho>. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close>
    unfolding kraus_family_norm_def
  proof (rule cSUP_least)
    show \<open>Collect finite \<noteq> {}\<close>
      by auto
    fix M :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
    assume \<open>M \<in> Collect finite\<close>
    then have [simp]: \<open>finite M\<close> by simp
    have \<open>norm (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) - \<epsilon> \<le> (\<Squnion>\<rho>. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close> 
      (is \<open>?lhs \<le> ?rhs\<close>) if \<open>\<epsilon> > 0\<close> for \<epsilon>
    proof (cases \<open>\<forall>\<psi>::'a. \<psi> = 0\<close>)
      case True
      then have *: \<open>(A::'a\<Rightarrow>\<^sub>C\<^sub>L'a) = 0\<close> for A
        apply (rule_tac cblinfun_eqI)
        by auto
      show ?thesis
        apply (rule cSUP_upper2[where x=0])
        apply (rule bdd_aboveI[where M=\<open>kraus_family_norm \<EE>\<close>])
        using bounded \<open>\<epsilon> > 0\<close> by (auto simp: *[of \<open>sum _ _\<close>])
    next
      case False
      then have [simp]: \<open>class.not_singleton TYPE('a)\<close>
        apply intro_classes by blast
      obtain \<psi> where \<open>?lhs \<le> \<psi> \<bullet>\<^sub>C ((\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) *\<^sub>V \<psi>)\<close> and \<open>norm \<psi> = 1\<close>
        apply atomize_elim
        apply (rule cblinfun_norm_approx_witness_cinner[internalize_sort' 'a])
        using \<open>\<epsilon> > 0\<close>
        by (auto intro!: chilbert_space_axioms sum_nonneg scaleC_nonneg_nonneg of_nat_0_le_iff positive_cblinfun_squareI[OF refl])
      then have \<open>?lhs \<le> \<psi> \<bullet>\<^sub>C ((\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) *\<^sub>V \<psi>)\<close> (* Just restating *)
        by simp
      also have \<open>\<dots> = trace ((\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) o\<^sub>C\<^sub>L selfbutter \<psi>)\<close>
        by (simp flip: trace_butterfly_comp')
      also have \<open>\<dots> = (\<Sum>E\<in>M. complex_of_nat (\<EE> E) * trace (E* o\<^sub>C\<^sub>L (E o\<^sub>C\<^sub>L selfbutter \<psi>)))\<close>
        by (simp add: trace_class_scaleC trace_class_comp_right cblinfun_compose_sum_left
            cblinfun_compose_assoc
            flip: trace_scaleC trace_sum)
      also have \<open>\<dots> = (\<Sum>E\<in>M. complex_of_nat (\<EE> E) * trace (sandwich E (selfbutter \<psi>)))\<close>
        by (simp add: trace_class_comp_right sandwich_apply flip: circularity_of_trace)
      also have \<open>\<dots> = trace (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (sandwich E (selfbutter \<psi>)))\<close>
        by (simp add: trace_class_scaleC trace_class_comp_right cblinfun_compose_assoc trace_class_sandwich
            flip: trace_scaleC trace_sum)
      also have \<open>\<dots> = trace_norm (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (sandwich E (selfbutter \<psi>)))\<close>
        by (simp_all add: sandwich_pos of_nat_0_le_iff scaleC_nonneg_nonneg sum_nonneg abs_op_id_on_pos
            flip: trace_abs_op)
      also have \<open>\<dots> = norm (\<Sum>E\<in>M.
             complex_of_nat (\<EE> E) *\<^sub>C sandwich_tc E (Abs_trace_class (selfbutter \<psi>)))\<close>
        by (simp add: norm_trace_class.rep_eq from_trace_class_sum scaleC_trace_class.rep_eq
            from_trace_class_sandwich_tc Abs_trace_class_inverse trace_class_sandwich)
      also have \<open>\<dots> \<le> norm (kraus_family_map \<EE> (Abs_trace_class (selfbutter \<psi>)))\<close>
        apply (rule complex_of_real_mono)
        unfolding kraus_family_map_def
        using aux1 apply (rule norm_cblinfun_mono_trace_class)
        apply (subst infsum_finite[symmetric], simp)
        apply (rule infsum_mono_neutral_traceclass)
        by (auto intro!: scaleC_nonneg_nonneg of_nat_0_le_iff
            Abs_trace_class_geq0I  
            kraus_family_map_summable \<open>kraus_family \<EE>\<close> sandwich_tc_pos)
      also have \<open>\<dots> = norm (kraus_family_map \<EE> (Abs_trace_class (selfbutter \<psi>))) / norm (Abs_trace_class (selfbutter \<psi>))\<close>
        by (simp add: norm_trace_class.abs_eq eq_onp_def trace_norm_butterfly \<open>norm \<psi> = 1\<close>)
      also have \<open>\<dots> \<le> ?rhs\<close>
        apply (rule complex_of_real_mono)
        apply (rule cSup_upper)
        apply simp
        apply (rule bdd_aboveI[where M=\<open>kraus_family_norm \<EE>\<close>])
        using bounded by auto
      finally show ?thesis
        using complex_of_real_mono_iff by blast
    qed
    then show \<open>norm (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> (\<Squnion>\<rho>. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close>
      by (smt (verit, ccfv_SIG) nice_ordered_field_class.field_le_epsilon)
  qed
qed


lemma
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>((\<lambda>F. norm (\<Sum>E\<in>F. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E))) \<longlongrightarrow> kraus_family_norm \<EE>) (finite_subsets_at_top UNIV)\<close>
  sorry

lemma kraus_family_norm_welldefined:
  assumes \<open>kraus_equivalent \<EE> \<FF>\<close>
  shows \<open>kraus_family_norm \<EE> = kraus_family_norm \<FF>\<close>
  using assms unfolding kraus_equivalent_def
  by (smt (z3) SUP_cong kraus_family_map_bounded_tight)

lift_definition kraus_map_norm :: \<open>('a::chilbert_space, 'b::chilbert_space) kraus_map \<Rightarrow> real\<close> is
  kraus_family_norm
  by (rule kraus_family_norm_welldefined)

lemma kraus_map_of_op_norm[simp]:
  \<open>kraus_map_norm (kraus_map_of_op E) = (norm E)\<^sup>2\<close>
  apply (transfer fixing: E)
  by simp

lemma kraus_family_comp_finite:
  assumes \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close> and \<open>G \<noteq> 0\<close>
  shows \<open>finite {(E, F). \<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F = G}\<close>
proof (rule ccontr)
  assume infinite: \<open>infinite {(E, F). \<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F = G}\<close>
  from assms obtain BE where BE: \<open>norm (\<Sum>E\<in>S. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> if \<open>finite S\<close> for S
    by (auto simp: kraus_family_def)
  then have \<open>BE \<ge> 0\<close>
    by force
  from assms obtain BF where BF: \<open>norm (\<Sum>F\<in>S. \<FF> F *\<^sub>C (F* o\<^sub>C\<^sub>L F)) \<le> BF\<close> if \<open>finite S\<close> for S
    by (auto simp: kraus_family_def)
  from infinite obtain S where [simp]: \<open>finite S\<close> and S_subset: \<open>S \<subseteq> {(E, F). \<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F = G}\<close>
    and S_size: \<open>card S > BE * BF / norm (G* o\<^sub>C\<^sub>L G)\<close>
    by (smt (verit, best) infinite_arbitrarily_large reals_Archimedean2)
  define SE SF where \<open>SE = fst ` S\<close> and \<open>SF = snd ` S\<close>
  have \<open>BE * BF < card S * norm (G* o\<^sub>C\<^sub>L G)\<close>
    by (meson S_size assms(3) linordered_field_class.pos_divide_less_eq op_square_nondegenerate zero_less_norm_iff)
  also have \<open>\<dots> = norm (\<Sum>(F,E)\<in>prod.swap ` S. G* o\<^sub>C\<^sub>L G)\<close>
    by (simp add: case_prod_beta sum_constant_scale card_image)
  also have \<open>\<dots> \<le> norm (\<Sum>(F,E)\<in>prod.swap ` S. of_nat (\<EE> E * \<FF> F) *\<^sub>C (G* o\<^sub>C\<^sub>L G))\<close>
  proof -
    have \<open>G* o\<^sub>C\<^sub>L G \<le> (of_nat (\<EE> E) * of_nat (\<FF> F)) *\<^sub>C (G* o\<^sub>C\<^sub>L G)\<close> if \<open>(E, F) \<in> S\<close> for E F
    proof -
      from that have geq1: \<open>\<EE> E \<ge> 1\<close> \<open>\<FF> F \<ge> 1\<close>
        using S_subset by auto
      have \<open>G* o\<^sub>C\<^sub>L G = 1 *\<^sub>C (G* o\<^sub>C\<^sub>L G)\<close>
        by simp
      also have \<open>\<dots> \<le> (of_nat (\<EE> E) * of_nat (\<FF> F)) *\<^sub>C (G* o\<^sub>C\<^sub>L G)\<close>
        apply (intro scaleC_right_mono)
        using geq1 apply (simp_all add: less_eq_complex_def positive_cblinfun_squareI[OF refl]
            real_of_nat_ge_one_iff
            del: One_nat_def flip: of_nat_mult)
        by (metis mult_le_mono nat_mult_1 )
      finally show ?thesis
        by -
    qed
    then show ?thesis
      by (auto intro!: norm_cblinfun_mono sum_nonneg positive_cblinfun_squareI[OF refl] sum_mono)
  qed
  also have \<open>\<dots> = norm (\<Sum>(F,E)\<in>prod.swap ` S. of_nat (\<EE> E * \<FF> F) *\<^sub>C ((E o\<^sub>C\<^sub>L F)* o\<^sub>C\<^sub>L (E o\<^sub>C\<^sub>L F)))\<close>
    apply (rule arg_cong[where f=norm])
    apply (rule sum.cong, rule refl)
    using S_subset by auto
  also have \<open>\<dots> \<le> norm (\<Sum>(F,E)\<in>SF \<times> SE. of_nat (\<EE> E * \<FF> F) *\<^sub>C ((E o\<^sub>C\<^sub>L F)* o\<^sub>C\<^sub>L (E o\<^sub>C\<^sub>L F)))\<close>
    apply (auto intro!: norm_cblinfun_mono sum_nonneg scaleC_nonneg_nonneg mult_nonneg_nonneg
        of_nat_0_le_iff positive_cblinfun_squareI[OF refl] sum_mono2
        simp: SE_def[abs_def] SF_def[abs_def]
        simp del: adj_cblinfun_compose)
    by force+
  also have \<open>\<dots> = norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C sandwich (F*)
                             (\<Sum>E\<in>SE. of_nat (\<EE> E) *\<^sub>C ((E* o\<^sub>C\<^sub>L E))))\<close>
    by (simp add: sum.cartesian_product scaleC_sum_right 
        sandwich_apply Extra_Ordered_Fields.sign_simps(5)
        cblinfun_compose_assoc cblinfun_compose_sum_right cblinfun_compose_sum_left)
  also have \<open>\<dots> \<le> norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C sandwich (F*) (BE *\<^sub>C id_cblinfun))\<close>
    by (auto intro!: norm_cblinfun_mono sum_nonneg scaleC_nonneg_nonneg of_nat_0_le_iff
        sum_mono sandwich_pos positive_cblinfun_squareI[OF refl] scaleC_left_mono
        sandwich_mono less_eq_scaled_id_norm BE  finite_imageI
        simp: SE_def[abs_def] SF_def[abs_def] sum_adj)
  also have \<open>\<dots> = BE * norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C F* o\<^sub>C\<^sub>L F)\<close>
    by (simp flip: scaleC_scaleC scaleC_sum_right 
        add: sandwich_apply \<open>BE \<ge> 0\<close> scaleC_left_commute)
  also have \<open>\<dots> \<le> BE * BF\<close>
    by (auto intro!: mult_left_mono \<open>BE \<ge> 0\<close> BF finite_imageI simp: SF_def[abs_def])
  finally show False
    by simp
qed

lemma kraus_family_kraus_family_comp: 
  assumes \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family (kraus_family_comp \<EE> \<FF>)\<close>
proof -
  from assms obtain BE where BE: \<open>norm (\<Sum>E\<in>S. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> if \<open>finite S\<close> for S
    by (auto simp: kraus_family_def)
  then have \<open>BE \<ge> 0\<close>
    by force
  from assms obtain BF where BF: \<open>norm (\<Sum>F\<in>S. \<FF> F *\<^sub>C (F* o\<^sub>C\<^sub>L F)) \<le> BF\<close> if \<open>finite S\<close> for S
    by (auto simp: kraus_family_def)
  have \<open>norm (\<Sum>G\<in>S. kraus_family_comp \<EE> \<FF> G *\<^sub>C (G* o\<^sub>C\<^sub>L G)) \<le> BE * BF\<close> if \<open>finite S\<close> for S
  proof -
    define EF_G EF_S where \<open>EF_G G = {(E, F). \<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F = G}\<close>
      and \<open>EF_S = {(E, F). \<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F \<in> S-{0}}\<close> for G
    define SE SF where \<open>SE = fst ` EF_S\<close> and \<open>SF = snd ` EF_S\<close>
    have finite_EF: \<open>finite (EF_G G)\<close> if \<open>G \<noteq> 0\<close> for G :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      by (unfold EF_G_def, intro kraus_family_comp_finite assms that)
    then have finite_EFS: \<open>finite EF_S\<close>
      apply (subst asm_rl[of \<open>EF_S = (\<Union>G\<in>S-{0}. EF_G G)\<close>])
       apply (auto simp: EF_S_def EF_G_def)[1]
      by (auto intro!: finite_UN_I \<open>finite S\<close> finite_EF finite_Diff)
    have \<open>norm (\<Sum>G\<in>S. kraus_family_comp \<EE> \<FF> G *\<^sub>C (G* o\<^sub>C\<^sub>L G))
      = norm (\<Sum>G\<in>S-{0}. kraus_family_comp \<EE> \<FF> G *\<^sub>C (G* o\<^sub>C\<^sub>L G))\<close>
      by (auto intro!: arg_cong[where f=norm] sum.mono_neutral_right \<open>finite S\<close>)
    also have \<open>\<dots> = norm (\<Sum>G\<in>S-{0}. (\<Sum>(E, F)\<in>EF_G G. of_nat (\<EE> E * \<FF> F) *\<^sub>C (G* o\<^sub>C\<^sub>L G)))\<close>
      by (simp add: kraus_family_comp_def case_prod_beta scaleC_sum_left EF_G_def)
    also have \<open>\<dots> = norm (\<Sum>(G,E,F)\<in>(SIGMA G:S-{0}. EF_G G). of_nat (\<EE> E * \<FF> F) *\<^sub>C (G* o\<^sub>C\<^sub>L G))\<close>
      apply (subst sum.Sigma)
      using that finite_EF by auto
    also have \<open>\<dots> = norm (\<Sum>(G,E,F)\<in>(\<lambda>(F,E). (E o\<^sub>C\<^sub>L F, E, F)) ` prod.swap ` EF_S. 
                                             of_nat (\<EE> E * \<FF> F) *\<^sub>C (G* o\<^sub>C\<^sub>L G))\<close>
      apply (rule arg_cong[where f=norm])
      apply (rule sum.cong)
      by (auto simp: EF_S_def EF_G_def)
    also have \<open>\<dots> = norm (\<Sum>(F,E)\<in>prod.swap ` EF_S. 
                  of_nat (\<EE> E * \<FF> F) *\<^sub>C ((E o\<^sub>C\<^sub>L F)* o\<^sub>C\<^sub>L (E o\<^sub>C\<^sub>L F)))\<close>
      apply (subst sum.reindex)
      by (auto intro!: inj_onI simp: case_prod_beta)
    also have \<open>\<dots> \<le> norm (\<Sum>(F,E)\<in>SF \<times> SE. 
                  of_nat (\<EE> E * \<FF> F) *\<^sub>C ((E o\<^sub>C\<^sub>L F)* o\<^sub>C\<^sub>L (E o\<^sub>C\<^sub>L F)))\<close>
      apply (auto intro!: norm_cblinfun_mono sum_nonneg scaleC_nonneg_nonneg mult_nonneg_nonneg
          of_nat_0_le_iff positive_cblinfun_squareI[OF refl] sum_mono2 finite_cartesian_product
          finite_EFS finite_imageI
          simp: SE_def[abs_def] SF_def[abs_def]
          simp del: adj_cblinfun_compose)
      by force+
    also have \<open>\<dots> = norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C sandwich (F*)
                             (\<Sum>E\<in>SE. of_nat (\<EE> E) *\<^sub>C ((E* o\<^sub>C\<^sub>L E))))\<close>
      by (simp add: case_prod_beta sum.cartesian_product scaleC_sum_right scaleC_scaleC
          sandwich_apply Extra_Ordered_Fields.sign_simps(5)
          cblinfun_compose_assoc cblinfun_compose_sum_right cblinfun_compose_sum_left)
    also have \<open>\<dots> \<le> norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C sandwich (F*) (BE *\<^sub>C id_cblinfun))\<close>
      by (auto intro!: norm_cblinfun_mono sum_nonneg scaleC_nonneg_nonneg of_nat_0_le_iff
          sum_mono sandwich_pos positive_cblinfun_squareI[OF refl] scaleC_left_mono
          sandwich_mono less_eq_scaled_id_norm BE finite_EFS finite_imageI
          simp: SE_def[abs_def] SF_def[abs_def] sum_adj)
    also have \<open>\<dots> = BE * norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C F* o\<^sub>C\<^sub>L F)\<close>
      by (simp flip: scaleC_scaleC scaleC_sum_right 
          add: sandwich_apply \<open>BE \<ge> 0\<close> scaleC_left_commute)
    also have \<open>\<dots> \<le> BE * BF\<close>
      by (auto intro!: mult_left_mono \<open>BE \<ge> 0\<close> BF finite_imageI finite_EFS
          simp: SF_def[abs_def])
    finally show ?thesis
      by -
  qed
  then show ?thesis
    by (auto simp: kraus_family_def)
qed

lemma kraus_family_comp_apply:
  assumes \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) = kraus_family_map \<EE> \<circ> kraus_family_map \<FF>\<close>
  sorry

lift_definition kraus_map_comp :: \<open>('a::chilbert_space,'b::chilbert_space) kraus_map
                                \<Rightarrow> ('c::chilbert_space,'a) kraus_map \<Rightarrow> ('c,'b) kraus_map\<close>
  is kraus_family_comp
  by (auto intro!: kraus_family_kraus_family_comp
      simp add: kraus_equivalent_def kraus_family_comp_apply)


definition \<open>kraus_map_id = kraus_map_of_op id_cblinfun\<close>

lemma kraus_family_plus:
  assumes \<open>kraus_family \<EE>\<close>
  assumes \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family (\<lambda>E. \<EE> E + \<FF> E)\<close>
proof -
  from assms obtain BE where BE: \<open>norm (\<Sum>E\<in>S. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> if \<open>finite S\<close> for S
    by (auto simp: kraus_family_def)
  moreover
  from assms obtain BF where BF: \<open>norm (\<Sum>F\<in>S. \<FF> F *\<^sub>C (F* o\<^sub>C\<^sub>L F)) \<le> BF\<close> if \<open>finite S\<close> for S
    by (auto simp: kraus_family_def)
  ultimately  have \<open>norm (\<Sum>E\<in>S. (\<lambda>E. \<EE> E + \<FF> E) E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> BE + BF\<close> if \<open>finite S\<close> for S
    by (simp add: scaleC_add_left sum.distrib norm_triangle_mono that)
  then show ?thesis
    by (auto simp: kraus_family_def)
qed



lemma kraus_family_map_plus:
  assumes \<open>kraus_family \<EE>\<close>
  assumes \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family_map (\<lambda>E. \<EE> E + \<FF> E) \<rho> = kraus_family_map \<EE> \<rho> + kraus_family_map \<FF> \<rho>\<close>
proof -
  have \<open>kraus_family_map (\<lambda>E. \<EE> E + \<FF> E) \<rho> 
      = (\<Sum>\<^sub>\<infinity>E. \<EE> E *\<^sub>C sandwich_tc E \<rho> + \<FF> E *\<^sub>C sandwich_tc E \<rho>)\<close>
    by (simp add: kraus_family_map_def scaleC_add_left sum.distrib)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E. \<EE> E *\<^sub>C sandwich_tc E \<rho>) + (\<Sum>\<^sub>\<infinity>E. \<FF> E *\<^sub>C sandwich_tc E \<rho>)\<close>
   apply (rule infsum_add)
   using assms kraus_family_map_summable by auto
  also have \<open>\<dots> = kraus_family_map \<EE> \<rho> + kraus_family_map \<FF> \<rho>\<close>
    by (simp add: kraus_family_map_def)
  finally show ?thesis
    by -
qed

definition \<open>kraus_family_scale r \<EE> E = (if r \<le> 0 then 0 else \<EE> (E /\<^sub>R sqrt r))\<close>

lemma kraus_family_kraus_family_scale:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family (kraus_family_scale r \<EE>)\<close>
  sorry

lemma sandwich_scaleC_left: \<open>sandwich (c *\<^sub>C e) = (cmod c)^2 *\<^sub>C sandwich e\<close>
  by (auto intro!: cblinfun_eqI simp: sandwich_apply cnj_x_x abs_complex_def)

lemma sandwich_scaleR_left: \<open>sandwich (r *\<^sub>R e) = r^2 *\<^sub>R sandwich e\<close>
  by (simp add: scaleR_scaleC sandwich_scaleC_left flip: of_real_power)

lemma sandwich_tc_scaleC_left: \<open>sandwich_tc (c *\<^sub>C e) = (cmod c)^2 *\<^sub>C sandwich_tc e\<close>
  apply (rule cblinfun_eqI)
  apply (rule from_trace_class_inject[THEN iffD1])
  by (simp add: from_trace_class_sandwich_tc scaleC_trace_class.rep_eq
      sandwich_scaleC_left)

lemma sandwich_tc_scaleR_left: \<open>sandwich_tc (r *\<^sub>R e) = r^2 *\<^sub>R sandwich_tc e\<close>
  by (simp add: scaleR_scaleC sandwich_tc_scaleC_left flip: of_real_power)

lemma scaleC_scaleR_commute: \<open>a *\<^sub>C b *\<^sub>R x = b *\<^sub>R a *\<^sub>C x\<close> for x :: \<open>_::complex_normed_vector\<close>
  by (simp add: scaleR_scaleC scaleC_left_commute)

lemma kraus_family_scale_map:
  assumes \<open>r \<ge> 0\<close>
  shows \<open>kraus_family_map (kraus_family_scale r \<EE>) \<rho> = r *\<^sub>R kraus_family_map \<EE> \<rho>\<close>
proof (cases \<open>r \<le> 0\<close>)
  case True
  with assms show ?thesis
    by (simp add: kraus_family_map_def kraus_family_scale_def)
next
  case False
  then have \<open>r > 0\<close>
    by simp
  then have \<open>kraus_family_map (kraus_family_scale r \<EE>) \<rho>
    = infsum ((\<lambda>E. \<EE> E *\<^sub>C (sandwich_tc (sqrt r *\<^sub>R E) *\<^sub>V \<rho>)) \<circ> (\<lambda>E. E /\<^sub>R sqrt r)) UNIV\<close>
    by (simp add: kraus_family_map_def kraus_family_scale_def o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>range (\<lambda>x. x /\<^sub>R sqrt r). \<EE> E *\<^sub>C (sandwich_tc (sqrt r *\<^sub>R E) *\<^sub>V \<rho>))\<close>
    apply (subst infsum_reindex[symmetric])
    using \<open>r > 0\<close> by (auto intro!: real_vector.injective_scale)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E. \<EE> E *\<^sub>C (sandwich_tc (sqrt r *\<^sub>R E) *\<^sub>V \<rho>))\<close>
    apply (rule arg_cong[where y=UNIV])
    by (metis False divideR_right dual_order.refl real_sqrt_le_0_iff surj_def)
  also have \<open>\<dots> =  r *\<^sub>R (\<Sum>\<^sub>\<infinity>E. \<EE> E *\<^sub>C (sandwich_tc E \<rho>))\<close>
    using \<open>r > 0\<close>
    by (simp add: sandwich_tc_scaleR_left cblinfun.scaleR_left scaleC_scaleR_commute infsum_scaleR_right)
  also have \<open>\<dots> = r *\<^sub>R kraus_family_map \<EE> \<rho>\<close>
    by (simp add: kraus_family_map_def)
  finally show ?thesis
    by -
qed

lemma kraus_family_scale_neg: \<open>kraus_family_scale r = (\<lambda>_. 0)\<close> if \<open>r \<le> 0\<close>
  using that by (auto intro!: ext simp add: kraus_family_scale_def)


instantiation kraus_map :: (chilbert_space, chilbert_space) \<open>{zero,plus,scaleR}\<close> begin
lift_definition zero_kraus_map :: \<open>('a,'b) kraus_map\<close> is \<open>\<lambda>_. 0::nat\<close>
  by (simp add: kraus_equivalent_def)
lift_definition plus_kraus_map :: \<open>('a,'b) kraus_map \<Rightarrow> ('a,'b) kraus_map \<Rightarrow> ('a,'b) kraus_map\<close> is
  \<open>\<lambda>a b x. a x + b x\<close>
  by (auto intro!: kraus_family_plus simp add: kraus_equivalent_def kraus_family_map_plus)
lift_definition scaleR_kraus_map :: \<open>real \<Rightarrow> ('a,'b) kraus_map \<Rightarrow> ('a,'b) kraus_map\<close> is
  kraus_family_scale
proof (unfold kraus_equivalent_def, intro conjI kraus_family_kraus_family_scale)
  fix r :: real and \<EE> \<FF> :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> nat\<close>
  assume \<open>kraus_family \<EE> \<and> kraus_family \<FF> \<and> kraus_family_map \<EE> = kraus_family_map \<FF>\<close>
  then show \<open>kraus_family_map (kraus_family_scale r \<EE>) = kraus_family_map (kraus_family_scale r \<FF>)\<close>
    apply (cases \<open>r < 0\<close>)
    by (auto intro!: ext kraus_family_kraus_family_scale 
        simp add: kraus_family_scale_neg kraus_equivalent_def kraus_family_scale_map)
qed auto
instance..
end

instantiation kraus_map :: (chilbert_space, chilbert_space) comm_monoid_add begin
instance
proof intro_classes
  fix a b c :: \<open>('a, 'b) kraus_map\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer
    apply (auto intro!: ext kraus_family_plus simp add: kraus_equivalent_def)
    apply (subst kraus_family_map_plus)
    apply (auto intro!: kraus_family_plus simp add: kraus_family_map_plus)
    apply (subst kraus_family_map_plus)
    by (auto intro!: kraus_family_plus simp add: kraus_family_map_plus)
  show \<open>a + b = b + a\<close>
    apply transfer
    by (auto intro!: ext kraus_family_plus simp add: kraus_equivalent_def kraus_family_map_plus)
  show \<open>0 + a = a\<close>
    apply transfer
    by (auto intro!: ext kraus_family_plus simp add: kraus_equivalent_def)
qed
end


lift_definition kraus_map_apply :: \<open>('a::chilbert_space,'b::chilbert_space) kraus_map \<Rightarrow> ('a,'a) trace_class \<Rightarrow>\<^sub>C\<^sub>L ('b,'b) trace_class\<close> is
  \<open>kraus_family_map\<close>
  by (auto simp: kraus_equivalent_def kraus_family_map_bounded_clinear)

lemma kraus_family_rep_kraus_map[simp]: \<open>kraus_family (rep_kraus_map \<EE>)\<close>
  using Quotient_rep_reflp[OF Quotient_kraus_map]
  by (auto simp add: kraus_equivalent_def)

lemma kraus_map_scaleR:
  assumes \<open>r \<ge> 0\<close>
  shows \<open>kraus_map_apply (r *\<^sub>R \<EE>) = r *\<^sub>R kraus_map_apply \<EE>\<close>
proof (rule cblinfun_eqI)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  have \<open>kraus_map_apply (r *\<^sub>R \<EE>) \<rho> = CBlinfun (kraus_family_map (kraus_family_scale r (rep_kraus_map \<EE>))) *\<^sub>V \<rho>\<close>
    by (simp add: scaleR_kraus_map_def kraus_map_apply.abs_eq kraus_equivalent_reflI kraus_family_kraus_family_scale)
  also have \<open>\<dots> = kraus_family_map (kraus_family_scale r (rep_kraus_map \<EE>)) \<rho>\<close>
    apply (subst CBlinfun_inverse)
    by (auto intro!: kraus_family_map_bounded_clinear kraus_family_kraus_family_scale)
  also have \<open>\<dots> = r *\<^sub>R kraus_family_map (rep_kraus_map \<EE>) \<rho>\<close>
    by (simp add: kraus_family_scale_map assms)
  also have \<open>\<dots> = (r *\<^sub>R kraus_map_apply \<EE>) \<rho>\<close>
    by (simp flip: kraus_map_apply.rep_eq add: cblinfun.scaleR_left)
  finally show \<open>kraus_map_apply (r *\<^sub>R \<EE>) *\<^sub>V \<rho> = r *\<^sub>R kraus_map_apply \<EE> *\<^sub>V \<rho>\<close>
    by -
qed

lemma kraus_map_scaleR_neg:
  assumes \<open>r \<le> 0\<close>
  shows \<open>kraus_map_apply (r *\<^sub>R \<EE>) = 0\<close>
proof (rule cblinfun_eqI)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  have \<open>kraus_map_apply (r *\<^sub>R \<EE>) \<rho> = CBlinfun (kraus_family_map (kraus_family_scale r (rep_kraus_map \<EE>))) *\<^sub>V \<rho>\<close>
    by (simp add: scaleR_kraus_map_def kraus_map_apply.abs_eq kraus_equivalent_reflI kraus_family_kraus_family_scale)
  also have \<open>\<dots> = kraus_family_map (kraus_family_scale r (rep_kraus_map \<EE>)) \<rho>\<close>
    apply (subst CBlinfun_inverse)
    by (auto intro!: kraus_family_map_bounded_clinear kraus_family_kraus_family_scale)
  also have \<open>\<dots> = kraus_family_map 0 \<rho>\<close>
    by (simp add: kraus_family_scale_neg assms)
  also have \<open>\<dots> = 0 *\<^sub>V \<rho>\<close>
    by simp
  finally show \<open>kraus_map_apply (r *\<^sub>R \<EE>) *\<^sub>V \<rho> = 0 *\<^sub>V \<rho>\<close>
    by -
qed

end
