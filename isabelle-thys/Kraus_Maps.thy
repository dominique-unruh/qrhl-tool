theory Kraus_Maps
  imports Tensor_Product.Trace_Class Registers2.Missing_Bounded_Operators Wlog.Wlog "HOL-Library.Rewrite"
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

lemma sandwich_tc_apply:
  \<open>sandwich_tc e t = Abs_trace_class (sandwich e (from_trace_class t))\<close>
  using from_trace_class_sandwich_tc[of e t]
  by (metis from_trace_class_inverse)

lemma norm_sandwich_tc: \<open>norm (sandwich_tc e t) \<le> (norm e)^2 * norm t\<close>
  by (simp add: norm_trace_class.rep_eq from_trace_class_sandwich_tc trace_norm_sandwich)

lemma sandwich_tc_pos: \<open>sandwich_tc e t \<ge> 0\<close> if \<open>t \<ge> 0\<close>
  using that apply (transfer fixing: e)
  by (simp add: sandwich_pos)

definition \<open>kraus_family \<EE> \<longleftrightarrow> (\<exists>B. \<forall>F. finite F \<longrightarrow> norm (\<Sum>E\<in>F. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> B)\<close>
  for \<EE> :: \<open>(_::chilbert_space, _::chilbert_space) kraus_family\<close>
definition \<open>kraus_family_norm \<EE> = (SUP F\<in>Collect finite. norm (\<Sum>E\<in>F. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)))\<close>

lemma kraus_family_norm_geq0:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_norm \<EE> \<ge> 0\<close>
  unfolding kraus_family_norm_def
  apply (rule cSUP_upper2[where x=\<open>{}\<close>])
  using assms
  by (simp_all add: bdd_above_def kraus_family_def)

lemma kraus_family_sums_bounded_by_norm:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>norm (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> kraus_family_norm \<EE>\<close>
proof (cases \<open>finite M\<close>)
  case True
  then show ?thesis
    using assms 
    unfolding kraus_family_def kraus_family_norm_def
    apply (rule_tac cSup_upper)
     apply (rule image_eqI)
    by auto
next
  case False
  then show ?thesis
    by (simp add: kraus_family_norm_geq0 assms)
qed


definition \<open>kraus_family_map \<EE> \<rho> = (\<Sum>\<^sub>\<infinity>E. of_nat (\<EE> E) *\<^sub>C sandwich_tc E \<rho>)\<close>

lemma kraus_family_map_0[simp]: \<open>kraus_family_map 0 = 0\<close>
  by (auto intro!: ext simp: kraus_family_map_def)

definition \<open>kraus_equivalent \<EE> \<FF> \<longleftrightarrow> kraus_family \<EE> \<and> kraus_family \<FF> \<and> kraus_family_map \<EE> = kraus_family_map \<FF>\<close>

lemma kraus_equivalent_reflI: \<open>kraus_equivalent x x\<close> if \<open>kraus_family x\<close>
  using that by (simp add: kraus_equivalent_def)

lemma kraus_family_zero[simp]: \<open>kraus_family (\<lambda>_. 0)\<close>
  by (auto simp: kraus_family_def)
lemma kraus_family_zero'[simp]: \<open>kraus_family 0\<close>
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

lift_definition trace_tc :: \<open>('a::chilbert_space, 'a) trace_class \<Rightarrow> complex\<close> is trace.

lemma trace_tc_plus: \<open>trace_tc (a + b) = trace_tc a + trace_tc b\<close>
  apply transfer by (simp add: trace_plus)

lemma trace_tc_scaleC: \<open>trace_tc (c *\<^sub>C a) = c *\<^sub>C trace_tc a\<close>
  apply transfer by (simp add: trace_scaleC)

lemma trace_tc_norm: \<open>norm (trace_tc a) \<le> norm a\<close>
  apply transfer by auto

lemma bounded_clinear_trace_tc[bounded_clinear, simp]: \<open>bounded_clinear trace_tc\<close>
  apply (rule bounded_clinearI[where K=1])
  by (auto simp: trace_tc_scaleC trace_tc_plus intro!: trace_tc_norm)

lemma kraus_family_map_scaleC:
  shows \<open>kraus_family_map \<EE> (c *\<^sub>C x) = c *\<^sub>C kraus_family_map \<EE> x\<close>
  by (simp add: kraus_family_map_def cblinfun.scaleC_right mult.commute
      flip: infsum_scaleC_right)

lemma trace_norm_pos: \<open>trace_norm A = trace A\<close> if \<open>A \<ge> 0\<close>
  by (metis abs_op_id_on_pos that trace_abs_op)

lemma norm_tc_pos: \<open>norm A = trace_tc A\<close> if \<open>A \<ge> 0\<close>
   using that apply transfer by (simp add: trace_norm_pos)

lemma from_trace_class_pos: \<open>from_trace_class A \<ge> 0 \<longleftrightarrow> A \<ge> 0\<close>
  by (simp add: less_eq_trace_class.rep_eq)

lemma infsum_tc_norm_bounded_abs_summable:
  fixes A :: \<open>'a \<Rightarrow> ('b::chilbert_space, 'b::chilbert_space) trace_class\<close>
  assumes pos: \<open>\<And>x. x \<in> M \<Longrightarrow> A x \<ge> 0\<close>
  assumes bound_B: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> M \<Longrightarrow> norm (\<Sum>x\<in>F. A x) \<le> B\<close>
  shows \<open>A abs_summable_on M\<close>
proof -
  have \<open>(\<Sum>x\<in>F. norm (A x)) = norm (\<Sum>x\<in>F. A x)\<close> if \<open>F \<subseteq> M\<close> for F
  proof -
    have \<open>complex_of_real (\<Sum>x\<in>F. norm (A x)) = (\<Sum>x\<in>F. complex_of_real (trace_norm (from_trace_class (A x))))\<close>
      by (simp add: norm_trace_class.rep_eq trace_norm_pos)
    also have \<open>\<dots> = (\<Sum>x\<in>F. trace (from_trace_class (A x)))\<close>
      using that pos by (auto intro!: sum.cong simp add: trace_norm_pos less_eq_trace_class.rep_eq)
    also have \<open>\<dots> = trace (from_trace_class (\<Sum>x\<in>F. A x))\<close>
      by (simp add: from_trace_class_sum trace_sum)
    also have \<open>\<dots> = norm (\<Sum>x\<in>F. A x)\<close>
      by (smt (verit, ccfv_threshold) calculation norm_of_real norm_trace_class.rep_eq sum_norm_le trace_leq_trace_norm)
    finally show ?thesis
      using of_real_hom.injectivity by blast
  qed
  with bound_B have bound_B': \<open>(\<Sum>x\<in>F. norm (A x)) \<le> B\<close> if \<open>finite F\<close> and \<open>F \<subseteq> M\<close> for F
    by (metis that(1) that(2))
  then show \<open>A abs_summable_on M\<close>
    apply (rule_tac nonneg_bdd_above_summable_on)
    by (auto intro!: bdd_aboveI)
qed

lemma abs_op_geq: \<open>abs_op a \<ge> a\<close> if [simp]: \<open>a* = a\<close>
proof -
  define A P where \<open>A = abs_op a\<close> and \<open>P = Proj (kernel (A + a))\<close>
  have [simp]: \<open>A \<ge> 0\<close>
    by (simp add: A_def)
  then have [simp]: \<open>A* = A\<close>
    using positive_hermitianI by fastforce
  have aa_AA: \<open>a o\<^sub>C\<^sub>L a = A o\<^sub>C\<^sub>L A\<close>
    by (metis A_def \<open>A* = A\<close> abs_op_square that)
  have [simp]: \<open>P* = P\<close>
    by (simp add: P_def adj_Proj)
  have Aa_aA: \<open>A o\<^sub>C\<^sub>L a = a o\<^sub>C\<^sub>L A\<close>
    by (metis (full_types) A_def lift_cblinfun_comp(2) abs_op_def positive_cblinfun_squareI sqrt_op_commute that)

  have \<open>(A-a) \<psi> \<bullet>\<^sub>C (A+a) \<phi> = 0\<close> for \<phi> \<psi>
    by (simp add: adj_minus that \<open>A* = A\<close> aa_AA Aa_aA cblinfun_compose_add_right cblinfun_compose_minus_left
        flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
  then have \<open>(A-a) \<psi> \<in> space_as_set (kernel (A+a))\<close> for \<psi>
    by (metis \<open>A* = A\<close> adj_plus call_zero_iff cinner_adj_left kernel_memberI that)
  then have P_fix: \<open>P o\<^sub>C\<^sub>L (A-a) = (A-a)\<close>
    by (simp add: P_def Proj_fixes_image cblinfun_eqI)
  then have \<open>P o\<^sub>C\<^sub>L (A-a) o\<^sub>C\<^sub>L P = (A-a) o\<^sub>C\<^sub>L P\<close>
    by simp
  also have \<open>\<dots> = (P o\<^sub>C\<^sub>L (A-a))*\<close>
    by (simp add: adj_minus \<open>A* = A\<close> that \<open>P* = P\<close>)
  also have \<open>\<dots> = (A-a)*\<close>
    by (simp add: P_fix)
  also have \<open>\<dots> = A-a\<close>
    by (simp add: \<open>A* = A\<close> that adj_minus)
  finally have 1: \<open>P o\<^sub>C\<^sub>L (A - a) o\<^sub>C\<^sub>L P = A - a\<close>
    by -
  have 2: \<open>P o\<^sub>C\<^sub>L (A + a) o\<^sub>C\<^sub>L P = 0\<close>
    by (simp add: P_def cblinfun_compose_assoc)
  have \<open>A - a = P o\<^sub>C\<^sub>L (A - a) o\<^sub>C\<^sub>L P + P o\<^sub>C\<^sub>L (A + a) o\<^sub>C\<^sub>L P\<close>
    by (simp add: 1 2)
  also have \<open>\<dots> = sandwich P (2 *\<^sub>C A)\<close>
    by (simp add: sandwich_apply cblinfun_compose_minus_left cblinfun_compose_minus_right
        cblinfun_compose_add_left cblinfun_compose_add_right scaleC_2 \<open>P* = P\<close>) 
  also have \<open>\<dots> \<ge> 0\<close>
    by (auto intro!: sandwich_pos scaleC_nonneg_nonneg simp: less_eq_complex_def)
  finally show \<open>A \<ge> a\<close>
    by auto
qed

lemma abs_op_geq_neq: \<open>abs_op a \<ge> - a\<close> if \<open>a* = a\<close>
  by (metis abs_op_geq abs_op_uminus adj_uminus that)

lemma trace_norm_uminus[simp]: \<open>trace_norm (-a) = trace_norm a\<close>
  by (metis abs_op_uminus of_real_eq_iff trace_abs_op)

(* TODO: remove [simp] from trace_class_uminus *)
lemma trace_class_uminus_iff[simp]: \<open>trace_class (-a) =  trace_class a\<close>
  by (auto simp add: trace_class_def)
lemma trace_norm_triangle_minus: 
  fixes a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes [simp]: \<open>trace_class a\<close> \<open>trace_class b\<close>
  shows \<open>trace_norm (a - b) \<le> trace_norm a + trace_norm b\<close>
  using trace_norm_triangle[of a \<open>-b\<close>]
  by auto

lemma trace_norm_abs_op[simp]: \<open>trace_norm (abs_op t) = trace_norm t\<close>
  by (simp add: trace_norm_def)

lemma 
  fixes t :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space\<close>
  shows cblinfun_decomp_4pos: \<open>
             \<exists>t1 t2 t3 t4.
              t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4
               \<and> t1 \<ge> 0 \<and> t2 \<ge> 0 \<and> t3 \<ge> 0 \<and> t4 \<ge> 0\<close>  (is ?thesis1)
  and trace_class_decomp_4pos: \<open>trace_class t \<Longrightarrow>
             \<exists>t1 t2 t3 t4.
              t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4
               \<and> trace_class t1 \<and> trace_class t2 \<and> trace_class t3 \<and> trace_class t4
               \<and> trace_norm t1 \<le> trace_norm t \<and> trace_norm t2 \<le> trace_norm t \<and> trace_norm t3 \<le> trace_norm t \<and> trace_norm t4 \<le> trace_norm t 
               \<and> t1 \<ge> 0 \<and> t2 \<ge> 0 \<and> t3 \<ge> 0 \<and> t4 \<ge> 0\<close> (is \<open>_ \<Longrightarrow> ?thesis2\<close>)
proof -
  define th ta where \<open>th = (1/2) *\<^sub>C (t + t*)\<close> and \<open>ta = (-\<i>/2) *\<^sub>C (t - t*)\<close>
  have th_herm: \<open>th* = th\<close>
    by (simp add: adj_plus th_def)
  have \<open>ta* = ta\<close>
    by (simp add: adj_minus ta_def scaleC_diff_right adj_uminus)
  have \<open>t = th + \<i> *\<^sub>C ta\<close>
    by (smt (verit, ccfv_SIG) add.commute add.inverse_inverse complex_i_mult_minus complex_vector.vector_space_assms(1) complex_vector.vector_space_assms(3) diff_add_cancel group_cancel.add2 i_squared scaleC_half_double ta_def th_def times_divide_eq_right)
  define t1 t2 where \<open>t1 = (abs_op th + th) /\<^sub>R 2\<close> and \<open>t2 = (abs_op th - th) /\<^sub>R 2\<close>
  have \<open>t1 \<ge> 0\<close>
    using abs_op_geq_neq[OF \<open>th* = th\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t1_def intro!: scaleR_nonneg_nonneg)
  have \<open>t2 \<ge> 0\<close>
    using abs_op_geq[OF \<open>th* = th\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t2_def intro!: scaleR_nonneg_nonneg)
  have \<open>th = t1 - t2\<close>
    apply (simp add: t1_def t2_def)
    by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(8) diff_add_cancel ordered_field_class.sign_simps(2) ordered_field_class.sign_simps(27) scaleR_half_double)
  define t3 t4 where \<open>t3 = (abs_op ta + ta) /\<^sub>R 2\<close> and \<open>t4 = (abs_op ta - ta) /\<^sub>R 2\<close>
  have \<open>t3 \<ge> 0\<close>
    using abs_op_geq_neq[OF \<open>ta* = ta\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t3_def intro!: scaleR_nonneg_nonneg)
  have \<open>t4 \<ge> 0\<close>
    using abs_op_geq[OF \<open>ta* = ta\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t4_def intro!: scaleR_nonneg_nonneg)
  have \<open>ta = t3 - t4\<close>
    apply (simp add: t3_def t4_def)
    by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(8) diff_add_cancel ordered_field_class.sign_simps(2) ordered_field_class.sign_simps(27) scaleR_half_double)
  have decomp: \<open>t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4\<close>
    by (simp add: \<open>t = th + \<i> *\<^sub>C ta\<close> \<open>th = t1 - t2\<close> \<open>ta = t3 - t4\<close> scaleC_diff_right)
  from decomp \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close>
  show ?thesis1
    by auto
  show ?thesis2 if \<open>trace_class t\<close>
  proof -
    have \<open>trace_class th\<close> \<open>trace_class ta\<close>
      by (auto simp add: th_def ta_def
          intro!: \<open>trace_class t\<close> trace_class_scaleC trace_class_plus trace_class_minus trace_class_uminus trace_class_adj)
    then have tc: \<open>trace_class t1\<close> \<open>trace_class t2\<close> \<open>trace_class t3\<close> \<open>trace_class t4\<close>
      by (auto simp add: t1_def t2_def t3_def t4_def scaleR_scaleC intro!: trace_class_scaleC)
    have tn_th: \<open>trace_norm th \<le> trace_norm t\<close>
      using trace_norm_triangle[of t \<open>t*\<close>] 
      by (auto simp add: that th_def trace_norm_scaleC)
    have tn_ta: \<open>trace_norm ta \<le> trace_norm t\<close>
      using trace_norm_triangle_minus[of t \<open>t*\<close>] 
      by (auto simp add: that ta_def trace_norm_scaleC)
    have tn1: \<open>trace_norm t1 \<le> trace_norm t\<close>
      using trace_norm_triangle[of \<open>abs_op th\<close> th] tn_th
      by (auto simp add: \<open>trace_class th\<close> t1_def trace_norm_scaleC scaleR_scaleC)
    have tn2: \<open>trace_norm t2 \<le> trace_norm t\<close>
      using trace_norm_triangle_minus[of \<open>abs_op th\<close> th] tn_th
      by (auto simp add: \<open>trace_class th\<close> t2_def trace_norm_scaleC scaleR_scaleC)
    have tn3: \<open>trace_norm t3 \<le> trace_norm t\<close>
      using trace_norm_triangle[of \<open>abs_op ta\<close> ta] tn_ta
      by (auto simp add: \<open>trace_class ta\<close> t3_def trace_norm_scaleC scaleR_scaleC)
    have tn4: \<open>trace_norm t4 \<le> trace_norm t\<close>
      using trace_norm_triangle_minus[of \<open>abs_op ta\<close> ta] tn_ta
      by (auto simp add: \<open>trace_class ta\<close> t4_def trace_norm_scaleC scaleR_scaleC)
    from decomp tc \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close> tn1 tn2 tn3 tn4
    show ?thesis2
      by auto
  qed
qed

lemma trace_class_decomp_4pos':
  fixes t :: \<open>('a::chilbert_space,'a) trace_class\<close>
  shows \<open>\<exists>t1 t2 t3 t4.
              t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4
               \<and> norm t1 \<le> norm t \<and> norm t2 \<le> norm t \<and> norm t3 \<le> norm t \<and> norm t4 \<le> norm t 
               \<and> t1 \<ge> 0 \<and> t2 \<ge> 0 \<and> t3 \<ge> 0 \<and> t4 \<ge> 0\<close>
proof -
  from trace_class_decomp_4pos[of \<open>from_trace_class t\<close>, OF trace_class_from_trace_class]
  obtain t1' t2' t3' t4'
    where *: \<open>from_trace_class t = t1' - t2' + \<i> *\<^sub>C t3' - \<i> *\<^sub>C t4'
               \<and> trace_class t1' \<and> trace_class t2' \<and> trace_class t3' \<and> trace_class t4'
               \<and> trace_norm t1' \<le> trace_norm (from_trace_class t) \<and> trace_norm t2' \<le> trace_norm (from_trace_class t) \<and> trace_norm t3' \<le> trace_norm (from_trace_class t) \<and> trace_norm t4' \<le> trace_norm (from_trace_class t) 
               \<and> t1' \<ge> 0 \<and> t2' \<ge> 0 \<and> t3' \<ge> 0 \<and> t4' \<ge> 0\<close>
    by auto
  then obtain t1 t2 t3 t4 where
    t1234: \<open>t1' = from_trace_class t1\<close> \<open>t2' = from_trace_class t2\<close> \<open>t3' = from_trace_class t3\<close> \<open>t4' = from_trace_class t4\<close>
    by (metis from_trace_class_cases mem_Collect_eq)
  with * have n1234: \<open>norm t1 \<le> norm t\<close> \<open>norm t2 \<le> norm t\<close> \<open>norm t3 \<le> norm t\<close> \<open>norm t4 \<le> norm t\<close>
    by (metis norm_trace_class.rep_eq)+
  have t_decomp: \<open>t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4\<close>
    using * unfolding t1234 
    by (auto simp: from_trace_class_inject
        simp flip: scaleC_trace_class.rep_eq plus_trace_class.rep_eq minus_trace_class.rep_eq)
  have pos1234: \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close>
    using * unfolding t1234 
    by (auto simp: less_eq_trace_class_def)
  from t_decomp pos1234 n1234
  show ?thesis
    by blast
qed

lemma kraus_family_map_abs_summable:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>(\<lambda>E. of_nat (\<EE> E) *\<^sub>C sandwich_tc E \<rho>) abs_summable_on UNIV\<close>
proof -
  wlog \<rho>_pos: \<open>\<rho> \<ge> 0\<close> generalizing \<rho>
  proof -
    obtain \<rho>1 \<rho>2 \<rho>3 \<rho>4 where \<rho>_decomp: \<open>\<rho> = \<rho>1 - \<rho>2 + \<i> *\<^sub>C \<rho>3 - \<i> *\<^sub>C \<rho>4\<close>
      and pos: \<open>\<rho>1 \<ge> 0\<close> \<open>\<rho>2 \<ge> 0\<close> \<open>\<rho>3 \<ge> 0\<close> \<open>\<rho>4 \<ge> 0\<close>
      apply atomize_elim using trace_class_decomp_4pos'[of \<rho>] by blast
    have \<open>norm (of_nat (\<EE> x) *\<^sub>C sandwich_tc x \<rho>) 
      \<le> norm (of_nat (\<EE> x) *\<^sub>C sandwich_tc x \<rho>1)
      + norm (of_nat (\<EE> x) *\<^sub>C sandwich_tc x \<rho>2)
      + norm (of_nat (\<EE> x) *\<^sub>C sandwich_tc x \<rho>3)
      + norm (of_nat (\<EE> x) *\<^sub>C sandwich_tc x \<rho>4)\<close> 
      (is \<open>_ \<le> ?S x\<close>) for x
      by (auto simp add: \<rho>_decomp cblinfun.add_right cblinfun.diff_right cblinfun.scaleC_right
          scaleC_add_right scaleC_diff_right norm_mult
          intro!: norm_triangle_le norm_triangle_le_diff)
    then have *: \<open>norm (of_nat (\<EE> x) *\<^sub>C sandwich_tc x \<rho>) \<le> norm (?S x)\<close> for x
      by force
    show ?thesis
      apply (rule abs_summable_on_comparison_test[OF _ *])
      by (intro abs_summable_on_add abs_summable_norm abs_summable_on_scaleC_right hypothesis pos)
  qed
  from assms obtain B where B: \<open>norm (\<Sum>E\<in>F. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> B\<close> if \<open>finite F\<close> for F
    by (auto simp: kraus_family_def)

  have \<open>norm (\<Sum>E\<in>F. \<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V \<rho>)) \<le> B * norm \<rho>\<close> if \<open>finite F\<close> for F
  proof -
    have aux: \<open>complex_of_real (norm x) = y \<Longrightarrow> norm x = norm y\<close> for x :: \<open>('b,'b) trace_class\<close> and y
      using norm_of_real by fastforce
    have \<open>norm (\<Sum>E\<in>F. \<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V \<rho>))
        = norm (trace (from_trace_class (\<Sum>E\<in>F. \<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V \<rho>))))\<close>
      apply (rule aux)
      by (simp add: Misc_Missing.of_nat_0_le_iff \<rho>_pos from_trace_class_pos norm_trace_class.rep_eq sandwich_tc_pos scaleC_nonneg_nonneg sum_nonneg trace_norm_pos)
    also have \<open>\<dots> = norm (\<Sum>E\<in>F. \<EE> E * trace (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E*))\<close>
      apply (simp add: trace_sum from_trace_class_sum scaleC_trace_class.rep_eq trace_class_scaleC
          trace_scaleC from_trace_class_sandwich_tc trace_class_sandwich)
      by (simp add: sandwich_apply)
    also have \<open>\<dots> = norm (\<Sum>E\<in>F. \<EE> E * trace (E* o\<^sub>C\<^sub>L E o\<^sub>C\<^sub>L from_trace_class \<rho>))\<close>
      apply (subst circularity_of_trace)
      by (auto intro!: trace_class_comp_right simp: cblinfun_compose_assoc)
    also have \<open>\<dots> = norm (trace ((\<Sum>E\<in>F. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) o\<^sub>C\<^sub>L from_trace_class \<rho>))\<close>
      by (simp add: trace_class_scaleC trace_class_comp_right cblinfun_compose_sum_left
          flip: trace_scaleC trace_sum)
    also have \<open>\<dots> \<le> norm (\<Sum>E\<in>F. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) * norm \<rho>\<close>
      apply (simp add: norm_trace_class.rep_eq)
      using cmod_trace_times trace_class_from_trace_class by blast
    also have \<open>\<dots> \<le> B * norm \<rho>\<close>
      by (simp add: B mult_right_mono that)
    finally show ?thesis
      by -
  qed
  then show ?thesis
    apply (rule_tac infsum_tc_norm_bounded_abs_summable[where B=\<open>B * norm \<rho>\<close>])
     apply (intro scaleC_nonneg_nonneg of_nat_0_le_iff sandwich_tc_pos \<rho>_pos)
    by simp
qed

lemma kraus_family_map_summable:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>(\<lambda>E. of_nat (\<EE> E) *\<^sub>C sandwich_tc E \<rho>) summable_on UNIV\<close>
  apply (rule abs_summable_summable)
  unfolding sandwich_apply
  using assms by (rule kraus_family_map_abs_summable)

lemma kraus_family_map_plus_right:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_map \<EE> (x + y) = kraus_family_map \<EE> x + kraus_family_map \<EE> y\<close>
  using assms
  by (auto intro!: infsum_add kraus_family_map_summable
      simp add: kraus_family_map_def cblinfun.add_right scaleC_add_right)

lemma kraus_family_map_uminus_right:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_map \<EE> (- x) = - kraus_family_map \<EE> x\<close>
  using assms
  by (auto intro!: infsum_uminus kraus_family_map_summable
      simp add: kraus_family_map_def cblinfun.minus_right scaleC_minus_right)


lemma kraus_family_map_minus_right:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_map \<EE> (x - y) = kraus_family_map \<EE> x - kraus_family_map \<EE> y\<close>
  using assms
  by (simp only: diff_conv_add_uminus kraus_family_map_plus_right kraus_family_map_uminus_right)

lemma infsum_nonneg_cblinfun:
  fixes f :: "'a \<Rightarrow> 'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b"
  assumes "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum f M \<ge> 0"
  apply (cases \<open>f summable_on M\<close>)
   apply (subst infsum_0_simp[symmetric])
   apply (rule infsum_mono_cblinfun)
  using assms by (auto simp: infsum_not_exists)

lemma infsum_nonneg_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum f M \<ge> 0"
  apply (cases \<open>f summable_on M\<close>)
   apply (subst infsum_0_simp[symmetric])
   apply (rule infsum_mono_neutral_traceclass)
  using assms by (auto simp: infsum_not_exists)

lemma kraus_family_map_pos:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kraus_family_map \<EE> \<rho> \<ge> 0\<close>
  by (auto intro!: infsum_nonneg_traceclass scaleC_nonneg_nonneg of_nat_0_le_iff
      sandwich_tc_pos assms simp: kraus_family_map_def)

lemma kraus_family_map_bounded_pos:
  assumes \<open>kraus_family \<EE>\<close> and \<open>\<rho> \<ge> 0\<close>
  shows \<open>norm (kraus_family_map \<EE> \<rho>) \<le> kraus_family_norm \<EE> * norm \<rho>\<close>
proof -
  have \<open>norm (kraus_family_map \<EE> \<rho>) = Re (trace_tc (\<Sum>\<^sub>\<infinity>E. \<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V \<rho>)))\<close>
    apply (subst Re_complex_of_real[symmetric])
    apply (subst norm_tc_pos)
    using \<open>\<rho> \<ge> 0\<close> apply (rule kraus_family_map_pos)
    by (simp add: kraus_family_map_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E. Re (trace_tc (\<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V \<rho>))))\<close>
    by (simp flip: infsum_bounded_linear[of \<open>\<lambda>x. Re (trace_tc x)\<close>] 
        add: bounded_linear_compose[of Re trace_tc] bounded_linear_Re bounded_clinear.bounded_linear o_def trace_tc_scaleC assms kraus_family_map_def kraus_family_map_summable bounded_clinear.bounded_linear)
  also have \<open>\<dots> \<le> kraus_family_norm \<EE> * norm \<rho>\<close>
  proof (rule infsum_le_finite_sums)
    show \<open>(\<lambda>E. Re (trace_tc (\<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V \<rho>)))) summable_on UNIV\<close>
      apply (rule summable_on_bounded_linear[unfolded o_def, where f=\<open>\<lambda>x. Re (trace_tc x)\<close>])
      by (simp_all flip: infsum_bounded_linear[of \<open>\<lambda>x. Re (trace_tc x)\<close>] 
        add: bounded_linear_compose[of Re trace_tc] bounded_linear_Re bounded_clinear.bounded_linear o_def trace_tc_scaleC assms kraus_family_map_def kraus_family_map_summable bounded_clinear.bounded_linear)
    fix M :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close> assume \<open>finite M\<close>
    have \<open>(\<Sum>E\<in>M. Re (trace_tc (\<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V \<rho>)))) 
        = (\<Sum>E\<in>M. Re (\<EE> E * trace (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E*)))\<close>
      by (simp add: trace_tc.rep_eq from_trace_class_sandwich_tc sandwich_apply scaleC_trace_class.rep_eq trace_scaleC)
    also have \<open>\<dots> = (\<Sum>E\<in>M. Re (\<EE> E * trace (E* o\<^sub>C\<^sub>L E o\<^sub>C\<^sub>L from_trace_class \<rho>)))\<close>
      apply (subst circularity_of_trace)
      by (auto intro!: trace_class_comp_right simp: cblinfun_compose_assoc)
    also have \<open>\<dots> = Re (trace ((\<Sum>E\<in>M. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) o\<^sub>C\<^sub>L from_trace_class \<rho>))\<close>
      by (simp only: trace_class_scaleC trace_class_comp_right trace_class_from_trace_class
          flip: Re_sum trace_scaleC trace_sum cblinfun.scaleC_left cblinfun_compose_scaleC_left cblinfun_compose_sum_left)
    also have \<open>\<dots> \<le> cmod (trace ((\<Sum>E\<in>M. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) o\<^sub>C\<^sub>L from_trace_class \<rho>))\<close>
      by (rule complex_Re_le_cmod)
    also have \<open>\<dots> \<le> norm (\<Sum>E\<in>M. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) * trace_norm (from_trace_class \<rho>)\<close>
      apply (rule cmod_trace_times)
      by simp
    also have \<open>\<dots> \<le> kraus_family_norm \<EE> * norm \<rho>\<close>
      apply (simp add: flip: norm_trace_class.rep_eq)
      apply (rule mult_right_mono)
      apply (rule kraus_family_sums_bounded_by_norm)
      using assms by auto
    finally show \<open>(\<Sum>E\<in>M. Re (trace_tc (complex_of_nat (\<EE> E) *\<^sub>C (sandwich_tc E *\<^sub>V \<rho>)))) \<le> kraus_family_norm \<EE> * norm \<rho>\<close>
      by -
  qed
  finally show ?thesis 
    by -
qed

lemma kraus_family_map_bounded:
  assumes [simp]: \<open>kraus_family \<EE>\<close>
  shows \<open>norm (kraus_family_map \<EE> \<rho>) \<le> 4 * kraus_family_norm \<EE> * norm \<rho>\<close>
proof -
  have aux: \<open>4 * x = x + x + x + x\<close> for x :: real
    by auto
  obtain \<rho>1 \<rho>2 \<rho>3 \<rho>4 where \<rho>_decomp: \<open>\<rho> = \<rho>1 - \<rho>2 + \<i> *\<^sub>C \<rho>3 - \<i> *\<^sub>C \<rho>4\<close>
    and pos: \<open>\<rho>1 \<ge> 0\<close> \<open>\<rho>2 \<ge> 0\<close> \<open>\<rho>3 \<ge> 0\<close> \<open>\<rho>4 \<ge> 0\<close>
    and norm: \<open>norm \<rho>1 \<le> norm \<rho>\<close> \<open>norm \<rho>2 \<le> norm \<rho>\<close> \<open>norm \<rho>3 \<le> norm \<rho>\<close> \<open>norm \<rho>4 \<le> norm \<rho>\<close>
    apply atomize_elim using trace_class_decomp_4pos'[of \<rho>] by blast
  have \<open>norm (kraus_family_map \<EE> \<rho>) \<le>
          norm (kraus_family_map \<EE> \<rho>1) +
          norm (kraus_family_map \<EE> \<rho>2) +
          norm (kraus_family_map \<EE> \<rho>3) +
          norm (kraus_family_map \<EE> \<rho>4)\<close>
    by (auto intro!: norm_triangle_le norm_triangle_le_diff
        simp add: \<rho>_decomp kraus_family_map_plus_right kraus_family_map_minus_right
        kraus_family_map_scaleC)
  also have \<open>\<dots> \<le> 
        kraus_family_norm \<EE> * norm \<rho>1
        + kraus_family_norm \<EE> * norm \<rho>2
        + kraus_family_norm \<EE> * norm \<rho>3
        + kraus_family_norm \<EE> * norm \<rho>4\<close>
    by (auto intro!: add_mono simp add: pos kraus_family_map_bounded_pos)
  also have \<open>\<dots> = kraus_family_norm \<EE> * (norm \<rho>1 + norm \<rho>2 + norm \<rho>3 + norm \<rho>4)\<close>
    by argo
  also have \<open>\<dots> \<le> kraus_family_norm \<EE> * (norm \<rho> + norm \<rho> + norm \<rho> + norm \<rho>)\<close>
    by (auto intro!: mult_left_mono add_mono kraus_family_norm_geq0 assms
        simp only: aux norm)
  also have \<open>\<dots> = 4 * kraus_family_norm \<EE> * norm \<rho>\<close>
    by argo
  finally show ?thesis
    by -
qed

lemma kraus_family_map_bounded_clinear:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>bounded_clinear (kraus_family_map \<EE>)\<close>
  apply (rule bounded_clinearI[where K=\<open>4 * kraus_family_norm \<EE>\<close>])
    apply (auto intro!: kraus_family_map_plus_right kraus_family_map_scaleC assms
      mult.commute)
  using kraus_family_map_bounded[OF assms]
  by (simp add: mult.commute)


lemma kraus_family_map_bounded_tight:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_norm \<EE> = (\<Squnion>\<rho>\<in>{\<rho>. \<rho>\<ge>0}. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close>
proof (rule antisym)
  from assms
  have bounded: \<open>norm (kraus_family_map \<EE> \<rho>) / norm \<rho> \<le> kraus_family_norm \<EE>\<close> if \<open>\<rho> \<ge> 0\<close> for \<rho>
    apply (cases \<open>\<rho> = 0\<close>)
    by (simp_all add: that kraus_family_norm_geq0 kraus_family_map_bounded_pos linordered_field_class.pos_divide_le_eq)

  have aux1: \<open>0 \<le> (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C
            sandwich_tc E (Abs_trace_class (selfbutter \<psi>)))\<close> for \<psi> M
    by (auto intro!: sum_nonneg scaleC_nonneg_nonneg of_nat_0_le_iff Abs_trace_class_geq0I
        trace_class_sandwich sandwich_tc_pos)

  show \<open>(\<Squnion>\<rho>\<in>{\<rho>. \<rho>\<ge>0}. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>) \<le> kraus_family_norm \<EE>\<close>
    apply (rule cSUP_least)
    using bounded by auto
  show \<open>kraus_family_norm \<EE> \<le> (\<Squnion>\<rho>\<in>{\<rho>. \<rho>\<ge>0}. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close>
    unfolding kraus_family_norm_def
  proof (rule cSUP_least)
    show \<open>Collect finite \<noteq> {}\<close>
      by auto
    fix M :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
    assume \<open>M \<in> Collect finite\<close>
    then have [simp]: \<open>finite M\<close> by simp
    have \<open>norm (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) - \<epsilon>
            \<le> (\<Squnion>\<rho>\<in>{\<rho>. \<rho>\<ge>0}. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close> 
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
        apply (auto intro!: image_eqI simp: less_eq_trace_class_def Abs_trace_class_inverse)[1]
        apply (rule bdd_aboveI[where M=\<open>kraus_family_norm \<EE>\<close>])
        using bounded by auto
      finally show ?thesis
        using complex_of_real_mono_iff by blast
    qed
    then show \<open>norm (\<Sum>E\<in>M. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> (\<Squnion>\<rho>\<in>{\<rho>. \<rho>\<ge>0}. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close>
      by (smt (verit, ccfv_SIG) nice_ordered_field_class.field_le_epsilon)
  qed
qed


(* lemma
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>((\<lambda>F. norm (\<Sum>E\<in>F. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E))) \<longlongrightarrow> kraus_family_norm \<EE>) (finite_subsets_at_top UNIV)\<close> *)

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

(* TODO: also flip sandwich_compose *)
lemma sandwich_tc_compose: \<open>sandwich_tc (A o\<^sub>C\<^sub>L B) = sandwich_tc A o\<^sub>C\<^sub>L sandwich_tc B\<close>
  apply (rule cblinfun_eqI)
  apply (rule from_trace_class_inject[THEN iffD1])
  apply (transfer fixing: A B)
  by (simp flip: sandwich_compose)

lemma sandwich_tc_0_left[simp]: \<open>sandwich_tc 0 = 0\<close>
  by (metis (no_types, opaque_lifting) cblinfun.zero_left cblinfun_eqI linorder_not_le norm_sandwich_tc norm_scaleC norm_zero power2_eq_square scaleC_left.zero zero_less_norm_iff)


lemma kraus_family_map_mono:
  assumes \<open>kraus_family \<EE>\<close> and \<open>\<rho> \<ge> \<tau>\<close>
  shows \<open>kraus_family_map \<EE> \<rho> \<ge> kraus_family_map \<EE> \<tau>\<close>
  apply (subst diff_ge_0_iff_ge[symmetric])
  apply (subst kraus_family_map_minus_right[symmetric])
   apply (fact assms)
  apply (rule kraus_family_map_pos)
  using assms(2) by (subst diff_ge_0_iff_ge)

lemma kraus_family_map_geq_sum:
  assumes \<open>kraus_family \<EE>\<close> and \<open>\<rho> \<ge> 0\<close>
  shows \<open>kraus_family_map \<EE> \<rho> \<ge> (\<Sum>E\<in>M. \<EE> E *\<^sub>C sandwich_tc E \<rho>)\<close>
proof (cases \<open>finite M\<close>)
  case True
  have *: \<open>(\<lambda>E. complex_of_nat (\<EE> E) *\<^sub>C (sandwich_tc E *\<^sub>V \<rho>)) summable_on X\<close> for X
    apply (rule summable_on_subset_banach[where A=UNIV])
     apply (rule kraus_family_map_summable)
    using assms by auto
  show ?thesis
    apply (subst infsum_finite[symmetric])
    by (auto intro!: infsum_mono_neutral_traceclass * scaleC_nonneg_nonneg of_nat_0_le_iff 
        True sandwich_tc_pos assms
        simp: kraus_family_map_def)
next
  case False
  with assms show ?thesis
    by (simp add: kraus_family_map_pos) 
qed


lemma kraus_family_comp_apply:
  assumes [simp]: \<open>kraus_family \<EE>\<close> \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) = kraus_family_map \<EE> \<circ> kraus_family_map \<FF>\<close>
proof (rule ext, rename_tac \<rho>)
  fix \<rho> :: \<open>('c, 'c) trace_class\<close>
  wlog \<rho>_pos: \<open>\<rho> \<ge> 0\<close>
    goal \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) \<rho> = (kraus_family_map \<EE> \<circ> kraus_family_map \<FF>) \<rho>\<close>
    generalizing \<rho>
  proof -
    have aux: \<open>trace_class (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E* )\<close> 
      for \<rho> :: \<open>('a, 'a) trace_class\<close> and E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      by (simp add: trace_class_comp_left trace_class_comp_right)
    obtain \<rho>1 \<rho>2 \<rho>3 \<rho>4 where \<rho>_decomp: \<open>\<rho> = \<rho>1 - \<rho>2 + \<i> *\<^sub>C \<rho>3 - \<i> *\<^sub>C \<rho>4\<close>
      and pos: \<open>\<rho>1 \<ge> 0\<close> \<open>\<rho>2 \<ge> 0\<close> \<open>\<rho>3 \<ge> 0\<close> \<open>\<rho>4 \<ge> 0\<close>
      apply atomize_elim using trace_class_decomp_4pos'[of \<rho>] by blast
    show ?thesis
      using pos by (simp add: hypothesis \<rho>_decomp kraus_family_map_plus_right kraus_family_map_minus_right kraus_family_kraus_family_comp kraus_family_map_scaleC)
  qed

  define EF where \<open>EF G = {(E, F). \<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F = G}\<close> for G
  have finite_EF: \<open>finite (EF G)\<close> if \<open>G \<noteq> 0\<close> for G
    unfolding EF_def
    using assms that by (rule kraus_family_comp_finite)

  have sum1: \<open>(\<lambda>(E, F). \<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V complex_of_nat (\<FF> F) *\<^sub>C (sandwich_tc F *\<^sub>V \<rho>))) summable_on U\<close> for U
  proof -
    have *: \<open>norm (\<Sum>(E,F)\<in>M. \<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V \<FF> F *\<^sub>C (sandwich_tc F *\<^sub>V \<rho>))) \<le> norm (kraus_family_map \<EE> (kraus_family_map \<FF> \<rho>))\<close> if \<open>finite M\<close> for M
    proof -
      have \<open>norm (\<Sum>(E,F)\<in>M. \<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V \<FF> F *\<^sub>C (sandwich_tc F *\<^sub>V \<rho>)))
          \<le> norm (\<Sum>(E,F)\<in>fst ` M \<times> snd ` M. \<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V \<FF> F *\<^sub>C (sandwich_tc F *\<^sub>V \<rho>)))\<close>
        apply (rule norm_cblinfun_mono_trace_class)
        using that by (force intro!: sum_mono2 simp add: \<rho>_pos case_prod_unfold Misc_Missing.of_nat_0_le_iff   sandwich_tc_pos scaleC_nonneg_nonneg sum_nonneg)+
      also have \<open>\<dots> = norm (\<Sum>E\<in>fst ` M. \<EE> E *\<^sub>C sandwich_tc E *\<^sub>V (\<Sum>F\<in>snd ` M. \<FF> F *\<^sub>C (sandwich_tc F *\<^sub>V \<rho>)))\<close>
        by (simp add:  flip: sum.cartesian_product scaleC_sum_right cblinfun.sum_right)
      also have \<open>\<dots> \<le> norm (kraus_family_map \<EE> (\<Sum>F\<in>snd ` M. \<FF> F *\<^sub>C (sandwich_tc F *\<^sub>V \<rho>)))\<close>
        apply (rule norm_cblinfun_mono_trace_class)
         apply (simp add: \<rho>_pos case_prod_unfold Misc_Missing.of_nat_0_le_iff sandwich_tc_pos scaleC_nonneg_nonneg sum_nonneg)+
        apply (rule kraus_family_map_geq_sum)
        by (simp add: \<rho>_pos case_prod_unfold Misc_Missing.of_nat_0_le_iff sandwich_tc_pos scaleC_nonneg_nonneg sum_nonneg)+
      also have \<open>\<dots> \<le> norm (kraus_family_map \<EE> (kraus_family_map \<FF> \<rho>))\<close>
        apply (rule norm_cblinfun_mono_trace_class)
         apply (simp add: kraus_family_map_pos \<rho>_pos case_prod_unfold Misc_Missing.of_nat_0_le_iff sandwich_tc_pos scaleC_nonneg_nonneg sum_nonneg)+
        apply (rule kraus_family_map_mono, simp)
        apply (rule kraus_family_map_geq_sum)
        by (auto simp: \<rho>_pos)
      finally show ?thesis
        by -
    qed
    show ?thesis
      apply (rule summable_on_subset_banach[where A=\<open>UNIV \<times> UNIV\<close>, rotated], simp)
      apply (rule abs_summable_summable)
      apply (rule infsum_tc_norm_bounded_abs_summable)
       apply (simp add: \<rho>_pos case_prod_unfold Misc_Missing.of_nat_0_le_iff   sandwich_tc_pos scaleC_nonneg_nonneg sum_nonneg )
      using * by simp
  qed
  then have \<open>(\<lambda>(G, E, F). \<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V complex_of_nat (\<FF> F) *\<^sub>C (sandwich_tc F *\<^sub>V \<rho>))) summable_on (SIGMA G:UNIV. EF G)\<close>
    apply (subst summable_on_reindex_bij_betw[where A=\<open>{E. \<EE> E \<noteq> 0} \<times> {F. \<FF> F \<noteq> 0}\<close> and g=\<open>\<lambda>(E,F). (E o\<^sub>C\<^sub>L F, E, F)\<close>, symmetric])
     apply (rule bij_betw_byWitness[where f'=\<open>\<lambda>(G,E,F). (E, F)\<close>])
    by (auto simp: case_prod_unfold EF_def[abs_def])
  then have sum2: \<open>(\<lambda>(G, E, F). (\<EE> E * \<FF> F) *\<^sub>C sandwich_tc G *\<^sub>V \<rho>) summable_on (SIGMA G:UNIV. EF G)\<close>
    apply (rule summable_on_cong[THEN iffD1, rotated -1])
    by (auto simp: EF_def cblinfun.scaleC_right sandwich_tc_compose)

  have \<open>(kraus_family_map \<EE> \<circ> kraus_family_map \<FF>) \<rho> 
      = (\<Sum>\<^sub>\<infinity>E|\<EE> E \<noteq> 0. \<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V (\<Sum>\<^sub>\<infinity>F|\<FF> F \<noteq> 0. \<FF> F *\<^sub>C (sandwich_tc F *\<^sub>V \<rho>))))\<close>
    apply (simp add: kraus_family_map_def)
    apply (subst infsum_cong_neutral[where S=\<open>{F. 0 < \<FF> F}\<close> and T=UNIV])
    apply auto
    apply (subst infsum_cong_neutral[where S=\<open>{E. 0 < \<EE> E}\<close> and T=UNIV])
    by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E|\<EE> E \<noteq> 0. \<Sum>\<^sub>\<infinity>F|\<FF> F \<noteq> 0. \<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V \<FF> F *\<^sub>C (sandwich_tc F *\<^sub>V \<rho>)))\<close>
    by (simp add: infsum_scaleC_right infsum_cblinfun_apply kraus_family_map_summable assms
        summable_on_subset_banach[where A=UNIV])
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,F)|\<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0. \<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V \<FF> F *\<^sub>C (sandwich_tc F *\<^sub>V \<rho>)))\<close>
    apply (subst infsum_Sigma'_banach)
    using sum1 by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(G,E,F)\<in>(SIGMA G:UNIV. EF G). \<EE> E *\<^sub>C (sandwich_tc E *\<^sub>V \<FF> F *\<^sub>C (sandwich_tc F *\<^sub>V \<rho>)))\<close>
    apply (subst infsum_reindex_bij_betw[symmetric, where A=\<open>SIGMA G:UNIV. EF G\<close> and g=\<open>\<lambda>(G,E,F). (E,F)\<close>])
    apply (rule bij_betw_byWitness[where f'=\<open>\<lambda>(E,F). (E o\<^sub>C\<^sub>L F, E, F)\<close>])
    by (auto simp: case_prod_unfold EF_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(G,E,F)\<in>(SIGMA G:UNIV. EF G). (\<EE> E * \<FF> F) *\<^sub>C sandwich_tc G *\<^sub>V \<rho>)\<close>
    apply (rule infsum_cong)
    by (auto simp: EF_def cblinfun.scaleC_right sandwich_tc_compose)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>G. \<Sum>\<^sub>\<infinity>(E,F)\<in>EF G. (\<EE> E * \<FF> F) *\<^sub>C sandwich_tc G *\<^sub>V \<rho>)\<close>
    apply (rule infsum_Sigma'_banach[symmetric])
    using sum2 by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>G|G\<noteq>0. \<Sum>\<^sub>\<infinity>(E,F)\<in>EF G. (\<EE> E * \<FF> F) *\<^sub>C sandwich_tc G *\<^sub>V \<rho>)\<close>
    apply (rule infsum_cong_neutral)
    by (auto simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>G|G\<noteq>0. \<Sum>(E,F)\<in>EF G. (\<EE> E * \<FF> F) *\<^sub>C sandwich_tc G *\<^sub>V \<rho>)\<close>
    apply (rule infsum_cong)
    using finite_EF by simp
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>G|G\<noteq>0. (\<Sum>(E,F)\<in>EF G. (\<EE> E * \<FF> F)) *\<^sub>C sandwich_tc G *\<^sub>V \<rho>)\<close>
    by (auto intro!: infsum_cong simp: case_prod_unfold simp flip: scaleC_sum_left)
  also have \<open>\<dots> = kraus_family_map (kraus_family_comp \<EE> \<FF>) \<rho>\<close>
    unfolding kraus_family_map_def kraus_family_comp_def
    apply (rule infsum_cong_neutral)
    by (auto simp: EF_def)
  finally show \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) \<rho> = (kraus_family_map \<EE> \<circ> kraus_family_map \<FF>) \<rho>\<close>
    by simp
qed



lift_definition kraus_map_comp :: \<open>('a::chilbert_space,'b::chilbert_space) kraus_map
                                \<Rightarrow> ('c::chilbert_space,'a) kraus_map \<Rightarrow> ('c,'b) kraus_map\<close>
  is kraus_family_comp
  by (auto intro!: kraus_family_kraus_family_comp
      simp add: kraus_equivalent_def kraus_family_comp_apply)

definition \<open>kraus_map_id = kraus_map_of_op id_cblinfun\<close>

lemma kraus_map_norm_id_le: \<open>kraus_map_norm kraus_map_id \<le> 1\<close>
  apply (simp add: kraus_map_id_def)
  apply transfer
  by (auto intro!: power_le_one onorm_pos_le onorm_id_le)

lemma kraus_map_norm_id[simp]: \<open>kraus_map_norm (kraus_map_id :: ('a :: {chilbert_space, not_singleton},'a) kraus_map) = 1\<close>
  by (auto intro!: antisym kraus_map_norm_id_le simp: kraus_map_id_def)

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

lemma scaleC_scaleR_commute: \<open>a *\<^sub>C b *\<^sub>R x = b *\<^sub>R a *\<^sub>C x\<close> for x :: \<open>_::complex_normed_vector\<close>
  by (simp add: scaleR_scaleC scaleC_left_commute)


definition \<open>kraus_family_scale r \<EE> E = (if r \<le> 0 then 0 else \<EE> (E /\<^sub>R sqrt r))\<close>


lemma kraus_family_scale_neg: \<open>kraus_family_scale r = (\<lambda>_. 0)\<close> if \<open>r \<le> 0\<close>
  using that by (auto intro!: ext simp add: kraus_family_scale_def)


lemma kraus_family_kraus_family_scale:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family (kraus_family_scale r \<EE>)\<close>
proof (cases \<open>r > 0\<close>)
  case True
  define B where \<open>B = kraus_family_norm \<EE> * r\<close>
  have \<open>norm (\<Sum>E\<in>F. \<EE> (E /\<^sub>R sqrt r) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> B\<close>
    if \<open>finite F\<close> for F
  proof -
    define F' where \<open>F' = (\<lambda>x. x /\<^sub>R sqrt r) ` F\<close>
    have [simp]: \<open>finite F'\<close>
      using F'_def that by blast
    have inj: \<open>inj_on (\<lambda>x. x /\<^sub>R sqrt r) F\<close>
      by (metis True UNIV_I dual_order.refl injective_scaleR linordered_field_class.inverse_positive_iff_positive not_less real_sqrt_less_mono real_sqrt_zero subset_iff subset_inj_on)
    from assms have \<open>norm (\<Sum>E\<in>F'. \<EE> E *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> kraus_family_norm \<EE>\<close>
      using B_def kraus_family_sums_bounded_by_norm by blast
    then show \<open>norm (\<Sum>E\<in>F. \<EE> (E /\<^sub>R sqrt r) *\<^sub>C (E* o\<^sub>C\<^sub>L E)) \<le> B\<close>
      unfolding F'_def B_def
      apply (subst (asm) sum.reindex)
      apply (fact inj)
      using True apply (simp add: scaleC_scaleR_commute flip: scale_sum_right inverse_mult_distrib divide_inverse_commute)
      using nice_ordered_field_class.pos_divide_le_eq by blast
  qed
  then show ?thesis
    using True by (auto simp add: kraus_family_def kraus_family_scale_def) 
next
  case False
  then show ?thesis
    apply (subst kraus_family_scale_neg)
    by auto
qed

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

lemma kraus_map_norm_0[simp]: \<open>kraus_map_norm 0 = 0\<close>
  apply transfer
  by (auto intro!: cSUP_const simp: kraus_family_norm_def)

(*
(* TODO move, TODO generalize from real *)
lemma
  fixes a :: real
  assumes \<open>bdd_above (f ` F)\<close>
  assumes \<open>(\<Squnion>x\<in>F. f x) = a\<close>
  assumes \<open>b \<in> F\<close>
  shows \<open>f b \<le> a\<close>
  by (metis assms(1) assms(2) assms(3) cSUP_upper)
by -

lemma
  fixes a :: real
  assumes \<open>bdd_above F\<close>
  assumes \<open>(\<Squnion>F) = a\<close>
  assumes \<open>b \<in> F\<close>
  shows \<open>b \<le> a\<close>
try0
sledgehammer
by - *)


instantiation kraus_map :: (chilbert_space, chilbert_space) dist begin
definition dist_kraus_map :: \<open>('a,'b) kraus_map \<Rightarrow> ('a,'b) kraus_map \<Rightarrow> real\<close> where
  \<open>dist_kraus_map E F = (\<Squnion>\<rho>. dist (kraus_map_apply E \<rho>) (kraus_map_apply F \<rho>) / norm \<rho>)\<close>
instance..
end

lemma kraus_map_apply_inj: \<open>kraus_map_apply x = kraus_map_apply y \<Longrightarrow> x = y\<close>
  apply transfer
  by (simp add: kraus_equivalent_def)

lemma norm_kraus_map_apply: \<open>norm (kraus_map_apply E \<rho>) \<le> 4 * kraus_map_norm E * norm \<rho>\<close>
  apply (transfer fixing: \<rho>)
  using kraus_equivalent_def kraus_family_map_bounded by blast

lemma norm_kraus_map_apply_pos: \<open>norm (kraus_map_apply E \<rho>) \<le> kraus_map_norm E * norm \<rho>\<close> if \<open>\<rho> \<ge> 0\<close>
  apply (transfer fixing: \<rho>)
  by (simp add: kraus_equivalent_def kraus_family_map_bounded_pos that)

lemma kraus_map_norm_geq0[simp]: \<open>kraus_map_norm E \<ge> 0\<close>
  apply transfer
  by (simp add: kraus_equivalent_def kraus_family_norm_geq0)

lemma dist_kraus_map_bdd: \<open>bdd_above (range (\<lambda>\<rho>. dist (kraus_map_apply x *\<^sub>V \<rho>) (kraus_map_apply y *\<^sub>V \<rho>) / norm \<rho>))\<close>
proof (rule bdd_aboveI)
  fix r
  assume \<open>r \<in> range (\<lambda>\<rho>. dist (kraus_map_apply x *\<^sub>V \<rho>) (kraus_map_apply y *\<^sub>V \<rho>) / norm \<rho>)\<close>
  then obtain \<rho> where r_\<rho>: \<open>r = dist (kraus_map_apply x *\<^sub>V \<rho>) (kraus_map_apply y *\<^sub>V \<rho>) / norm \<rho>\<close>
    by auto
  have \<open>dist (kraus_map_apply x *\<^sub>V \<rho>) (kraus_map_apply y *\<^sub>V \<rho>) \<le> 
        norm (kraus_map_apply x *\<^sub>V \<rho>) + norm (kraus_map_apply y *\<^sub>V \<rho>)\<close>
    by (metis dist_0_norm dist_triangle3)
  also have \<open>\<dots> \<le> 4 * kraus_map_norm x * norm \<rho> + 4 * kraus_map_norm y * norm \<rho>\<close>
    by (auto intro!: add_mono norm_kraus_map_apply)
  also have \<open>\<dots> \<le> (4 * kraus_map_norm x + 4 * kraus_map_norm y) * norm \<rho>\<close>
    by (simp add: cross3_simps(23))
  finally show \<open>r \<le> 4 * kraus_map_norm x + 4 * kraus_map_norm y\<close>
    apply (cases \<open>norm \<rho> = 0\<close>)
    by (auto simp: r_\<rho> linordered_field_class.pos_divide_le_eq)
qed

instantiation kraus_map :: (chilbert_space, chilbert_space) metric_space begin
definition \<open>uniformity_kraus_map = (\<Sqinter>e\<in>{0<..}. principal {(x :: ('a,'b) kraus_map, y). dist x y < e})\<close>
definition \<open>open_kraus_map U = (\<forall>x::('a,'b) kraus_map \<in> U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)\<close>
instance
proof (intro_classes, rule uniformity_kraus_map_def, rule open_kraus_map_def)
  fix x y z :: \<open>('a,'b) kraus_map\<close>
  show \<open>(dist x y = 0) \<longleftrightarrow> (x = y)\<close>
  proof (rule iffI)
    show \<open>x = y \<Longrightarrow> dist x y = 0\<close>
      by (simp add: dist_kraus_map_def)
    assume dist_0: \<open>dist x y = 0\<close>
    have \<open>dist (kraus_map_apply x *\<^sub>V \<rho>) (kraus_map_apply y *\<^sub>V \<rho>) / norm \<rho> \<le> 0\<close> for \<rho>
      by (auto intro!: cSUP_upper dist_kraus_map_bdd simp: dist_kraus_map_def simp flip: dist_0)
    then have \<open>dist (kraus_map_apply x *\<^sub>V \<rho>) (kraus_map_apply y *\<^sub>V \<rho>) = 0\<close> for \<rho>
      using order_antisym by fastforce
    then have \<open>kraus_map_apply x *\<^sub>V \<rho> = kraus_map_apply y *\<^sub>V \<rho>\<close> for \<rho>
      by simp
    then have \<open>kraus_map_apply x = kraus_map_apply y\<close> for \<rho>
      by (simp add: cblinfun_eqI)
    then show \<open>x = y\<close>
      by (simp add: kraus_map_apply_inj)
  qed
  show \<open>dist x y \<le> dist x z + dist y z\<close>
  proof (unfold dist_kraus_map_def, rule cSUP_least)
    show \<open>UNIV \<noteq> {}\<close> by simp
    fix \<rho>
    have \<open>dist (kraus_map_apply x *\<^sub>V \<rho>) (kraus_map_apply y *\<^sub>V \<rho>) / norm \<rho>
            \<le> (dist (kraus_map_apply x *\<^sub>V \<rho>) (kraus_map_apply z *\<^sub>V \<rho>) +
                dist (kraus_map_apply y *\<^sub>V \<rho>) (kraus_map_apply z *\<^sub>V \<rho>)) / norm \<rho>\<close>
      apply (rule divide_right_mono)
      using dist_triangle2 by auto
    also have \<open>\<dots> = dist (kraus_map_apply x *\<^sub>V \<rho>) (kraus_map_apply z *\<^sub>V \<rho>) / norm \<rho> +
                    dist (kraus_map_apply y *\<^sub>V \<rho>) (kraus_map_apply z *\<^sub>V \<rho>) / norm \<rho>\<close>
      by (simp add: add_divide_distrib)
    also have \<open>\<dots> \<le> (\<Squnion>\<rho>. dist (kraus_map_apply x *\<^sub>V \<rho>) (kraus_map_apply z *\<^sub>V \<rho>) / norm \<rho>) +
                  (\<Squnion>\<rho>. dist (kraus_map_apply y *\<^sub>V \<rho>) (kraus_map_apply z *\<^sub>V \<rho>) / norm \<rho>)\<close>
      by (auto intro!: add_mono cSUP_upper2 dist_kraus_map_bdd)
    finally show \<open>dist (kraus_map_apply x *\<^sub>V \<rho>) (kraus_map_apply y *\<^sub>V \<rho>) / norm \<rho> \<le> \<dots>\<close>
      by -
  qed
qed
end

lemma kraus_map_apply_comp: \<open>kraus_map_apply (kraus_map_comp E F) = kraus_map_apply E o\<^sub>C\<^sub>L kraus_map_apply F\<close>
  apply transfer
  apply (rule kraus_family_comp_apply)
  using kraus_equivalent_def by auto

lemma kraus_map_apply_0[simp]: \<open>kraus_map_apply 0 = 0\<close>
  apply transfer'
  by (simp add: kraus_family_map_def[abs_def])

lemma kraus_map_comp_0_left[simp]: \<open>kraus_map_comp 0 E = 0\<close>
  apply (rule kraus_map_apply_inj)
  apply (rule cblinfun_eqI)
  by (simp add: kraus_map_apply_comp)

lemma kraus_map_comp_0_right[simp]: \<open>kraus_map_comp E 0 = 0\<close>
  apply (rule kraus_map_apply_inj)
  apply (rule cblinfun_eqI)
  by (simp add: kraus_map_apply_comp)

lemma kraus_map_comp_assoc: \<open>kraus_map_comp (kraus_map_comp E F) G = kraus_map_comp E (kraus_map_comp F G)\<close>
  by (simp add: cblinfun_assoc_left(1) kraus_map_apply_comp kraus_map_apply_inj)

end
