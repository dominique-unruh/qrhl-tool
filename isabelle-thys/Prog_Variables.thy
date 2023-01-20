theory Prog_Variables
  imports Extended_Sorry Multi_Transfer (* Registers.Classical_Extra Registers.Quantum_Extra2 *)
    (* Complex_Bounded_Operators.Complex_L2 *)
    HOL.Map
    (* "HOL-Library.Adhoc_Overloading" *)
    (* Tensor_Product.Tensor_Product *)
    BOLegacy
    Misc_Missing
  (* keywords "variables" :: thy_decl_block *)
    Missing_Bounded_Operators
    Registers.Classical_Extra
    Registers.Quantum_Extra2
begin

unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)
hide_const (open) Order.top
no_notation Order.top ("\<top>\<index>")
hide_const (open) Axioms_Classical.getter
hide_const (open) Axioms_Classical.setter
declare [[simproc del: Laws_Quantum.compatibility_warn]]
declare [[simproc del: Laws_Classical.compatibility_warn]]
hide_const (open) Classical_Extra.X Classical_Extra.Y Classical_Extra.x Classical_Extra.y

type_synonym 'a cupdate = \<open>'a \<Rightarrow> 'a option\<close>
type_synonym 'a qupdate = \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>

subsubsection \<open>Wrapper types around registers\<close>

abbreviation \<open>cregister_raw \<equiv> Axioms_Classical.register\<close>
abbreviation \<open>qregister_raw \<equiv> Axioms_Quantum.register\<close>

abbreviation (input) \<open>tensorOp \<equiv> tensor_op\<close>

lemma cregister_raw_empty: \<open>cregister_raw F \<Longrightarrow> F Map.empty = Map.empty\<close>
  by (simp add: register_empty)
lemma qregister_raw_1: \<open>qregister_raw F \<Longrightarrow> F id_cblinfun = id_cblinfun\<close>
  by simp
lemma cregister_raw_1: \<open>cregister_raw F \<Longrightarrow> F Some = Some\<close>
  by simp
lemma qregister_raw_bounded_clinear: \<open>qregister_raw F \<Longrightarrow> bounded_clinear F\<close>
  by (rule Axioms_Quantum.register_bounded_clinear)
lemma qregister_raw_0: \<open>qregister_raw F \<Longrightarrow> F 0 = 0\<close>
  by (intro complex_vector.linear_0 bounded_clinear.clinear qregister_raw_bounded_clinear)

definition non_cregister_raw :: \<open>'a cupdate \<Rightarrow> 'b cupdate\<close> where \<open>non_cregister_raw a = Map.empty\<close>
definition non_qregister_raw :: \<open>'a qupdate \<Rightarrow> 'b qupdate\<close> where \<open>non_qregister_raw a = 0\<close>

lemma cregister_raw_inj: \<open>inj_on F X\<close> if \<open>cregister_raw F\<close>
proof -
  note [[simproc del: Laws_Classical.compatibility_warn]]
  define get set where \<open>get = Axioms_Classical.getter F\<close> and \<open>set = Axioms_Classical.setter F\<close>
  have get_set: \<open>get (set a b) = a\<close> and set_set: \<open>set a (set a' b) = set a b\<close> for a a' b
     apply (metis get_def local.set_def that valid_getter_setter_def valid_getter_setter_getter_setter)
    by (metis local.set_def that valid_getter_setter_def valid_getter_setter_getter_setter)
  fix b
  define G :: \<open>'b Axioms_Classical.update \<Rightarrow> 'a Axioms_Classical.update\<close> 
    where \<open>G g a = map_option get (g (set a b))\<close> for g a
  have \<open>G (F f) a = f a\<close> for f a
    apply (subst register_from_getter_setter_of_getter_setter[OF that, symmetric])
    unfolding G_def 
    apply (cases \<open>f a\<close>)
    by (simp_all add: register_from_getter_setter_def[abs_def] set_set get_set
        del: register_from_getter_setter_of_getter_setter
        flip: get_def set_def)
  then show \<open>inj_on F X\<close>
    by (metis ext inj_onI)
qed
lemma qregister_raw_inj: \<open>qregister_raw F \<Longrightarrow> inj_on F X\<close>
  by (rule register_inj)

lemma non_cregister_raw: \<open>\<not> cregister_raw non_cregister_raw\<close>
  by (metis cregister_raw_1 non_cregister_raw_def not_Some_eq)
lemma non_qregister_raw: \<open>\<not> qregister_raw non_qregister_raw\<close>
  by (metis id_cblinfun_not_0 non_qregister_raw_def qregister_raw_1)

typedef ('a,'b) cregister = \<open>{f :: 'a cupdate \<Rightarrow> 'b cupdate. cregister_raw f} \<union> {non_cregister_raw}\<close>
  morphisms apply_cregister Abs_cregister by auto
typedef ('a,'b) qregister = \<open>{f :: 'a qupdate \<Rightarrow> 'b qupdate. qregister_raw f} \<union> {non_qregister_raw}\<close>
  morphisms apply_qregister Abs_qregister by auto
setup_lifting type_definition_cregister
setup_lifting type_definition_qregister

lemma bounded_clinear_apply_qregister[simp]: \<open>bounded_clinear (apply_qregister F)\<close>
  apply transfer
  unfolding Axioms_Quantum.register_def
  by (auto simp: non_qregister_raw_def[abs_def])

lemma clinear_apply_qregister[simp]: \<open>clinear (apply_qregister F)\<close>
  using bounded_clinear.clinear bounded_clinear_apply_qregister by blast

lift_definition apply_cregister_total :: \<open>('a,'b) cregister \<Rightarrow> ('a\<Rightarrow>'a) \<Rightarrow> ('b\<Rightarrow>'b)\<close> is
  \<open>\<lambda>F f. the o F (Some o f)\<close>.

lift_definition non_cregister :: \<open>('a,'b) cregister\<close> is non_cregister_raw by auto
lift_definition non_qregister :: \<open>('a,'b) qregister\<close> is non_qregister_raw by auto

lift_definition cregister :: \<open>('a,'b) cregister \<Rightarrow> bool\<close> is cregister_raw.
lift_definition qregister :: \<open>('a,'b) qregister \<Rightarrow> bool\<close> is qregister_raw.

lemma non_cregister: \<open>\<not> cregister F \<longleftrightarrow> F = non_cregister\<close>
  apply transfer using non_cregister_raw by blast
lemma non_qregister: \<open>\<not> qregister F \<longleftrightarrow> F = non_qregister\<close>
  apply transfer using non_qregister_raw by blast

lemma non_cregister'[simp]: \<open>\<not> cregister non_cregister\<close>
  by (simp add: non_cregister)
lemma non_qregister'[simp]: \<open>\<not> qregister non_qregister\<close>
  by (simp add: non_qregister)

lemma apply_qregister_bounded_clinear: \<open>bounded_clinear (apply_qregister F)\<close>
  apply transfer by (auto simp add: qregister_raw_bounded_clinear non_qregister_raw_def[abs_def])

lemma apply_cregister_of_0[simp]: \<open>apply_cregister F Map.empty = Map.empty\<close>
  apply transfer apply (auto simp: non_cregister_raw_def)
  by (simp add: cregister_raw_empty)
lemma apply_qregister_of_0[simp]: \<open>apply_qregister F 0 = 0\<close>
  by (metis non_qregister non_qregister.rep_eq non_qregister_raw_def qregister.rep_eq qregister_raw_0)

lemma apply_cregister_of_id[simp]: \<open>cregister F \<Longrightarrow> apply_cregister F Some = Some\<close>
  using cregister.rep_eq cregister_raw_1 by blast
lemma apply_qregister_of_id[simp]: \<open>qregister F \<Longrightarrow> apply_qregister F id_cblinfun = id_cblinfun\<close>
  by (simp add: qregister.rep_eq qregister_raw_1)

(* Equivalence class of cregisters *)
axiomatization valid_cregister_range :: \<open>'a cupdate set \<Rightarrow> bool\<close>
  where valid_cregister_range: \<open>cregister F \<Longrightarrow> valid_cregister_range (range (apply_cregister F))\<close> for F :: \<open>('b,'a) cregister\<close>

(* TODO move *)
lemma csubspace_commutant[simp]: \<open>csubspace (commutant X)\<close>
  by (auto simp add: complex_vector.subspace_def commutant_def cblinfun_compose_add_right cblinfun_compose_add_left)

lemma closed_commutant[simp]: \<open>closed (commutant X)\<close>
proof (subst closed_sequential_limits, intro allI impI, erule conjE)
  fix s :: \<open>nat \<Rightarrow> _\<close> and l 
  assume s_comm: \<open>\<forall>n. s n \<in> commutant X\<close>
  assume \<open>s \<longlonglongrightarrow> l\<close>
  have \<open>l o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L l = 0\<close> if \<open>x \<in> X\<close> for x
  proof -
    from \<open>s \<longlonglongrightarrow> l\<close>
    have \<open>(\<lambda>n. s n o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L s n) \<longlonglongrightarrow> l o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L l\<close>
      apply (rule isCont_tendsto_compose[rotated])
      by (intro continuous_intros)
    then have \<open>(\<lambda>_. 0) \<longlonglongrightarrow> l o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L l\<close>
      using s_comm that by (auto simp add: commutant_def)
    then show ?thesis
      by (simp add: LIMSEQ_const_iff that)
  qed
  then show \<open>l \<in> commutant X\<close>
    by (simp add: commutant_def)
qed

(* TODO move *)
lemma closed_csubspace_commutant[simp]: \<open>closed_csubspace (commutant X)\<close>
  apply (rule closed_csubspace.intro) by simp_all

(* TODO move *)
lemma commutant_mult: \<open>a o\<^sub>C\<^sub>L b \<in> commutant X\<close> if \<open>a \<in> commutant X\<close> and \<open>b \<in> commutant X\<close>
  using that 
  apply (auto simp: commutant_def cblinfun_compose_assoc)
  by (simp flip: cblinfun_compose_assoc)

(* TODO move *)
lemma double_commutant_grows[simp]: \<open>X \<subseteq> commutant (commutant X)\<close>
  by (auto simp add: commutant_def)

(* TODO move *)
lemma commutant_antimono: \<open>X \<subseteq> Y \<Longrightarrow> commutant X \<supseteq> commutant Y\<close>
  by (auto simp add: commutant_def)

definition valid_qregister_range :: \<open>'a qupdate set \<Rightarrow> bool\<close> where
  \<open>valid_qregister_range \<FF> \<longleftrightarrow> (\<forall>a\<in>\<FF>. a* \<in> \<FF>) \<and> commutant (commutant \<FF>) = \<FF>\<close>

lemma valid_qregister_rangeI: \<open>(\<And>a. a\<in>\<FF> \<Longrightarrow> a* \<in> \<FF>) \<Longrightarrow> commutant (commutant \<FF>) \<subseteq> \<FF> \<Longrightarrow> valid_qregister_range \<FF>\<close>
  apply (auto simp: valid_qregister_range_def)
  using double_commutant_grows by blast

(* TODO move *)
lemma set_compr_2_image_collect: \<open>{f x y |x y. P x y} = case_prod f ` Collect (case_prod P)\<close>
  by fast
lemma set_compr_4_image_collect: \<open>{f x y z w |x y z w. P x y z w} = (\<lambda>(x,y,z,w). f x y z w) ` Collect (\<lambda>(x,y,z,w). P x y z w)\<close>
  by (auto simp: image_def)


(* TODO move *)
lemma closure_image_closure: \<open>continuous_on (closure S) f \<Longrightarrow> closure (f ` closure S) = closure (f ` S)\<close>
  by (smt (verit) closed_closure closure_closure closure_mono closure_subset image_closure_subset image_mono set_eq_subset)

(* TODO move *)
lemma ccspan_closure[simp]: \<open>ccspan (closure X) = ccspan X\<close>
  by (simp add: basic_trans_rules(24) ccspan.rep_eq ccspan_leqI ccspan_mono closure_mono closure_subset complex_vector.span_superset)

lemma tensor_ell2_diff1: \<open>tensor_ell2 (a - b) c = tensor_ell2 a c - tensor_ell2 b c\<close>
  by (simp add: bounded_cbilinear.diff_left bounded_cbilinear_tensor_ell2)

lemma tensor_ell2_diff2: \<open>tensor_ell2 a (b - c) = tensor_ell2 a b - tensor_ell2 a c\<close>
  by (simp add: bounded_cbilinear.diff_right bounded_cbilinear_tensor_ell2)

lemma continuous_tensor_ell2: \<open>continuous_on UNIV (\<lambda>(x::'a ell2, y::'b ell2). x \<otimes>\<^sub>s y)\<close>
proof -
  have cont: \<open>continuous_on UNIV (\<lambda>t. t \<otimes>\<^sub>s x)\<close> for x :: \<open>'b ell2\<close>
    by (intro linear_continuous_on bounded_clinear.bounded_linear bounded_clinear_tensor_ell22)
  have lip: \<open>local_lipschitz (UNIV :: 'a ell2 set) (UNIV :: 'b ell2 set) (\<otimes>\<^sub>s)\<close>
  proof (rule local_lipschitzI)
    fix t :: \<open>'a ell2\<close> and x :: \<open>'b ell2\<close>
    define u L :: real where \<open>u = 1\<close> and \<open>L = norm t + u\<close>
    have \<open>u > 0\<close>
      by (simp add: u_def)
    have [simp]: \<open>L \<ge> 0\<close>
      by (simp add: L_def u_def)
    have *: \<open>norm s \<le> L\<close> if \<open>s\<in>cball t u\<close> for s :: \<open>'a ell2\<close>
      using that
      apply (simp add: L_def dist_norm)
      by (smt (verit) norm_minus_commute norm_triangle_sub)
    have \<open>L-lipschitz_on (cball x u) ((\<otimes>\<^sub>s) s)\<close> if \<open>s\<in>cball t u\<close> for s :: \<open>'a ell2\<close>
      apply (rule lipschitz_onI)
      by (auto intro!: mult_right_mono *[OF that]
          simp add: dist_norm norm_tensor_ell2 simp flip: tensor_ell2_diff2)
    with \<open>u > 0\<close> show \<open>\<exists>u>0. \<exists>L. \<forall>s\<in>cball t u \<inter> UNIV. L-lipschitz_on (cball x u \<inter> UNIV) ((\<otimes>\<^sub>s) s)\<close>
      by force
  qed
  show ?thesis
    apply (subst UNIV_Times_UNIV[symmetric])
    using lip cont by (rule Lipschitz.continuous_on_TimesI)
qed

(* TODO move to Tensor_Product *)
lemma tensor_ccsubspace_image: \<open>(A *\<^sub>S T) \<otimes>\<^sub>S (B *\<^sub>S U) = (A \<otimes>\<^sub>o B) *\<^sub>S (T \<otimes>\<^sub>S U)\<close>
proof -
  have \<open>(A *\<^sub>S T) \<otimes>\<^sub>S (B *\<^sub>S U) = ccspan ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` (space_as_set (A *\<^sub>S T) \<times> space_as_set (B *\<^sub>S U)))\<close>
    by (simp add: tensor_ccsubspace_def set_compr_2_image_collect ccspan.rep_eq)
  also have \<open>\<dots> = ccspan ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` closure ((A ` space_as_set T) \<times> (B ` space_as_set U)))\<close>
    by (simp add: cblinfun_image.rep_eq closure_Times)
  also have \<open>\<dots> = ccspan (closure ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` ((A ` space_as_set T) \<times> (B ` space_as_set U))))\<close>
    apply (subst closure_image_closure[symmetric])
    using continuous_on_subset continuous_tensor_ell2 by auto
  also have \<open>\<dots> = ccspan ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` ((A ` space_as_set T) \<times> (B ` space_as_set U)))\<close>
    by simp
  also have \<open>\<dots> = (A \<otimes>\<^sub>o B) *\<^sub>S ccspan ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` (space_as_set T \<times> space_as_set U))\<close>
    by (simp add: cblinfun_image_ccspan image_image tensor_op_ell2 case_prod_beta
        flip: map_prod_image)
  also have \<open>\<dots> = (A \<otimes>\<^sub>o B) *\<^sub>S (T \<otimes>\<^sub>S U)\<close>
    by (simp add: tensor_ccsubspace_def set_compr_2_image_collect)
  finally show ?thesis
    by -
qed

(* TODO move *)
lemma isometry_tensor_op: \<open>isometry (U \<otimes>\<^sub>o V)\<close> if \<open>isometry U\<close> and \<open>isometry V\<close>
  unfolding isometry_def using that by (simp add: tensor_op_adjoint comp_tensor_op)

(* TODO move *)
lemma isometry_tensor_ell2_right: \<open>isometry (tensor_ell2_right \<psi>)\<close> if \<open>norm \<psi> = 1\<close>
  apply (rule norm_preserving_isometry)
  by (simp add: tensor_ell2_right_apply norm_tensor_ell2 that)

(* TODO move *)
lemma isometry_tensor_ell2_left: \<open>isometry (tensor_ell2_left \<psi>)\<close> if \<open>norm \<psi> = 1\<close>
  apply (rule norm_preserving_isometry)
  by (simp add: tensor_ell2_left_apply norm_tensor_ell2 that)

(* TODO move *)
lemma sandwich_isometry_id: \<open>isometry (U*) \<Longrightarrow> sandwich U id_cblinfun = id_cblinfun\<close>
  by (simp add: sandwich_apply isometry_def)

(* TODO move *)
(* TODO same for left *)
lemma tensor_ell2_right_scale: \<open>tensor_ell2_right (a *\<^sub>C \<psi>) = a *\<^sub>C tensor_ell2_right \<psi>\<close>
  apply transfer by (auto intro!: ext simp: tensor_ell2_scaleC2)

(* TODO move *)
(* TODO same for left *)
lemma tensor_ell2_right_0[simp]: \<open>tensor_ell2_right 0 = 0\<close>
  by (auto intro!: cblinfun_eqI simp: tensor_ell2_right_apply)

(* TODO move *)
(* TODO same for left *)
lemma tensor_ell2_right_adj_apply[simp]: \<open>(tensor_ell2_right \<psi>*) *\<^sub>V (\<alpha> \<otimes>\<^sub>s \<beta>) = (\<psi> \<bullet>\<^sub>C \<beta>) *\<^sub>C \<alpha>\<close>
  apply (rule cinner_extensionality)
  by (simp add: cinner_adj_right tensor_ell2_right_apply)

(* TODO move *)
(* TODO same for left *)
lemma sandwich_tensor_ell2_right: \<open>sandwich (tensor_ell2_right \<psi>*) *\<^sub>V a \<otimes>\<^sub>o b = (\<psi> \<bullet>\<^sub>C (b *\<^sub>V \<psi>)) *\<^sub>C a\<close>
  apply (rule cblinfun_eqI)
  by (simp add: sandwich_apply tensor_ell2_right_apply tensor_op_ell2)

(* TODO move *)
lemma register_range_complement_commutant: \<open>commutant (range F) = range G\<close> if \<open>complements F G\<close>
  apply (rule complement_range[symmetric])
  using that by (simp_all add: complements_def)

(* TODO move *)
lemma register_range_double_commutant: \<open>commutant (commutant (range F)) = range F\<close> if \<open>qregister_raw F\<close>
proof -
  from complement_exists
  have \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis F.
        commutant (commutant (range F)) = range F\<close>
  proof (rule with_type_mp)
    from that show \<open>qregister_raw F\<close>
      apply transfer by simp
    assume \<open>\<exists>G :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2 \<Rightarrow> 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. complements F G\<close>
    then obtain G :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2 \<Rightarrow> 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> 
      where \<open>complements F G\<close>
      by auto
    then have \<open>commutant (range F) = range G\<close>
      by (simp add: register_range_complement_commutant)
    moreover have \<open>commutant (range G) = range F\<close>
      by (meson \<open>complements F G\<close> complements_sym register_range_complement_commutant)
    ultimately show \<open>commutant (commutant (range F)) = range F\<close>
      by simp
  qed
  note this[cancel_with_type]
  then show ?thesis
    by -
qed

lemma valid_qregister_range: 
  fixes F :: \<open>('a,'b) qregister\<close>
  assumes \<open>qregister F\<close>
  shows \<open>valid_qregister_range (range (apply_qregister F))\<close>
proof (rule valid_qregister_rangeI)
  show \<open>a \<in> range (apply_qregister F) \<Longrightarrow> a* \<in> range (apply_qregister F)\<close> for a
    by (metis (mono_tags, lifting) assms image_iff qregister.rep_eq rangeI register_adj)
  show \<open>commutant (commutant (range (apply_qregister F))) \<subseteq> range (apply_qregister F)\<close>
    apply (subst register_range_double_commutant)
    using assms qregister.rep_eq by auto
qed

lift_definition cregister_id :: \<open>('a,'a) cregister\<close> is id by simp
lift_definition qregister_id :: \<open>('a,'a) qregister\<close> is id by simp

lemma apply_cregister_id[simp]: \<open>apply_cregister cregister_id = id\<close>
  by (rule cregister_id.rep_eq)
lemma apply_qregister_id[simp]: \<open>apply_qregister qregister_id = id\<close>
  by (rule qregister_id.rep_eq)

lemma cregister_id[simp]: \<open>cregister cregister_id\<close>
  apply transfer by simp
lemma qregister_id[simp]: \<open>qregister qregister_id\<close>
  apply transfer by simp

definition \<open>empty_cregister_raw = register_from_getter_setter (\<lambda>_. undefined) (\<lambda>_::_::CARD_1. id)\<close> 
lemma cregister_raw_empty_cregister_raw: \<open>cregister_raw empty_cregister_raw\<close>
  apply (auto intro!: exI simp add: Axioms_Classical.register_def empty_cregister_raw_def)
  by (simp add: valid_getter_setter_def)


lift_definition empty_cregister :: \<open>('a::{CARD_1,enum}, 'b) cregister\<close> is
  empty_cregister_raw
  using cregister_raw_empty_cregister_raw by fast
lemma empty_cregister_is_register[simp]: \<open>cregister empty_cregister\<close>
  apply transfer by (rule cregister_raw_empty_cregister_raw)
lift_definition empty_qregister :: \<open>('a::{CARD_1,enum}, 'b) qregister\<close> is
  Quantum_Extra2.empty_var
  by simp
lemma empty_qregister_is_register[simp]: \<open>qregister empty_qregister\<close>
  apply transfer by simp

definition \<open>empty_cregister_range = {Map.empty, Some}\<close>
lemma valid_empty_cregister_range: \<open>valid_cregister_range empty_cregister_range\<close>
proof -
  have 1: \<open>a \<in> (empty_cregister_range :: 'a cupdate set)\<close>
    if \<open>a \<in> range (apply_cregister (empty_cregister :: (unit,_) cregister))\<close> for a
  proof -
    from that 
    obtain b :: \<open>unit \<rightharpoonup> unit\<close> where ab: \<open>a = apply_cregister (empty_cregister :: (unit,_) cregister) b\<close>
      by auto
    consider (some) \<open>b = Some\<close> | (empty) \<open>b = Map.empty\<close>
      by force
    then show ?thesis
      apply cases
      by (auto simp add: ab empty_cregister_range_def)
  qed

  have \<open>Map.empty \<in> range (apply_cregister (empty_cregister :: (unit,_) cregister))\<close>
    by (auto intro!: range_eqI[of _ _ Map.empty])
  moreover have \<open>Some \<in> range (apply_cregister (empty_cregister :: (unit,_) cregister))\<close>
    by (auto intro!: range_eqI[of _ _ Some])
  ultimately have 2: \<open>range (apply_cregister (empty_cregister :: (unit,_) cregister)) \<supseteq> (empty_cregister_range :: 'a cupdate set)\<close>
    by (auto simp add: empty_cregister_range_def)

  from 1 2 have \<open>range (apply_cregister (empty_cregister :: (unit,_) cregister)) = (empty_cregister_range :: 'a cupdate set)\<close>
    by auto
  then show ?thesis
    by (metis empty_cregister_is_register valid_cregister_range)
qed
lemma valid_cregister_range_UNIV: \<open>valid_cregister_range UNIV\<close>
proof -
  have \<open>range (apply_cregister cregister_id) = UNIV\<close>
    by simp
  then show ?thesis
    using cregister_id valid_cregister_range by fastforce
qed
definition \<open>empty_qregister_range = range (\<lambda>c. c *\<^sub>C id_cblinfun)\<close>
lemma valid_empty_qregister_range: \<open>valid_qregister_range empty_qregister_range\<close>
proof -
  have 1: \<open>(empty_qregister_range :: 'a qupdate set) = (\<lambda>c. c *\<^sub>C id_cblinfun) ` (one_dim_iso :: unit qupdate \<Rightarrow> _) ` UNIV\<close>
    by (metis (mono_tags, lifting) UNIV_eq_I empty_qregister_range_def one_dim_iso_idem one_dim_scaleC_1 rangeI)
  have 2: \<open>\<dots> = range (apply_qregister (empty_qregister :: (unit,_) qregister))\<close>
    by (simp add: empty_qregister.rep_eq empty_var_def image_image)
  show ?thesis
    by (simp add: 1 2 valid_qregister_range)
qed
lemma valid_qregister_range_UNIV: \<open>valid_qregister_range UNIV\<close>
  by (auto simp: valid_qregister_range_def commutant_def)

typedef 'a CREGISTER = \<open>Collect valid_cregister_range :: 'a cupdate set set\<close>
  using valid_empty_cregister_range by blast
typedef 'a QREGISTER = \<open>Collect valid_qregister_range :: 'a qupdate set set\<close>
  using valid_empty_qregister_range by blast
setup_lifting type_definition_CREGISTER
setup_lifting type_definition_QREGISTER

lift_definition CREGISTER_of :: \<open>('a,'b) cregister \<Rightarrow> 'b CREGISTER\<close> is
  \<open>\<lambda>F::('a,'b) cregister. if cregister F then range (apply_cregister F) :: 'b cupdate set else empty_cregister_range\<close>
  by (simp add: valid_empty_cregister_range valid_cregister_range)
lift_definition QREGISTER_of :: \<open>('a,'b) qregister \<Rightarrow> 'b QREGISTER\<close> is
  \<open>\<lambda>F::('a,'b) qregister. if qregister F then range (apply_qregister F) :: 'b qupdate set else empty_qregister_range\<close>
  by (simp add: valid_empty_qregister_range valid_qregister_range)

instantiation CREGISTER :: (type) order begin
lift_definition less_eq_CREGISTER :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> bool\<close> is \<open>(\<subseteq>)\<close>.
lift_definition less_CREGISTER :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> bool\<close> is \<open>(\<subset>)\<close>.
instance
  apply (intro_classes; transfer)
  by auto
end
instantiation QREGISTER :: (type) order begin
lift_definition less_eq_QREGISTER :: \<open>'a QREGISTER \<Rightarrow> 'a QREGISTER \<Rightarrow> bool\<close> is \<open>(\<subseteq>)\<close>.
lift_definition less_QREGISTER :: \<open>'a QREGISTER \<Rightarrow> 'a QREGISTER \<Rightarrow> bool\<close> is \<open>(\<subset>)\<close>.
instance
  apply (intro_classes; transfer)
  by auto
end

lift_definition CREGISTER_unit :: \<open>'a CREGISTER\<close> is empty_cregister_range
  by (simp add: valid_empty_cregister_range)
lift_definition QREGISTER_unit :: \<open>'a QREGISTER\<close> is empty_qregister_range
  by (simp add: valid_empty_qregister_range)
lift_definition CREGISTER_all :: \<open>'a CREGISTER\<close> is UNIV
  by (simp add: valid_cregister_range_UNIV)
lift_definition QREGISTER_all :: \<open>'a QREGISTER\<close> is UNIV
  by (simp add: valid_qregister_range_UNIV)

(* TODO move *)
lemma triple_commutant[simp]: \<open>commutant (commutant (commutant X)) = commutant X\<close>
  by (auto simp: commutant_def)

(* TODO move *)
lemma commutant_adj: \<open>adj ` commutant X = commutant (adj ` X)\<close>
  apply (auto intro!: image_eqI double_adj[symmetric] simp: commutant_def simp flip: adj_cblinfun_compose)
  by (metis adj_cblinfun_compose double_adj)

axiomatization CREGISTER_pair :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> 'a CREGISTER\<close>
lift_definition QREGISTER_pair :: \<open>'a QREGISTER \<Rightarrow> 'a QREGISTER \<Rightarrow> 'a QREGISTER\<close> is
  \<open>\<lambda>\<FF> \<GG> :: 'a qupdate set. commutant (commutant (\<FF> \<union> \<GG>))\<close>
proof -
  fix \<FF> \<GG> :: \<open>'a qupdate set\<close>
  assume \<open>\<FF> \<in> Collect valid_qregister_range\<close>
  then have [simp]: \<open>adj ` \<FF> = \<FF>\<close>
    apply (auto simp: valid_qregister_range_def)
    by force
  assume \<open>\<GG> \<in> Collect valid_qregister_range\<close>
  then have [simp]: \<open>adj ` \<GG> = \<GG>\<close>
    apply (auto simp: valid_qregister_range_def)
    by force
  have \<open>adj ` commutant (commutant (\<FF> \<union> \<GG>)) = commutant (commutant (\<FF> \<union> \<GG>))\<close>
    by (simp add: commutant_adj image_Un)
  then show \<open>commutant (commutant (\<FF> \<union> \<GG>)) \<in> Collect valid_qregister_range\<close>
    by (auto intro!: valid_qregister_rangeI)
qed

definition ccommuting_raw :: \<open>('a cupdate \<Rightarrow> 'c cupdate) \<Rightarrow> ('b cupdate \<Rightarrow> 'c cupdate) \<Rightarrow> bool\<close> where
  \<open>ccommuting_raw F G \<longleftrightarrow> (\<forall>a b. F a \<circ>\<^sub>m G b = G b \<circ>\<^sub>m F a)\<close>
definition qcommuting_raw :: \<open>('a qupdate \<Rightarrow> 'c qupdate) \<Rightarrow> ('b qupdate \<Rightarrow> 'c qupdate) \<Rightarrow> bool\<close> where
  \<open>qcommuting_raw F G \<longleftrightarrow> (\<forall>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a)\<close>

abbreviation \<open>ccompatible_raw \<equiv> Laws_Classical.compatible\<close>
lemmas ccompatible_raw_def = Laws_Classical.compatible_def
abbreviation \<open>qcompatible_raw \<equiv> Laws_Quantum.compatible\<close>
lemmas qcompatible_raw_def = compatible_def

(* definition ccompatible_raw :: \<open>('a cupdate \<Rightarrow> 'c cupdate) \<Rightarrow> ('b cupdate \<Rightarrow> 'c cupdate) \<Rightarrow> bool\<close> where
  \<open>ccompatible_raw F G \<longleftrightarrow> cregister_raw F \<and> cregister_raw G \<and> (\<forall>a b. F a \<circ>\<^sub>m G b = G b \<circ>\<^sub>m F a)\<close>
definition qcompatible_raw :: \<open>('a qupdate \<Rightarrow> 'c qupdate) \<Rightarrow> ('b qupdate \<Rightarrow> 'c qupdate) \<Rightarrow> bool\<close> where
  \<open>qcompatible_raw F G \<longleftrightarrow> qregister_raw F \<and> qregister_raw G \<and> (\<forall>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a)\<close> *)

lift_definition cregister_pair :: \<open>('a,'c) cregister \<Rightarrow> ('b,'c) cregister \<Rightarrow> ('a\<times>'b, 'c) cregister\<close>
  is \<open>\<lambda>F G. if ccompatible_raw F G then Axioms_Classical.register_pair F G else non_cregister_raw\<close>
  by simp
lift_definition qregister_pair :: \<open>('a,'c) qregister \<Rightarrow> ('b,'c) qregister \<Rightarrow> ('a\<times>'b, 'c) qregister\<close>
  is \<open>\<lambda>F G. if qcompatible_raw F G then Axioms_Quantum.register_pair F G else non_qregister_raw\<close>
  by simp

abbreviation (input) \<open>ccompatible F G \<equiv> cregister (cregister_pair F G)\<close>
abbreviation (input) \<open>qcompatible F G \<equiv> qregister (qregister_pair F G)\<close>

lemma ccompatible_def: \<open>ccompatible F G \<longleftrightarrow> cregister F \<and> cregister G \<and> Laws_Classical.compatible (apply_cregister F) (apply_cregister G)\<close>
  by (metis Laws_Classical.compatible_register1 Laws_Classical.compatible_register2 Laws_Classical.pair_is_register cregister.rep_eq cregister_pair.rep_eq non_cregister_raw)

lemma qcompatible_def: \<open>qcompatible F G \<longleftrightarrow> qregister F \<and> qregister G \<and> Laws_Quantum.compatible (apply_qregister F) (apply_qregister G)\<close>
  by (metis Laws_Quantum.compatible_register2 Laws_Quantum.compatible_sym Laws_Quantum.pair_is_register non_qregister_raw qregister.rep_eq qregister_pair.rep_eq)

lemma ccompatibleI: \<open>cregister F \<Longrightarrow> cregister G \<Longrightarrow> (\<And>a b. apply_cregister F a \<circ>\<^sub>m apply_cregister G b = apply_cregister G b \<circ>\<^sub>m apply_cregister F a) \<Longrightarrow> ccompatible F G\<close>
  apply transfer
  by (simp add: Laws_Classical.compatible_def[abs_def])
lemma qcompatibleI: \<open>qregister F \<Longrightarrow> qregister G \<Longrightarrow> (\<And>a b. apply_qregister F a o\<^sub>C\<^sub>L apply_qregister G b = apply_qregister G b o\<^sub>C\<^sub>L apply_qregister F a) \<Longrightarrow> qcompatible F G\<close>
  apply transfer
  by (simp add: Laws_Quantum.compatible_def[abs_def])

lemma ccompatible_commute: 
  assumes \<open>ccompatible F G\<close>
  shows \<open>apply_cregister F a \<circ>\<^sub>m apply_cregister G b = apply_cregister G b \<circ>\<^sub>m apply_cregister F a\<close>
  using Laws_Classical.swap_registers assms ccompatible_def by blast
lemma qcompatible_commute: 
  assumes \<open>qcompatible F G\<close>
  shows \<open>apply_qregister F a o\<^sub>C\<^sub>L apply_qregister G b = apply_qregister G b o\<^sub>C\<^sub>L apply_qregister F a\<close>
  by (metis Laws_Quantum.swap_registers assms non_qregister_raw qregister.rep_eq qregister_pair.rep_eq)

abbreviation \<open>tensor_map \<equiv> Axioms_Classical.tensor_update\<close>

lemma apply_cregister_pair: \<open>ccompatible F G \<Longrightarrow>
  apply_cregister (cregister_pair F G) (tensor_map a b) = apply_cregister F a \<circ>\<^sub>m apply_cregister G b\<close>
  apply transfer
  using Laws_Classical.register_pair_apply Laws_Classical.compatible_register1 Laws_Classical.compatible_register2 non_cregister_raw by auto

lemma apply_qregister_pair: \<open>qcompatible F G \<Longrightarrow>
  apply_qregister (qregister_pair F G) (tensorOp a b) = apply_qregister F a o\<^sub>C\<^sub>L  apply_qregister G b\<close>
  apply transfer
  using Laws_Quantum.register_pair_apply non_qregister_raw by auto

lift_definition CCcompatible :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> bool\<close> is
  \<open>\<lambda>F G. \<forall>a\<in>F. \<forall>b\<in>G. a \<circ>\<^sub>m b = b \<circ>\<^sub>m a\<close>.
lift_definition QQcompatible :: \<open>'a QREGISTER \<Rightarrow> 'a QREGISTER \<Rightarrow> bool\<close> is
  \<open>\<lambda>F G. \<forall>a\<in>F. \<forall>b\<in>G. a o\<^sub>C\<^sub>L b = b o\<^sub>C\<^sub>L a\<close>.

lift_definition Cccompatible :: \<open>'a CREGISTER \<Rightarrow> ('b,'a) cregister \<Rightarrow> bool\<close> is
  \<open>\<lambda>F G. cregister_raw G \<and> (\<forall>a\<in>F. \<forall>b. a \<circ>\<^sub>m G b = G b \<circ>\<^sub>m a)\<close>.
lift_definition Qqcompatible :: \<open>'a QREGISTER \<Rightarrow> ('b,'a) qregister \<Rightarrow> bool\<close> is
  \<open>\<lambda>F G. qregister_raw G \<and> (\<forall>a\<in>F. \<forall>b. a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L a)\<close>.

lemma Cccompatible_CCcompatible: \<open>Cccompatible F G \<longleftrightarrow> cregister G \<and> CCcompatible F (CREGISTER_of G)\<close>
  by (simp add: Cccompatible.rep_eq CCcompatible.rep_eq CREGISTER_of.rep_eq cregister.rep_eq)
lemma Qqcompatible_QQcompatible: \<open>Qqcompatible F G \<longleftrightarrow> qregister G \<and> QQcompatible F (QREGISTER_of G)\<close>
  by (simp add: Qqcompatible.rep_eq QQcompatible.rep_eq QREGISTER_of.rep_eq qregister.rep_eq)

lemma empty_cregisters_same[simp]:
  fixes F :: \<open>('a::{CARD_1,enum},'b) cregister\<close>
  assumes [simp]: \<open>cregister F\<close>
  shows \<open>F = empty_cregister\<close>
proof (rule apply_cregister_inject[THEN iffD1], rule ext)
  fix a :: \<open>'a cupdate\<close>
  consider \<open>a = Map.empty\<close> | \<open>a = Some\<close>
  proof (atomize_elim, cases \<open>a undefined\<close>)
    case None
    then have \<open>a = Map.empty\<close>
      apply (rule_tac ext, subst everything_the_same[of _ undefined])
      by simp
    then show \<open>a = Map.empty \<or> a = Some\<close>
      by simp
  next
    case (Some x)
    then have \<open>a = Some\<close>
      apply (rule_tac ext, subst everything_the_same[of _ undefined])
      by simp
    then show \<open>a = Map.empty \<or> a = Some\<close>
      by simp
  qed
  then show \<open>apply_cregister F a = apply_cregister empty_cregister a\<close>
    apply cases apply auto
    by -
qed
lemma empty_qregisters_same[simp]:
  fixes F :: \<open>('a::{CARD_1,enum},'b) qregister\<close>
  assumes [simp]: \<open>qregister F\<close>
  shows \<open>F = empty_qregister\<close>
proof (rule apply_qregister_inject[THEN iffD1], rule ext)
  fix a :: \<open>'a qupdate\<close>
  define empty :: \<open>('a,'b) qregister\<close> where \<open>empty = empty_qregister\<close>
  have [simp]: \<open>qregister empty\<close>
    using empty_qregister_is_register empty_def by blast

  have [simp]: \<open>clinear (apply_qregister F)\<close> \<open>clinear (apply_qregister empty)\<close>
    by (auto simp add: apply_qregister_bounded_clinear bounded_clinear.clinear)
  have \<open>apply_qregister F a = apply_qregister F (one_dim_iso a *\<^sub>C id_cblinfun)\<close>
    by simp
  also have \<open>\<dots> = one_dim_iso a *\<^sub>C apply_qregister F (id_cblinfun)\<close>
    by (metis \<open>clinear (apply_qregister F)\<close> complex_vector.linear_scale)
  also have \<open>\<dots> = one_dim_iso a *\<^sub>C id_cblinfun\<close>
    by (metis apply_qregister_of_id assms(1))
  also have \<open>\<dots> = one_dim_iso a *\<^sub>C apply_qregister empty (id_cblinfun)\<close>
    by (metis \<open>qregister empty\<close> apply_qregister_of_id)
  also have \<open>\<dots> = apply_qregister empty (one_dim_iso a *\<^sub>C id_cblinfun)\<close>
    by (metis \<open>clinear (apply_qregister empty)\<close> complex_vector.linear_scale)
  also have \<open>\<dots> = apply_qregister empty a\<close>
    by simp
  finally show \<open>apply_qregister F a = apply_qregister empty a\<close>
    by -
qed

lemma CCcompatible_sym: \<open>CCcompatible F G \<Longrightarrow> CCcompatible G F\<close> for F G :: \<open>'a CREGISTER\<close>
  by (auto simp: CCcompatible_def)
lemma QQcompatible_sym: \<open>QQcompatible F G \<Longrightarrow> QQcompatible G F\<close> for F G :: \<open>'a QREGISTER\<close>
  by (auto simp: QQcompatible_def)

lemma ccompatible_CCcompatible: \<open>ccompatible F G \<longleftrightarrow> cregister F \<and> cregister G \<and> CCcompatible (CREGISTER_of F) (CREGISTER_of G)\<close>
  apply (transfer fixing: F G)
  apply (auto simp add: Laws_Classical.compatible_def ccompatible_def)
  by (simp_all add: cregister.rep_eq)
lemma qcompatible_QQcompatible: \<open>qcompatible F G \<longleftrightarrow> qregister F \<and> qregister G \<and> QQcompatible (QREGISTER_of F) (QREGISTER_of G)\<close>
  apply (transfer fixing: F G)
  apply (auto simp add: qcompatible_commute qcompatible_def)
  by (simp add: Laws_Quantum.compatible_def qregister.rep_eq)

lemma CCcompatible_CREGISTER_ofI[simp]: \<open>ccompatible F G \<Longrightarrow> CCcompatible (CREGISTER_of F) (CREGISTER_of G)\<close>
  using ccompatible_CCcompatible by auto
lemma QQcompatible_QREGISTER_ofI[simp]: \<open>qcompatible F G \<Longrightarrow> QQcompatible (QREGISTER_of F) (QREGISTER_of G)\<close>
  using qcompatible_QQcompatible by auto

lemma ccompatible_sym: \<open>ccompatible F G \<Longrightarrow> ccompatible G F\<close> for F :: \<open>('a,'c) cregister\<close> and G :: \<open>('b,'c) cregister\<close>
  by (auto intro: CCcompatible_sym simp: ccompatible_CCcompatible)
lemma qcompatible_sym: \<open>qcompatible F G \<Longrightarrow> qcompatible G F\<close> for F :: \<open>('a,'c) qregister\<close> and G :: \<open>('b,'c) qregister\<close>
  by (auto intro: QQcompatible_sym simp: qcompatible_QQcompatible)

lemma ccompatible3: \<open>ccompatible (cregister_pair F G) H \<longleftrightarrow> ccompatible F G \<and> ccompatible F H \<and> ccompatible G H\<close>
  unfolding ccompatible_def
  apply transfer
  apply (auto simp: non_cregister_raw)
  apply (metis Laws_Classical.compatible_comp_left Laws_Classical.register_Fst Laws_Classical.register_pair_Fst)
  by (metis Laws_Classical.compatible_comp_left Laws_Classical.register_Snd Laws_Classical.register_pair_Snd)
lemma qcompatible3: \<open>qcompatible (qregister_pair F G) H \<longleftrightarrow> qcompatible F G \<and> qcompatible F H \<and> qcompatible G H\<close>
  unfolding qcompatible_def
  apply transfer
  apply (auto simp: non_qregister_raw)
  apply (metis Laws_Quantum.compatible_comp_left Laws_Quantum.register_Fst Laws_Quantum.register_pair_Fst)
  by (metis Laws_Quantum.compatible_comp_left Laws_Quantum.register_Snd Laws_Quantum.register_pair_Snd)

lemma ccompatible3': \<open>ccompatible H (cregister_pair F G) \<longleftrightarrow> ccompatible F G \<and> ccompatible H F \<and> ccompatible H G\<close>
  by (metis ccompatible3 ccompatible_sym)
lemma qcompatible3': \<open>qcompatible H (qregister_pair F G) \<longleftrightarrow> qcompatible F G \<and> qcompatible H F \<and> qcompatible H G\<close>
  by (metis qcompatible3 qcompatible_sym)

lemma compatible_empty_cregister_raw:
  \<open>cregister_raw Q \<Longrightarrow> ccompatible_raw Q empty_cregister_raw\<close>
  apply (simp add: ccompatible_raw_def cregister_raw_empty_cregister_raw)
  apply (auto intro!: ext simp add: empty_cregister_raw_def register_from_getter_setter_def[abs_def] map_comp_def)
  apply (case_tac \<open>Q a k\<close>)
  apply (case_tac \<open>b undefined\<close>)
  apply auto
  apply (case_tac \<open>b undefined\<close>)
  by auto

lemma ccompatible_empty[simp]: \<open>ccompatible Q empty_cregister \<longleftrightarrow> cregister Q\<close>
  apply transfer
  apply (auto simp: compatible_empty_cregister_raw non_cregister_raw)
  by (auto simp: ccompatible_raw_def non_cregister_raw)
lemma qcompatible_empty[simp]: \<open>qcompatible Q empty_qregister \<longleftrightarrow> qregister Q\<close>
  apply transfer
  apply (auto simp: non_qregister_raw)
  by (auto simp: qcompatible_raw_def non_qregister_raw)

lemma ccompatible_empty'[simp]: \<open>ccompatible empty_cregister Q \<longleftrightarrow> cregister Q\<close>
  by (metis ccompatible_empty ccompatible_sym)
lemma qcompatible_empty'[simp]: \<open>qcompatible empty_qregister Q \<longleftrightarrow> qregister Q\<close>
  by (meson qcompatible_empty qcompatible_sym)

lemma ccompatible_register1: \<open>ccompatible F G \<Longrightarrow> cregister F\<close>
  apply transfer
  by (auto simp add: ccompatible_raw_def non_cregister_raw non_cregister_raw)
lemma ccompatible_register2: \<open>ccompatible F G \<Longrightarrow> cregister G\<close>
  apply transfer
  by (auto simp add: ccompatible_raw_def non_cregister_raw non_cregister_raw)
lemma qcompatible_register1: \<open>qcompatible F G \<Longrightarrow> qregister F\<close>
  apply transfer
  by (auto simp add: qcompatible_raw_def non_qregister_raw non_qregister_raw)
lemma qcompatible_register2: \<open>qcompatible F G \<Longrightarrow> qregister G\<close>
  apply transfer
  by (auto simp add: qcompatible_raw_def non_qregister_raw non_qregister_raw)

lemma ccompatible_non_cregister1[simp]: \<open>\<not> ccompatible non_cregister F\<close>
  apply transfer by (simp add: non_cregister_raw ccompatible_raw_def)
lemma ccompatible_non_cregister2[simp]: \<open>\<not> ccompatible F non_cregister\<close>
  apply transfer by (simp add: non_cregister_raw ccompatible_raw_def)
lemma qcompatible_non_qregister1[simp]: \<open>\<not> qcompatible non_qregister F\<close>
  apply transfer by (simp add: non_qregister_raw qcompatible_raw_def)
lemma qcompatible_non_qregister2[simp]: \<open>\<not> qcompatible F non_qregister\<close>
  apply transfer by (simp add: non_qregister_raw qcompatible_raw_def)

lift_definition cFst :: \<open>('a, 'a\<times>'b) cregister\<close> is \<open>Laws_Classical.Fst\<close>
  by simp
lemma cFst_register[simp]: \<open>cregister cFst\<close>
  apply transfer by simp
lift_definition qFst :: \<open>('a, 'a\<times>'b) qregister\<close> is \<open>Laws_Quantum.Fst\<close>
  by simp
lemma qFst_register[simp]: \<open>qregister qFst\<close>
  apply transfer by simp
lift_definition cSnd :: \<open>('b, 'a\<times>'b) cregister\<close> is \<open>Laws_Classical.Snd\<close>
  by simp
lemma cSnd_register[simp]: \<open>cregister cSnd\<close>
  apply transfer by simp
lift_definition qSnd :: \<open>('b, 'a\<times>'b) qregister\<close> is \<open>Laws_Quantum.Snd\<close>
  by simp
lemma qSnd_register[simp]: \<open>qregister qSnd\<close>
  apply transfer by simp

lemma ccompatible_Fst_Snd[simp]: \<open>ccompatible cFst cSnd\<close>
  by (simp add: cFst.rep_eq cSnd.rep_eq ccompatible_def)
lemma qcompatible_Fst_Snd[simp]: \<open>qcompatible qFst qSnd\<close>
  by (simp add: qFst.rep_eq qSnd.rep_eq qcompatible_def)

lift_definition cregister_chain :: \<open>('b,'c) cregister \<Rightarrow> ('a,'b) cregister \<Rightarrow> ('a,'c) cregister\<close>
  is \<open>\<lambda>F G. if cregister_raw F \<and> cregister_raw G then F o G else non_cregister_raw\<close>
  by auto
lift_definition qregister_chain :: \<open>('b,'c) qregister \<Rightarrow> ('a,'b) qregister \<Rightarrow> ('a,'c) qregister\<close>
  is \<open>\<lambda>F G. if qregister_raw F \<and> qregister_raw G then F o G else non_qregister_raw\<close>
  by (metis (no_types, lifting) register_comp UnCI mem_Collect_eq singletonI)

lemmas cregister_raw_chain = Axioms_Classical.register_comp
lemmas qregister_raw_chain = register_comp

lemma cregister_chain_apply[simp]: \<open>apply_cregister (cregister_chain F G) = apply_cregister F o apply_cregister G\<close>
  apply (rule ext) apply transfer
  by (auto simp: non_cregister_raw_def cregister_raw_empty)
lemma qregister_chain_apply: \<open>apply_qregister (qregister_chain F G) = apply_qregister F o apply_qregister G\<close>
  apply (rule ext) apply transfer
  by (auto simp: non_qregister_raw_def qregister_raw_0)
(* We limit this simplification rule to the case where F is neither Fst nor Snd because those cases are used commonly to encode indexed variables *)
lemma qregister_chain_apply_simp[simp]:
  assumes \<open>NO_MATCH qFst F\<close> \<open>NO_MATCH qSnd F\<close>
  shows \<open>apply_qregister (qregister_chain F G) = apply_qregister F o apply_qregister G\<close>
  by (rule qregister_chain_apply)

lemma cregister_id_chain[simp]: \<open>cregister_chain cregister_id F = F\<close>
  apply transfer by auto
lemma qregister_id_chain[simp]: \<open>qregister_chain qregister_id F = F\<close>
  apply transfer by auto
lemma cregister_chain_id[simp]: \<open>cregister_chain F cregister_id = F\<close>
  apply transfer by auto
lemma qregister_chain_id[simp]: \<open>qregister_chain F qregister_id = F\<close>
  apply transfer by auto

lemma cregister_chain_non_register1[simp]: \<open>cregister_chain non_cregister F = non_cregister\<close>
  apply transfer by (auto simp add: non_cregister_raw)
lemma cregister_chain_non_register2[simp]: \<open>cregister_chain F non_cregister = non_cregister\<close>
  apply transfer by (auto simp add: non_cregister_raw)
lemma qregister_chain_non_register1[simp]: \<open>qregister_chain non_qregister F = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)
lemma qregister_chain_non_register2[simp]: \<open>qregister_chain F non_qregister = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)

lemma cregister_chain_assoc: \<open>cregister_chain (cregister_chain F G) H = cregister_chain F (cregister_chain G H)\<close>
  apply (cases \<open>cregister F\<close>; cases \<open>cregister G\<close>; cases \<open>cregister H\<close>)
  apply (simp_all add: non_cregister)
  apply transfer
  by (auto simp add: cregister_raw_chain)
lemma qregister_chain_assoc: \<open>qregister_chain (qregister_chain F G) H = qregister_chain F (qregister_chain G H)\<close>
  apply (cases \<open>qregister F\<close>; cases \<open>qregister G\<close>; cases \<open>qregister H\<close>)
  apply (simp_all add: non_qregister)
  apply transfer
  by (auto simp add: qregister_raw_chain)

lemma cregister_chain_is_cregister[simp]: \<open>cregister (cregister_chain F G) \<longleftrightarrow> cregister F \<and> cregister G\<close>
  apply transfer
  by (auto simp: non_cregister_raw cregister_raw_chain)
lemma qregister_chain_is_qregister[simp]: \<open>qregister (qregister_chain F G) \<longleftrightarrow> qregister F \<and> qregister G\<close>
  apply transfer
  by (auto simp: non_qregister_raw qregister_raw_chain)

lemma cregister_chain_pair_Fst[simp]: \<open>ccompatible F G \<Longrightarrow> cregister_chain (cregister_pair F G) cFst = F\<close>
  unfolding ccompatible_def apply transfer
  by (simp add: Laws_Classical.register_pair_Fst)
lemma qregister_chain_pair_Fst[simp]: \<open>qcompatible F G \<Longrightarrow> qregister_chain (qregister_pair F G) qFst = F\<close>
  unfolding qcompatible_def apply transfer
  by (simp add: Laws_Quantum.register_pair_Fst)

lemma cregister_chain_pair_Fst_chain[simp]:
  assumes \<open>ccompatible F G\<close>
  shows \<open>cregister_chain (cregister_pair F G) (cregister_chain cFst H) = cregister_chain F H\<close>
  by (metis cregister_chain_pair_Fst assms cregister_chain_assoc)
lemma qregister_chain_pair_Fst_chain[simp]:
  assumes \<open>qcompatible F G\<close>
  shows \<open>qregister_chain (qregister_pair F G) (qregister_chain qFst H) = qregister_chain F H\<close>
  by (metis qregister_chain_pair_Fst assms qregister_chain_assoc)

lemma cregister_chain_pair_Snd[simp]: \<open>ccompatible F G \<Longrightarrow> cregister_chain (cregister_pair F G) cSnd = G\<close>
  unfolding ccompatible_def apply transfer
  by (simp add: Laws_Classical.register_pair_Snd)
lemma qregister_chain_pair_Snd[simp]: \<open>qcompatible F G \<Longrightarrow> qregister_chain (qregister_pair F G) qSnd = G\<close>
  unfolding qcompatible_def apply transfer
  by (simp add: Laws_Quantum.register_pair_Snd)

lemma cregister_chain_pair_Snd_chain[simp]:
  assumes \<open>ccompatible F G\<close>
  shows \<open>cregister_chain (cregister_pair F G) (cregister_chain cSnd H) = cregister_chain G H\<close>
  by (metis cregister_chain_pair_Snd assms cregister_chain_assoc)
lemma qregister_chain_pair_Snd_chain[simp]:
  assumes \<open>qcompatible F G\<close>
  shows \<open>qregister_chain (qregister_pair F G) (qregister_chain qSnd H) = qregister_chain G H\<close>
  by (metis qregister_chain_pair_Snd assms qregister_chain_assoc)


lemma qregister_chain_empty_right[simp]: \<open>qregister F \<Longrightarrow> qregister_chain F empty_qregister = empty_qregister\<close>
  apply (rule empty_qregisters_same) by auto
lemma qregister_chain_empty_left[simp]: \<open>qregister F \<Longrightarrow> qregister_chain empty_qregister F = empty_qregister\<close>
  apply (rule empty_qregisters_same) by auto

lemma ccompatible_comp_left[simp]: "ccompatible F G \<Longrightarrow> cregister H \<Longrightarrow> ccompatible (cregister_chain F H) G"
  unfolding ccompatible_def apply transfer by auto
lemma qcompatible_comp_left[simp]: "qcompatible F G \<Longrightarrow> qregister H \<Longrightarrow> qcompatible (qregister_chain F H) G"
  unfolding qcompatible_def apply transfer by auto

lemma ccompatible_comp_right[simp]: "ccompatible F G \<Longrightarrow> cregister H \<Longrightarrow> ccompatible F (cregister_chain G H)"
  by (meson ccompatible_comp_left ccompatible_sym)
lemma qcompatible_comp_right[simp]: "qcompatible F G \<Longrightarrow> qregister H \<Longrightarrow> qcompatible F (qregister_chain G H)"
  by (meson qcompatible_comp_left qcompatible_sym)

lemma Cccompatible_comp_right[simp]: "Cccompatible F G \<Longrightarrow> cregister H \<Longrightarrow> Cccompatible F (cregister_chain G H)"
  apply transfer by auto
lemma Qqcompatible_comp_right[simp]: "Qqcompatible F G \<Longrightarrow> qregister H \<Longrightarrow> Qqcompatible F (qregister_chain G H)"
  apply transfer by auto

lemmas ccompatible_Snd_Fst[simp] = ccompatible_Fst_Snd[THEN ccompatible_sym]
lemmas qcompatible_Snd_Fst[simp] = qcompatible_Fst_Snd[THEN qcompatible_sym]

lemma commutant_empty[simp]: \<open>commutant {} = UNIV\<close>
  by (simp add: commutant_def)

lemma closedin_vimage:
  assumes \<open>closedin U S\<close>
  assumes \<open>continuous_map T U f\<close>
  shows \<open>closedin T (topspace T \<inter> (f -` S))\<close>
  by (meson assms(1) assms(2) continuous_map_closedin_preimage_eq)

lemma join_forall: \<open>(\<forall>x. P x) \<and> (\<forall>x. Q x) \<longleftrightarrow> (\<forall>x. P x \<and> Q x)\<close>
  by auto

(* TODO move *)
lemma closedin_singleton: 
  assumes \<open>hausdorff T\<close> and \<open>x \<in> topspace T\<close>
  shows \<open>closedin T {x}\<close>
proof -
  obtain U where openU: \<open>openin T (U y)\<close> and x_not_U: \<open>x \<notin> U y\<close> and yU: \<open>y \<in> U y\<close> if \<open>x \<noteq> y\<close> and \<open>y \<in> topspace T\<close> for y
    apply atomize_elim unfolding join_forall apply (rule choice)
    using assms(1)[unfolded hausdorff_def, rule_format, OF assms(2)]
    by auto
  have \<open>topspace T - {x} = (\<Union>y\<in>topspace T - {x}. U y)\<close>
    using yU openU x_not_U apply auto
    using openin_subset by fastforce
  also have \<open>openin T \<dots>\<close>
    using openU by fastforce
  finally have \<open>openin T (topspace T - {x})\<close>
    by -
  then show ?thesis
    using assms(2) closedin_def by blast
qed

(* TODO move *)
lemma continuous_map_scaleC_weak_star'[continuous_intros]:
  assumes \<open>continuous_map T weak_star_topology f\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. scaleC c (f x))\<close>
  using continuous_map_compose[OF assms continuous_map_scaleC_weak_star]
  by (simp add: o_def)

(* TODO move *)
lemma continuous_map_uminus_weak_star[continuous_intros]:
  assumes \<open>continuous_map T weak_star_topology f\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. - f x)\<close>
  apply (subst scaleC_minus1_left[abs_def,symmetric])
  by (intro continuous_map_scaleC_weak_star' assms)

(* TODO move *)
lemma continuous_map_add_weak_star[continuous_intros]: 
  assumes \<open>continuous_map T weak_star_topology f\<close>
  assumes \<open>continuous_map T weak_star_topology g\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. f x + g x)\<close>
proof -
  have \<open>continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x))\<close> if \<open>trace_class t\<close> for t
    using assms(1) continuous_on_weak_star_topo_iff_coordinatewise that by auto
  moreover have \<open>continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L g x))\<close> if \<open>trace_class t\<close> for t
    using assms(2) continuous_on_weak_star_topo_iff_coordinatewise that by auto
  ultimately show ?thesis
    by (auto intro!: continuous_map_add simp add: continuous_on_weak_star_topo_iff_coordinatewise
        cblinfun_compose_add_right trace_class_comp_left trace_plus)
qed

(* TODO move *)
lemma continuous_map_minus_weak_star[continuous_intros]: 
  assumes \<open>continuous_map T weak_star_topology f\<close>
  assumes \<open>continuous_map T weak_star_topology g\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. f x - g x)\<close>
  apply (subst diff_conv_add_uminus)
  by (intro assms continuous_intros)

(* TODO move *)
lemma commutant_weak_star_closed[simp]: \<open>closedin weak_star_topology (commutant X)\<close>
proof -
  have comm_inter: \<open>commutant X = (\<Inter>x\<in>X. commutant {x})\<close>
    by (auto simp: commutant_def)
  have comm_x: \<open>commutant {x} = (\<lambda>y. x o\<^sub>C\<^sub>L y - y o\<^sub>C\<^sub>L x) -` {0}\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    by (auto simp add: commutant_def vimage_def)
  have cont: \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>y. x o\<^sub>C\<^sub>L y - y o\<^sub>C\<^sub>L x)\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    apply (rule continuous_intros)
    by (simp_all add: continuous_map_left_comp_weak_star continuous_map_right_comp_weak_star)
  have \<open>closedin weak_star_topology ((\<lambda>y. x o\<^sub>C\<^sub>L y - y o\<^sub>C\<^sub>L x) -` {0})\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    using closedin_vimage[where U=\<open>weak_star_topology\<close> and S=\<open>{0}\<close> and T=weak_star_topology]
    using cont by (auto simp add: closedin_singleton)
  then show ?thesis
    apply (cases \<open>X = {}\<close>)
    using closedin_topspace[of weak_star_topology]
    by (auto simp add: comm_inter comm_x)
qed

lemma cspan_in_double_commutant: \<open>cspan X \<subseteq> commutant (commutant X)\<close>
  by (simp add: complex_vector.span_minimal)

lemma weak_star_closure_in_double_commutant: \<open>weak_star_topology closure_of X \<subseteq> commutant (commutant X)\<close>
  by (simp add: closure_of_minimal)

lemma weak_star_closure_cspan_in_double_commutant: \<open>weak_star_topology closure_of cspan X \<subseteq> commutant (commutant X)\<close>
  by (simp add: closure_of_minimal cspan_in_double_commutant)

lemma CREGISTER_of_cregister_pair: \<open>ccompatible F G \<Longrightarrow> CREGISTER_of (cregister_pair F G) = CREGISTER_pair (CREGISTER_of F) (CREGISTER_of G)\<close>
  sorry
lemma QREGISTER_of_qregister_pair: \<open>QREGISTER_of (qregister_pair F G) = QREGISTER_pair (QREGISTER_of F) (QREGISTER_of G)\<close> 
  if [simp]: \<open>qcompatible F G\<close>
proof -
  have [simp]: \<open>qregister F\<close> \<open>qregister G\<close>
    using qcompatible_register1 qcompatible_register2 that by blast+
  define F' G' where FG'_def: \<open>F' = Rep_QREGISTER (QREGISTER_of F)\<close> \<open>G' = Rep_QREGISTER (QREGISTER_of G)\<close>

  have 1: \<open>Rep_QREGISTER (QREGISTER_pair (QREGISTER_of F) (QREGISTER_of G)) \<subseteq> Rep_QREGISTER (QREGISTER_of (qregister_pair F G))\<close>
  proof -
    have \<open>F' \<subseteq> Rep_QREGISTER (QREGISTER_of (qregister_pair F G))\<close>
      apply (auto simp add: FG'_def QREGISTER_of.rep_eq)
      apply (rule range_eqI[where x=\<open>_ \<otimes>\<^sub>o id_cblinfun\<close>])
      by (simp add: apply_qregister_pair)
    moreover have \<open>G' \<subseteq> Rep_QREGISTER (QREGISTER_of (qregister_pair F G))\<close>
      apply (auto simp add: FG'_def QREGISTER_of.rep_eq)
      apply (rule range_eqI[where x=\<open>id_cblinfun \<otimes>\<^sub>o _\<close>])
      by (simp add: apply_qregister_pair)
    ultimately have \<open>F' \<union> G' \<subseteq> Rep_QREGISTER (QREGISTER_of (qregister_pair F G))\<close>
      by (simp add: FG'_def)
    then have \<open>commutant (commutant (F' \<union> G')) \<subseteq> commutant (commutant (Rep_QREGISTER (QREGISTER_of (qregister_pair F G))))\<close>
      by (intro commutant_antimono)
    also have \<open>\<dots> = Rep_QREGISTER (QREGISTER_of (qregister_pair F G))\<close>
      using Rep_QREGISTER valid_qregister_range_def by auto
    finally show ?thesis
      by (simp add: QREGISTER_pair.rep_eq FG'_def)
  qed
  have 2: \<open>Rep_QREGISTER (QREGISTER_of (qregister_pair F G)) \<subseteq> Rep_QREGISTER (QREGISTER_pair (QREGISTER_of F) (QREGISTER_of G))\<close>
  proof -
    have \<open>Rep_QREGISTER (QREGISTER_of (qregister_pair F G)) = apply_qregister (qregister_pair F G) ` UNIV\<close>
      by (simp add: QREGISTER_of.rep_eq)
    also have \<open>\<dots> = apply_qregister (qregister_pair F G) ` 
                    (weak_star_topology closure_of cspan {butterket \<xi> \<eta> |\<xi> \<eta>. True})\<close>
      apply (subst butterkets_weak_star_dense) by simp
    also have \<open>\<dots> \<subseteq> weak_star_topology closure_of 
                        apply_qregister (qregister_pair F G) ` cspan {butterket \<xi> \<eta> |\<xi> \<eta>. True}\<close>
      apply (rule continuous_map_image_closure_subset)
      using qregister.rep_eq that weak_star_cont_register by blast
    also have \<open>\<dots> = weak_star_topology closure_of cspan
                        (apply_qregister (qregister_pair F G) ` {butterket \<xi> \<eta> |\<xi> \<eta>. True})\<close>
      apply (subst complex_vector.linear_span_image)
      by simp_all
    also have \<open>\<dots> = weak_star_topology closure_of cspan
                        (apply_qregister (qregister_pair F G) ` {butterket (a,b) (c,d) |a b c d. True})\<close>
      apply (rule arg_cong[where x=\<open>{butterket \<xi> \<eta> |\<xi> \<eta>. True}\<close>])
      by auto
    also have \<open>\<dots> = weak_star_topology closure_of cspan
                        {apply_qregister F (butterket a c) o\<^sub>C\<^sub>L apply_qregister G (butterket b d) |a b c d. True}\<close>
      apply (subst set_compr_4_image_collect)
      apply (subst set_compr_4_image_collect)
      by (simp add: image_image case_prod_unfold apply_qregister_pair
          flip: tensor_ell2_ket tensor_butterfly)
    also have \<open>\<dots> \<subseteq> weak_star_topology closure_of cspan
                        {f o\<^sub>C\<^sub>L g | f g. f \<in> F' \<and> g \<in> G'}\<close>
      apply (rule closure_of_mono)
      apply (rule complex_vector.span_mono)
      by (auto simp: FG'_def QREGISTER_of.rep_eq)
    also have \<open>\<dots> \<subseteq> commutant (commutant {f o\<^sub>C\<^sub>L g | f g. f \<in> F' \<and> g \<in> G'})\<close>
      by (rule weak_star_closure_cspan_in_double_commutant)
    also have \<open>\<dots> \<subseteq> commutant (commutant (F' \<union> G'))\<close>
      apply (rule commutant_antimono)
      apply (auto simp: commutant_def)
      by (metis (no_types, lifting) Un_iff lift_cblinfun_comp(2))
    also have \<open>\<dots> = Rep_QREGISTER (QREGISTER_pair (QREGISTER_of F) (QREGISTER_of G))\<close>
      by (simp add: QREGISTER_pair.rep_eq flip: FG'_def)
    finally show ?thesis
      by -
  qed

  from 1 2 show ?thesis
    by (auto intro!: antisym simp add: less_eq_QREGISTER_def)
qed

lemma ccompatible3I[simp]: \<open>ccompatible F G \<Longrightarrow> ccompatible G H \<Longrightarrow> ccompatible F H \<Longrightarrow> ccompatible (cregister_pair F G) H\<close>
  by (simp add: ccompatible3)
lemma qcompatible3I[simp]: \<open>qcompatible F G \<Longrightarrow> qcompatible G H \<Longrightarrow> qcompatible F H \<Longrightarrow> qcompatible (qregister_pair F G) H\<close>
  by (simp add: qcompatible3)
lemma ccompatible3I'[simp]: \<open>ccompatible F G \<Longrightarrow> ccompatible F H \<Longrightarrow> ccompatible G H \<Longrightarrow> ccompatible F (cregister_pair G H)\<close>
  by (simp add: ccompatible3')
lemma qcompatible3I'[simp]: \<open>qcompatible F G \<Longrightarrow> qcompatible F H \<Longrightarrow> qcompatible G H \<Longrightarrow> qcompatible F (qregister_pair G H)\<close>
  by (simp add: qcompatible3')

lemma CCcompatible3I[simp]: \<open>CCcompatible F G \<Longrightarrow> CCcompatible G H \<Longrightarrow> CCcompatible F H \<Longrightarrow> CCcompatible (CREGISTER_pair F G) H\<close>
  sorry
lemma QQcompatible3I[simp]: \<open>QQcompatible F G \<Longrightarrow> QQcompatible G H \<Longrightarrow> QQcompatible F H \<Longrightarrow> QQcompatible (QREGISTER_pair F G) H\<close> 
  apply transfer apply (auto simp: commutant_def)
  by (metis Un_iff)
lemma CCcompatible3I'[simp]: \<open>CCcompatible F G \<Longrightarrow> CCcompatible F H \<Longrightarrow> CCcompatible G H \<Longrightarrow> CCcompatible F (CREGISTER_pair G H)\<close> 
  using CCcompatible3I CCcompatible_sym by blast
lemma QQcompatible3I'[simp]: \<open>QQcompatible F G \<Longrightarrow> QQcompatible F H \<Longrightarrow> QQcompatible G H \<Longrightarrow> QQcompatible F (QREGISTER_pair G H)\<close> 
  using QQcompatible3I QQcompatible_sym by blast

lemma Cccompatible3I[simp]: \<open>CCcompatible F G \<Longrightarrow> Cccompatible G H \<Longrightarrow> Cccompatible F H \<Longrightarrow> Cccompatible (CREGISTER_pair F G) H\<close>
  by (simp add: Cccompatible_CCcompatible)
lemma Qqcompatible3I[simp]: \<open>QQcompatible F G \<Longrightarrow> Qqcompatible G H \<Longrightarrow> Qqcompatible F H \<Longrightarrow> Qqcompatible (QREGISTER_pair F G) H\<close>
  by (simp add: Qqcompatible_QQcompatible)
lemma Cccompatible3I'[simp]: \<open>Cccompatible F G \<Longrightarrow> Cccompatible F H \<Longrightarrow> ccompatible G H \<Longrightarrow> Cccompatible F (cregister_pair G H)\<close>
  by (simp add: Cccompatible_CCcompatible CREGISTER_of_cregister_pair)
lemma Qqcompatible3I'[simp]: \<open>Qqcompatible F G \<Longrightarrow> Qqcompatible F H \<Longrightarrow> qcompatible G H \<Longrightarrow> Qqcompatible F (qregister_pair G H)\<close>
  by (simp add: Qqcompatible_QQcompatible QREGISTER_of_qregister_pair)

(* TODO: (and also for quantum, also for COMPATIBLE)
lemma ccompatible_register_tensor[simp]: \<open>ccompatible F F' \<Longrightarrow> ccompatible G G' \<Longrightarrow> ccompatible (cregister_tensor F G) (cregister_tensor F' G')\<close> *)

definition \<open>cswap = cregister_pair cSnd cFst\<close>
definition \<open>qswap = qregister_pair qSnd qFst\<close>

lemma cregister_cswap[simp]: \<open>cregister cswap\<close>
  by (simp add: ccompatible_sym cswap_def)
lemma qregister_qswap[simp]: \<open>qregister qswap\<close>
  by (simp add: qcompatible_sym qswap_def)

lemma cregister_pair_cnonregister1[simp]: \<open>cregister_pair non_cregister F = non_cregister\<close>
  using non_cregister ccompatible_non_cregister1 by blast
lemma qregister_pair_qnonregister1[simp]: \<open>qregister_pair non_qregister F = non_qregister\<close>
  using non_qregister qcompatible_non_qregister1 by blast

lemma cregister_pair_cnonregister2[simp]: \<open>cregister_pair F non_cregister = non_cregister\<close>
  using non_cregister ccompatible_non_cregister2 by blast
lemma qregister_pair_qnonregister2[simp]: \<open>qregister_pair F non_qregister = non_qregister\<close>
  using non_qregister qcompatible_non_qregister2 by blast

lemma inj_cregister: \<open>inj (apply_cregister F)\<close> if \<open>cregister F\<close>
  using that apply transfer
  by (simp add: cregister_raw_inj)
lemma inj_qregister: \<open>inj (apply_qregister F)\<close> if \<open>qregister F\<close>
  using that apply transfer
  by (simp add: qregister_raw_inj)

lemma apply_non_qregister[simp]: \<open>apply_qregister non_qregister x = 0\<close>
  by (simp add: non_qregister.rep_eq non_qregister_raw_def)

lemma cregister_compose: \<open>apply_cregister F (a \<circ>\<^sub>m b) = apply_cregister F a \<circ>\<^sub>m apply_cregister F b\<close>
  apply (transfer fixing: a b)
  by (auto simp: non_cregister_raw_def Axioms_Classical.register_mult)
lemma qregister_compose: \<open>apply_qregister F (a o\<^sub>C\<^sub>L b) = apply_qregister F a o\<^sub>C\<^sub>L apply_qregister F b\<close>
  apply (transfer fixing: a b)
  by (auto simp: non_qregister_raw_def Axioms_Quantum.register_mult)

lemma not_ccompatible_chain: 
  assumes \<open>\<not> ccompatible G H\<close>
  shows \<open>\<not> ccompatible (cregister_chain F G) (cregister_chain F H)\<close>
proof (rule notI)
  assume asm: \<open>ccompatible (cregister_chain F G) (cregister_chain F H)\<close>
  consider (FGH) \<open>cregister F\<close> \<open>cregister G\<close> \<open>cregister H\<close>
    | (nF) \<open>\<not> cregister F\<close> | (nG) \<open>\<not> cregister G\<close> | (nH) \<open>\<not> cregister H\<close>
    by auto
  then show False
  proof cases
    case FGH
    have \<open>apply_cregister F (apply_cregister G a \<circ>\<^sub>m apply_cregister H b) = apply_cregister F (apply_cregister H b \<circ>\<^sub>m apply_cregister G a)\<close> for a b
      using ccompatible_commute[OF asm]
      by (simp add: cregister_compose)
    moreover from FGH have \<open>inj (apply_cregister F)\<close>
      by (simp add: inj_cregister)
    ultimately have \<open>apply_cregister G a \<circ>\<^sub>m apply_cregister H b = apply_cregister H b \<circ>\<^sub>m apply_cregister G a\<close> for a b
      by (simp add: injD)
    then have \<open>ccompatible G H\<close>
      apply (rule_tac ccompatibleI)
      using FGH by auto
    with assms show False
      by simp
  next
    case nF with asm assms show ?thesis by (simp add: non_cregister)
  next
    case nG with asm assms show ?thesis by (simp add: non_cregister)
  next
    case nH with asm assms show ?thesis by (simp add: non_cregister)
  qed
qed
lemma not_qcompatible_chain: 
  assumes \<open>\<not> qcompatible G H\<close>
  shows \<open>\<not> qcompatible (qregister_chain F G) (qregister_chain F H)\<close>
proof (rule notI)
  assume asm: \<open>qcompatible (qregister_chain F G) (qregister_chain F H)\<close>
  consider (FGH) \<open>qregister F\<close> \<open>qregister G\<close> \<open>qregister H\<close>
    | (nF) \<open>\<not> qregister F\<close> | (nG) \<open>\<not> qregister G\<close> | (nH) \<open>\<not> qregister H\<close>
    by auto
  then show False
  proof cases
    case FGH
    have \<open>apply_qregister F (apply_qregister G a o\<^sub>C\<^sub>L apply_qregister H b) = apply_qregister F (apply_qregister H b o\<^sub>C\<^sub>L apply_qregister G a)\<close> for a b
      using qcompatible_commute[OF asm]
      by (simp add: qregister_compose)
    moreover from FGH have \<open>inj (apply_qregister F)\<close>
      by (simp add: inj_qregister)
    ultimately have \<open>apply_qregister G a o\<^sub>C\<^sub>L apply_qregister H b = apply_qregister H b o\<^sub>C\<^sub>L apply_qregister G a\<close> for a b
      by (simp add: injD)
    then have \<open>qcompatible G H\<close>
      apply (rule_tac qcompatibleI)
      using FGH by auto
    with assms show False
      by simp
  next
    case nF with asm assms show ?thesis by (simp add: non_qregister)
  next
    case nG with asm assms show ?thesis by (simp add: non_qregister)
  next
    case nH with asm assms show ?thesis by (simp add: non_qregister)
  qed
qed

(* TODO: compatibility condition can be omitted *)
lemma cregister_chain_pair:
  shows \<open>cregister_chain F (cregister_pair G H) = cregister_pair (cregister_chain F G) (cregister_chain F H)\<close>
proof -
  consider (GH_F) \<open>ccompatible G H\<close> \<open>cregister F\<close> | (nF) \<open>F = non_cregister\<close> | (nGH) \<open>\<not> ccompatible G H\<close>
    by (auto simp flip: non_cregister)
  then show ?thesis
  proof cases
    case GH_F
    then show ?thesis
      unfolding ccompatible_def
      apply transfer
      by (simp add: Laws_Classical.register_comp_pair)
  next
    case nF
    then show ?thesis
      by simp
  next
    case nGH
    then have \<open>\<not> ccompatible (cregister_chain F G) (cregister_chain F H)\<close>
      by (rule not_ccompatible_chain)
    then have [simp]: \<open>cregister_pair (cregister_chain F G) (cregister_chain F H) = non_cregister\<close>
      using non_cregister by auto
    from nGH have [simp]: \<open>cregister_pair G H = non_cregister\<close>
      using non_cregister by blast
    with nGH show ?thesis 
      by simp
  qed
qed
lemma qregister_chain_pair:
  shows \<open>qregister_chain F (qregister_pair G H) = qregister_pair (qregister_chain F G) (qregister_chain F H)\<close>
proof -
  consider (GH_F) \<open>qcompatible G H\<close> \<open>qregister F\<close> | (nF) \<open>F = non_qregister\<close> | (nGH) \<open>\<not> qcompatible G H\<close>
    by (auto simp flip: non_qregister)
  then show ?thesis
  proof cases
    case GH_F
    then show ?thesis
      unfolding qcompatible_def
      apply transfer
      by (simp add: Laws_Quantum.register_comp_pair)
  next
    case nF
    then show ?thesis
      by simp
  next
    case nGH
    then have \<open>\<not> qcompatible (qregister_chain F G) (qregister_chain F H)\<close>
      by (rule not_qcompatible_chain)
    then have [simp]: \<open>qregister_pair (qregister_chain F G) (qregister_chain F H) = non_qregister\<close>
      using non_qregister by auto
    from nGH have [simp]: \<open>qregister_pair G H = non_qregister\<close>
      using non_qregister by blast
    with nGH show ?thesis 
      by simp
  qed
qed

lemma cregister_chain_cswap_cswap[simp]: \<open>cregister_chain cswap cswap = cregister_id\<close>
  by (metis Laws_Classical.pair_Fst_Snd apply_cregister_inverse cFst.rep_eq cSnd.rep_eq ccompatible_Fst_Snd ccompatible_Snd_Fst ccompatible_def cregister_chain_pair cregister_chain_pair_Fst cregister_chain_pair_Snd cregister_id.abs_eq cregister_pair.rep_eq cswap_def)
lemma qregister_chain_qswap_qswap[simp]: \<open>qregister_chain qswap qswap = qregister_id\<close>
  by (metis Laws_Quantum.compatible_Fst_Snd Laws_Quantum.pair_Fst_Snd apply_qregister_inverse qFst.rep_eq qSnd.rep_eq qcompatible_Snd_Fst qregister_chain_pair qregister_chain_pair_Fst qregister_chain_pair_Snd qregister_id.abs_eq qregister_pair.rep_eq qswap_def)


definition \<open>iso_cregister I \<longleftrightarrow> cregister I \<and> (\<exists>J. cregister J \<and> cregister_chain I J = cregister_id \<and> cregister_chain J I = cregister_id)\<close>
definition \<open>iso_qregister I \<longleftrightarrow> qregister I \<and> (\<exists>J. qregister J \<and> qregister_chain I J = qregister_id \<and> qregister_chain J I = qregister_id)\<close>

lift_definition cregister_inv :: \<open>('a,'b) cregister \<Rightarrow> ('b,'a) cregister\<close> is
  \<open>\<lambda>F. if cregister_raw (inv F) then inv F else non_cregister_raw\<close> by auto
lift_definition qregister_inv :: \<open>('a,'b) qregister \<Rightarrow> ('b,'a) qregister\<close> is
  \<open>\<lambda>F. if qregister_raw (inv F) then inv F else non_qregister_raw\<close> by auto

lemma iso_cregister_inv_iso: \<open>iso_cregister I \<Longrightarrow> iso_cregister (cregister_inv I)\<close>
  unfolding iso_cregister_def apply transfer apply auto
  using non_cregister_raw apply fastforce
  using inv_unique_comp apply blast
  apply (simp add: inv_unique_comp)
  using inv_unique_comp by blast
lemma iso_qregister_inv_iso: \<open>iso_qregister I \<Longrightarrow> iso_qregister (qregister_inv I)\<close>
  unfolding iso_qregister_def apply transfer apply auto
  using non_qregister_raw apply fastforce
  using inv_unique_comp apply blast
  apply (simp add: inv_unique_comp)
  using inv_unique_comp by blast

lemma iso_cregister_inv_iso_apply: \<open>iso_cregister I \<Longrightarrow> apply_cregister (cregister_inv I) = inv (apply_cregister I)\<close>
  unfolding iso_cregister_def apply transfer using non_cregister_raw inv_unique_comp apply auto by blast
lemma iso_qregister_inv_iso_apply: \<open>iso_qregister I \<Longrightarrow> apply_qregister (qregister_inv I) = inv (apply_qregister I)\<close>
  unfolding iso_qregister_def apply transfer using non_qregister_raw inv_unique_comp apply auto by blast

lemma iso_cregister_inv_chain: \<open>iso_cregister I \<Longrightarrow> cregister_chain (cregister_inv I) I = cregister_id\<close>
  apply (rule apply_cregister_inject[THEN iffD1], rule ext)
  apply simp
  by (smt (verit, del_insts) apply_cregister_id inv_unique_comp iso_cregister_def iso_cregister_inv_iso_apply pointfree_idE cregister_chain_apply)
lemma iso_qregister_inv_chain: \<open>iso_qregister I \<Longrightarrow> qregister_chain (qregister_inv I) I = qregister_id\<close>
  apply (rule apply_qregister_inject[THEN iffD1], rule ext)
  apply simp
  by (smt (verit, del_insts) apply_qregister_id inv_unique_comp iso_qregister_def iso_qregister_inv_iso_apply pointfree_idE qregister_chain_apply)

lemma iso_cregister_chain_inv: \<open>iso_cregister I \<Longrightarrow> cregister_chain I (cregister_inv I) = cregister_id\<close>
  apply (rule apply_cregister_inject[THEN iffD1], rule ext)
  apply simp
  by (smt (verit, best) apply_cregister_id iso_cregister_def iso_cregister_inv_chain left_right_inverse_eq pointfree_idE cregister_chain_apply)
lemma iso_qregister_chain_inv: \<open>iso_qregister I \<Longrightarrow> qregister_chain I (qregister_inv I) = qregister_id\<close>
  apply (rule apply_qregister_inject[THEN iffD1], rule ext)
  apply simp
  by (smt (verit, best) apply_qregister_id iso_qregister_def iso_qregister_inv_chain left_right_inverse_eq pointfree_idE qregister_chain_apply)

lemma CREGISTER_of_iso: \<open>CREGISTER_of I = CREGISTER_all\<close> if \<open>iso_cregister I\<close>
proof -
  have \<open>x \<in> range (apply_cregister I)\<close> for x
    apply (rule range_eqI[where x=\<open>apply_cregister (cregister_inv I) x\<close>])
    by (metis inj_cregister inv_f_eq iso_cregister_def iso_cregister_inv_iso iso_cregister_inv_iso_apply that)
  then show ?thesis
    apply (transfer fixing: I)
    using that by (auto simp: iso_cregister_def)
qed
lemma QREGISTER_of_iso: \<open>QREGISTER_of I = QREGISTER_all\<close> if \<open>iso_qregister I\<close>
proof -
  have \<open>x \<in> range (apply_qregister I)\<close> for x
    apply (rule range_eqI[where x=\<open>apply_qregister (qregister_inv I) x\<close>])
    by (metis inj_qregister inv_f_eq iso_qregister_def iso_qregister_inv_iso iso_qregister_inv_iso_apply that)
  then show ?thesis
    apply (transfer fixing: I)
    using that by (auto simp: iso_qregister_def)
qed

lemma cswap_iso[simp]: \<open>iso_cregister cswap\<close>
  by (auto intro!: exI[of _ cswap] simp: iso_cregister_def)
lemma qswap_iso[simp]: \<open>iso_qregister qswap\<close>
  by (auto intro!: exI[of _ qswap] simp: iso_qregister_def)

lemma ccompatible_chain[simp]: \<open>cregister F \<Longrightarrow> ccompatible G H \<Longrightarrow> ccompatible (cregister_chain F G) (cregister_chain F H)\<close>
  unfolding ccompatible_def apply transfer by simp  
lemma qcompatible_chain[simp]: \<open>qregister F \<Longrightarrow> qcompatible G H \<Longrightarrow> qcompatible (qregister_chain F G) (qregister_chain F H)\<close>
  unfolding qcompatible_def apply transfer by simp  

lemma ccompatible_chain_iso: \<open>iso_cregister I \<Longrightarrow> ccompatible (cregister_chain I F) (cregister_chain I G) \<longleftrightarrow> ccompatible F G\<close>
  apply (cases \<open>cregister F\<close>; cases \<open>cregister G\<close>)
     apply (simp_all add: non_cregister)
  apply (rule iffI)
   apply (subst asm_rl[of \<open>F = cregister_chain (cregister_inv I) (cregister_chain I F)\<close>])
    apply (simp add: cregister_chain_assoc[symmetric] iso_cregister_inv_chain)
   apply (subst asm_rl[of \<open>G = cregister_chain (cregister_inv I) (cregister_chain I G)\<close>])
    apply (simp add: cregister_chain_assoc[symmetric] iso_cregister_inv_chain)
   apply (rule ccompatible_chain)
  using iso_cregister_def iso_cregister_inv_iso apply auto
  by (simp add: iso_cregister_def ccompatible_chain)
lemma qcompatible_chain_iso: \<open>iso_qregister I \<Longrightarrow> qcompatible (qregister_chain I F) (qregister_chain I G) \<longleftrightarrow> qcompatible F G\<close>
  apply (cases \<open>qregister F\<close>; cases \<open>qregister G\<close>)
     apply (simp_all add: non_qregister)
  apply (rule iffI)
   apply (subst asm_rl[of \<open>F = qregister_chain (qregister_inv I) (qregister_chain I F)\<close>])
    apply (simp add: qregister_chain_assoc[symmetric] iso_qregister_inv_chain)
   apply (subst asm_rl[of \<open>G = qregister_chain (qregister_inv I) (qregister_chain I G)\<close>])
    apply (simp add: qregister_chain_assoc[symmetric] iso_qregister_inv_chain)
   apply (rule qcompatible_chain)
  using iso_qregister_def iso_qregister_inv_iso apply auto
  by (simp add: iso_qregister_def qcompatible_chain)

lift_definition getter :: \<open>('a,'b) cregister \<Rightarrow> 'b \<Rightarrow> 'a\<close> is
  \<open>\<lambda>F. if cregister_raw F then Axioms_Classical.getter F else (\<lambda>_. undefined)\<close>.
lift_definition setter :: \<open>('a,'b) cregister \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b\<close> is
  \<open>\<lambda>F. if cregister_raw F then Axioms_Classical.setter F else (\<lambda>_. id)\<close>.

lemma getter_non_cregister[simp]: \<open>getter non_cregister m = undefined\<close>
  apply transfer by (simp add: non_cregister_raw)
lemma setter_non_cregister[simp]: \<open>setter non_cregister a = id\<close>
  apply transfer by (simp add: non_cregister_raw)

lemma getter_setter_same[simp]: \<open>cregister x \<Longrightarrow> getter x (setter x a m) = a\<close>
  apply transfer apply (simp add: non_cregister_raw)
  by (meson valid_getter_setter_def valid_getter_setter_getter_setter)

lemma setter_setter_same[simp]: \<open>setter x b (setter x a m) = setter x b m\<close>
  apply transfer apply (simp add: non_cregister_raw)
  by (meson valid_getter_setter_def valid_getter_setter_getter_setter)

(* TODO move to Registers.Classical_Extra *)
lemma getter_setter: \<open>Axioms_Classical.getter F (Axioms_Classical.setter G a m) = Axioms_Classical.getter F m\<close> if \<open>Laws_Classical.compatible F G\<close> for F G
proof -
  have \<open>Axioms_Classical.register F\<close>
    using Laws_Classical.compatible_register1 that by blast
  have \<open>Axioms_Classical.register G\<close>
    using Laws_Classical.compatible_register2 that by auto
  have valid_gsF: \<open>valid_getter_setter (Axioms_Classical.getter F) (Axioms_Classical.setter F)\<close>
    by (simp add: \<open>cregister_raw F\<close>)

  have \<open>Axioms_Classical.getter F (Axioms_Classical.setter G a m)
      = Axioms_Classical.getter F (Axioms_Classical.setter G a 
              (Axioms_Classical.setter F (Axioms_Classical.getter F m) m))\<close>
    by (metis valid_gsF valid_getter_setter_def)
  also have \<open>\<dots> = Axioms_Classical.getter F (Axioms_Classical.setter F
                      (Axioms_Classical.getter F m) (Axioms_Classical.setter G a m))\<close>
    by (metis (mono_tags, lifting) Classical_Extra.compatible_setter 
        \<open>cregister_raw F\<close> \<open>cregister_raw G\<close> o_eq_dest that)
  also have \<open>\<dots> = Axioms_Classical.getter F m\<close>
    by (meson valid_gsF valid_getter_setter_def)
  finally show ?thesis
    by -
qed

(* TODO move to Registers *)
lemma setter_setter_compatI_raw:
  assumes \<open>cregister_raw x\<close> and \<open>cregister_raw y\<close>
  assumes \<open>\<And>a b m. Axioms_Classical.setter x a (Axioms_Classical.setter y b m)
                 = Axioms_Classical.setter y b (Axioms_Classical.setter x a m)\<close>
  shows \<open>ccompatible_raw x y\<close>
proof -
  define sx gx sy gy where \<open>sx = Axioms_Classical.setter x\<close> and \<open>gx = Axioms_Classical.getter x\<close>
    and \<open>sy = Axioms_Classical.setter y\<close> and \<open>gy = Axioms_Classical.getter y\<close>
  have x: \<open>x = register_from_getter_setter gx sx\<close>
    by (simp add: assms(1) gx_def sx_def)
  have y: \<open>y = register_from_getter_setter gy sy\<close>
    by (simp add: assms(2) gy_def sy_def)

  have [simp]: \<open>sx (gx m) m = m\<close> for m
    by (metis assms(1) gx_def sx_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have [simp]: \<open>gx (sx a m) = a\<close> for a m
    by (metis assms(1) gx_def sx_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have [simp]: \<open>sy (gy m) m = m\<close> for m
    by (metis assms(2) gy_def sy_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have [simp]: \<open>gy (sy a m) = a\<close> for a m
    by (metis assms(2) gy_def sy_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have s_comm: \<open>sx a (sy b m) = sy b (sx a m)\<close> for a b m
    using assms(3) by (simp add: sx_def sy_def)
  have [simp]: \<open>gx (sy a m) = gx m\<close> for a m
  proof -
    have \<open>gx (sy a m) = gx (sy a (sx (gx m) m))\<close>
      by simp
    also have \<open>\<dots> = gx (sx (gx m) (sy a m))\<close>
      by (simp add: s_comm)
    also have \<open>\<dots> = gx m\<close>
      by simp
    finally show ?thesis
      by -
  qed
  have [simp]: \<open>gy (sx a m) = gy m\<close> for a m
  proof -
    have \<open>gy (sx a m) = gy (sx a (sy (gy m) m))\<close>
      by simp
    also have \<open>\<dots> = gy (sy (gy m) (sx a m))\<close>
      by (simp flip: s_comm)
    also have \<open>\<dots> = gy m\<close>
      by simp
    finally show ?thesis
      by -
  qed

  have \<open>(x a \<circ>\<^sub>m y b) m = (y b \<circ>\<^sub>m x a) m\<close> for a b m
    apply (cases \<open>a (gx m)\<close>; cases \<open>b (gy m)\<close>)
    by (auto simp add: x y register_from_getter_setter_def[abs_def] s_comm)
  then show ?thesis
    apply (rule_tac Laws_Classical.compatibleI)
    using assms(1,2) by auto
qed

lemma getter_setter_compat[simp]: \<open>ccompatible x y \<Longrightarrow> getter x (setter y a m) = getter x m\<close>
  unfolding ccompatible_def
  apply transfer by (simp add: non_cregister_raw getter_setter)
lemma setter_setter_compat: \<open>ccompatible x y \<Longrightarrow> setter x a (setter y b m) = setter y b (setter x a m)\<close>
  unfolding ccompatible_def
  apply transfer apply (simp add: non_cregister_raw)
  by (metis Classical_Extra.compatible_setter o_def)
lemma setter_setter_compatI: 
  assumes \<open>cregister x\<close> and \<open>cregister y\<close>
  assumes \<open>\<And>a b m. setter x a (setter y b m) = setter y b (setter x a m)\<close>
  shows \<open>ccompatible x y\<close>
  unfolding ccompatible_def using assms
  apply transfer by (auto simp add: non_cregister_raw setter_setter_compatI_raw)
lemma setter_getter_same[simp]: \<open>setter x (getter x m) m = m\<close>
  apply transfer apply (simp add: non_cregister_raw)
  by (metis valid_getter_setter_def valid_getter_setter_getter_setter)

lift_definition cregister_from_getter_setter :: \<open>('b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a,'b) cregister\<close> is
  \<open>\<lambda>g s. if valid_getter_setter g s then register_from_getter_setter g s else non_cregister_raw\<close>
  by auto

lemma setter_of_cregister_from_getter_is_cregister: \<open>valid_getter_setter g s \<Longrightarrow> cregister (cregister_from_getter_setter g s)\<close>
  apply transfer by simp
lemma setter_of_cregister_from_getter_setter: \<open>valid_getter_setter g s \<Longrightarrow> setter (cregister_from_getter_setter g s) = s\<close>
  apply transfer by simp
lemma getter_of_cregister_from_getter_setter: \<open>valid_getter_setter g s \<Longrightarrow> getter (cregister_from_getter_setter g s) = g\<close>
  apply transfer by simp


(* TODO move to Registers *)
lemma valid_getter_setter_pair: 
  assumes \<open>Laws_Classical.compatible F G\<close>
  shows \<open>valid_getter_setter (\<lambda>m. (Axioms_Classical.getter F m, Axioms_Classical.getter G m))
           (\<lambda>(a, b) m. Axioms_Classical.setter F a (Axioms_Classical.setter G b m))\<close>
proof -
  have \<open>Axioms_Classical.register F\<close>
    using Laws_Classical.compatible_register1 assms by blast
  have \<open>Axioms_Classical.register G\<close>
    using Laws_Classical.compatible_register2 assms by auto
  have valid_gsF: \<open>valid_getter_setter (Axioms_Classical.getter F) (Axioms_Classical.setter F)\<close>
    by (simp add: \<open>cregister_raw F\<close>)
  have valid_gsG: \<open>valid_getter_setter (Axioms_Classical.getter G) (Axioms_Classical.setter G)\<close>
    by (simp add: \<open>cregister_raw G\<close>)

  have valid: \<open>valid_getter_setter (\<lambda>m. (Axioms_Classical.getter F m, Axioms_Classical.getter G m))
     (\<lambda>(a, b) m. Axioms_Classical.setter F a (Axioms_Classical.setter G b m))\<close>
    using valid_gsF valid_gsG
    apply (auto simp: valid_getter_setter_def)
     apply (metis Laws_Classical.compatible_sym assms getter_setter)
    by (metis Classical_Extra.compatible_setter Laws_Classical.compatible_register1 Laws_Classical.compatible_register2 assms o_def)
  show ?thesis
    using valid by (auto simp: Axioms_Classical.register_pair_def o_def setter_of_register_from_getter_setter)
qed

(* TODO move to Registers session *)
lemma setter_pair_raw: \<open>Axioms_Classical.setter (F;G) = (\<lambda>(x, y). Axioms_Classical.setter F x \<circ> Axioms_Classical.setter G y)\<close>
  if \<open>Laws_Classical.compatible F G\<close>
  using valid_getter_setter_pair[OF that] 
  by (auto simp: Axioms_Classical.register_pair_def o_def)

lemma setter_pair:
  assumes \<open>ccompatible F G\<close>
  shows \<open>setter (cregister_pair F G) = (\<lambda>(x,y). setter F x o setter G y)\<close>
  using assms unfolding ccompatible_def
  apply transfer using setter_pair_raw by auto

(* TODO move to Registers *)
lemma getter_pair_raw:
  assumes \<open>ccompatible_raw F G\<close>
  shows \<open>Axioms_Classical.getter (F;G) = (\<lambda>m. (Axioms_Classical.getter F m, Axioms_Classical.getter G m))\<close>
  using assms by (simp_all add: Axioms_Classical.register_pair_def valid_getter_setter_pair)

lemma getter_pair:
  assumes \<open>ccompatible F G\<close>
  shows \<open>getter (cregister_pair F G) = (\<lambda>m. (getter F m, getter G m))\<close>
  using assms unfolding ccompatible_def
  apply transfer using getter_pair_raw by auto

(* TODO move to Registers *)
lemma getterI: 
  assumes \<open>Axioms_Classical.register F\<close>
  assumes \<open>Axioms_Classical.setter F a m = m\<close>
  shows \<open>Axioms_Classical.getter F m = a\<close>
  by (metis assms(1) assms(2) valid_getter_setter_def valid_getter_setter_getter_setter)

(* TODO move to Registers *)
lemma register_apply_comp:
  assumes \<open>cregister_raw F\<close> and \<open>cregister_raw G\<close>
  shows \<open>register_apply (F \<circ> G) f m = register_apply F (register_apply G f) m\<close>
  apply (rule option.inject[THEN iffD1])
  by (simp add:
      register_apply[unfolded o_def, OF \<open>cregister_raw F\<close>, THEN fun_cong]
      register_apply[unfolded o_def, OF \<open>cregister_raw G\<close>, THEN fun_cong]
      register_apply[unfolded o_def, OF cregister_raw_chain[OF \<open>cregister_raw G\<close> \<open>cregister_raw F\<close>], THEN fun_cong]
      del: option.inject)

(* TODO move to Registers *)
lemma
  assumes [simp]: \<open>cregister_raw F\<close> \<open>cregister_raw G\<close>
  shows setter_chain_raw: \<open>Axioms_Classical.setter (F \<circ> G) a m =
       Axioms_Classical.setter F
        (Axioms_Classical.setter G a (Axioms_Classical.getter F m)) m\<close>
    and getter_chain_raw: \<open>Axioms_Classical.getter (F \<circ> G) = Axioms_Classical.getter G \<circ> Axioms_Classical.getter F\<close>
proof -
  define sF gF where \<open>sF = Axioms_Classical.setter F\<close> and \<open>gF = Axioms_Classical.getter F\<close>
  from \<open>Axioms_Classical.register F\<close>
  have F: \<open>F u m = (case u (gF m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (sF x m))\<close> for u m
    by (metis gF_def register_from_getter_setter_def register_from_getter_setter_of_getter_setter sF_def)
  have validF: \<open>valid_getter_setter gF sF\<close>
    using gF_def sF_def by auto
  define sG gG where \<open>sG = Axioms_Classical.setter G\<close> and \<open>gG = Axioms_Classical.getter G\<close>
  from \<open>Axioms_Classical.register G\<close>
  have G: \<open>G u m = (case u (gG m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (sG x m))\<close> for u m
    by (metis gG_def register_from_getter_setter_def register_from_getter_setter_of_getter_setter sG_def)
  have validG: \<open>valid_getter_setter gG sG\<close>
    by (simp add: gG_def sG_def)
  define s g where \<open>s a m = sF (sG a (gF m)) m\<close> and \<open>g m = gG (gF m)\<close> for a m
  have *: \<open>(F \<circ> G) a m = register_from_getter_setter g s a m\<close> for a m
    by (auto simp add: option.case_eq_if F G s_def g_def register_from_getter_setter_def)
  have \<open>valid_getter_setter g s\<close>
    using validF validG by (auto simp: valid_getter_setter_def s_def g_def)
  show \<open>Axioms_Classical.setter (F \<circ> G) a m = sF (sG a (gF m)) m\<close>
    apply (simp add: *[abs_def] setter_of_register_from_getter_setter \<open>valid_getter_setter g s\<close>)
    by (simp add: s_def)
  show \<open>Axioms_Classical.getter (F \<circ> G) = gG o gF\<close>
    apply (simp add: *[abs_def] getter_of_register_from_getter_setter \<open>valid_getter_setter g s\<close>)
    by (simp add: g_def[abs_def] o_def)
qed


lemma getter_chain:
  assumes \<open>cregister F\<close>
  shows \<open>getter (cregister_chain F G) = getter G o getter F\<close>
  using assms apply transfer using getter_chain_raw by (auto simp: non_cregister_raw)

definition same_outside_cregister :: \<open>('a,'b) cregister \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool\<close> where
  \<open>same_outside_cregister F x y \<longleftrightarrow> x = setter F (getter F x) y\<close>

lemma same_outside_cregister_non_cregister[simp]: \<open>same_outside_cregister non_cregister = (=)\<close>
  unfolding same_outside_cregister_def
  by simp

lemma equivp_same_outside_cregister[simp]: \<open>equivp (same_outside_cregister F)\<close>
proof (cases \<open>cregister F\<close>)
  case False
  then have [simp]: \<open>F = non_cregister\<close>
    using non_cregister by force
  show ?thesis
    using identity_equivp by simp
next
  case True
  have \<open>reflp (same_outside_cregister F)\<close>
    by (simp add: same_outside_cregister_def reflpI)
  moreover have \<open>symp (same_outside_cregister F)\<close>
    by (metis same_outside_cregister_def setter_getter_same setter_setter_same sympI)
  moreover have \<open>transp (same_outside_cregister F)\<close>
    by (smt (verit, del_insts) same_outside_cregister_def setter_setter_same transpI)
  ultimately show ?thesis
    by (rule equivpI)
qed

definition \<open>apply_qregister_space F S = apply_qregister F (Proj S) *\<^sub>S top\<close>

lemma apply_non_qregister_space[simp]: \<open>apply_qregister_space non_qregister x = 0\<close>
  by (simp add: apply_qregister_space_def)

axiomatization CCOMPLEMENT :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER\<close>
lift_definition QCOMPLEMENT :: \<open>'a QREGISTER \<Rightarrow> 'a QREGISTER\<close> is commutant
  apply (auto simp add: valid_qregister_range_def)
  by (metis (mono_tags, opaque_lifting) commutant_adj commutant_antimono double_adj image_iff subset_iff)

lemma cregister_pair_chain_swap[simp]:
  "cregister_chain (cregister_pair A B) cswap = (cregister_pair B A)"
  apply (cases \<open>ccompatible A B\<close>)
   apply (auto simp: non_cregister cregister_chain_pair cswap_def)
  by (metis ccompatible_sym non_cregister)
lemma qregister_pair_chain_swap[simp]:
  "qregister_chain (qregister_pair A B) qswap = (qregister_pair B A)"
  apply (cases \<open>qcompatible A B\<close>)
   apply (auto simp: non_qregister qregister_chain_pair qswap_def)
  by (metis qcompatible_sym non_qregister)

lemma Cccompatible_antimono_left: \<open>A \<le> B \<Longrightarrow> Cccompatible B C \<Longrightarrow> Cccompatible A C\<close>
  apply transfer by auto
lemma Qqcompatible_antimono_left: \<open>A \<le> B \<Longrightarrow> Qqcompatible B C \<Longrightarrow> Qqcompatible A C\<close>
  apply transfer by auto

lemma setter_chain:
  assumes \<open>cregister F\<close> \<open>cregister G\<close>
  shows \<open>setter (cregister_chain F G) a m = setter F (setter G a (getter F m)) m\<close>
  using assms apply transfer using setter_chain_raw apply auto by fast

(* TODO move to Registers *)
lemma valid_getter_setter_fst[simp]: \<open>valid_getter_setter fst (\<lambda>x (_,y). (x,y))\<close>
  by (simp add: valid_getter_setter_def)
lemma Fst_register_from_getter_setter: \<open>Laws_Classical.Fst = register_from_getter_setter fst (\<lambda>x (_,y). (x,y))\<close>
proof -
  have \<open>Axioms_Classical.preregister Laws_Classical.Fst\<close>
    by simp
  moreover have \<open>Axioms_Classical.preregister (register_from_getter_setter fst (\<lambda>x (_, y). (x, y)))\<close>
    by simp
  moreover have \<open>Laws_Classical.Fst (update1 u v) = register_from_getter_setter fst (\<lambda>x (_, y). (x, y)) (update1 u v)\<close> for u v :: 'a
    by (auto intro!: ext 
        simp add: Laws_Classical.Fst_def register_from_getter_setter_def[abs_def] 
        Axioms_Classical.tensor_update_def update1_def)
  ultimately show ?thesis
    by (rule update1_extensionality)
qed
lemma valid_getter_setter_snd[simp]: \<open>valid_getter_setter snd (\<lambda>y (x,_). (x,y))\<close>
  by (simp add: valid_getter_setter_def)
lemma Snd_register_from_getter_setter: \<open>Laws_Classical.Snd = register_from_getter_setter snd (\<lambda>y (x,_). (x,y))\<close>
proof -
  have \<open>Axioms_Classical.preregister Laws_Classical.Snd\<close>
    by simp
  moreover have \<open>Axioms_Classical.preregister (register_from_getter_setter snd (\<lambda>y (x,_). (x, y)))\<close>
    by simp
  moreover have \<open>Laws_Classical.Snd (update1 u v) = register_from_getter_setter snd (\<lambda>y (x,_). (x,y)) (update1 u v)\<close> for u v :: 'a
    by (auto intro!: ext 
        simp add: Laws_Classical.Snd_def register_from_getter_setter_def[abs_def] 
        Axioms_Classical.tensor_update_def update1_def)
  ultimately show ?thesis
    by (rule update1_extensionality)
qed
lemma setter_Fst: \<open>Axioms_Classical.setter Laws_Classical.Fst x' xy = (x',snd xy)\<close>
  apply (subst Fst_register_from_getter_setter)
  by (simp add: case_prod_beta)
lemma getter_Fst: \<open>Axioms_Classical.getter Laws_Classical.Fst = fst\<close>
  apply (subst Fst_register_from_getter_setter)
  by (simp add: case_prod_beta)
lemma setter_Snd: \<open>Axioms_Classical.setter Laws_Classical.Snd y' xy = (fst xy,y')\<close>
  apply (subst Snd_register_from_getter_setter)
  by (simp add: case_prod_beta)
lemma getter_Snd: \<open>Axioms_Classical.getter Laws_Classical.Snd = snd\<close>
  apply (subst Snd_register_from_getter_setter)
  by (simp add: case_prod_beta)

lemma setter_cFst: \<open>setter cFst x' xy = (x',snd xy)\<close>
  apply transfer
  by (simp add: setter_Fst[abs_def] case_prod_unfold)
lemma setter_cSnd: \<open>setter cSnd y' xy = (fst xy,y')\<close>
  apply transfer
  by (simp add: setter_Snd[abs_def] case_prod_unfold)
lemma getter_cFst[simp]: \<open>getter cFst = fst\<close>
  apply transfer by (simp add: getter_Fst)
lemma getter_cSnd[simp]: \<open>getter cSnd = snd\<close>
  apply transfer by (simp add: getter_Snd)

(* TODO move to misc *)
lemma Some_map_comp[simp]: \<open>Some \<circ>\<^sub>m f = f\<close>
  apply (rule ext, case_tac \<open>f x\<close>)
  by (auto simp: map_comp_def)

(* TODO move to misc *)
lemma map_comp_Some[simp]: \<open>f \<circ>\<^sub>m Some = f\<close>
  apply (rule ext, case_tac \<open>f x\<close>)
  by (auto simp: map_comp_def)

lemma Cccompatible_CREGISTER_of: \<open>Cccompatible (CREGISTER_of A) B \<longleftrightarrow> ccompatible A B \<or> (cregister B \<and> A = non_cregister)\<close>
  unfolding CREGISTER_of.rep_eq Cccompatible.rep_eq
  apply transfer
  by (auto simp add: non_cregister_raw empty_cregister_range_def ccompatible_raw_def)
lemma Qqcompatible_QREGISTER_of: \<open>Qqcompatible (QREGISTER_of A) B \<longleftrightarrow> qcompatible A B \<or> (qregister B \<and> A = non_qregister)\<close>
  unfolding QREGISTER_of.rep_eq Qqcompatible.rep_eq
  apply transfer
  by (auto simp add: non_qregister_raw empty_qregister_range_def qcompatible_raw_def)

lemma Cccompatible_CREGISTER_ofI[simp]: \<open>ccompatible F G \<Longrightarrow> Cccompatible (CREGISTER_of F) G\<close>
  by (simp add: Cccompatible_CREGISTER_of)
lemma Qqcompatible_QREGISTER_ofI[simp]: \<open>qcompatible F G \<Longrightarrow> Qqcompatible (QREGISTER_of F) G\<close>
  by (simp add: Qqcompatible_QREGISTER_of)

lemma cregister_conversion_raw_register: \<open>cregister_raw F \<Longrightarrow> cregister_raw G \<Longrightarrow> range F \<subseteq> range G \<Longrightarrow> cregister_raw (inv G \<circ> F)\<close>
  sorry
lemmas qregister_conversion_raw_register = register_inv_G_o_F
(* lemma qregister_conversion_raw_register: \<open>qregister_raw F \<Longrightarrow> qregister_raw G \<Longrightarrow> range F \<subseteq> range G \<Longrightarrow> qregister_raw (inv G \<circ> F)\<close> *)

lift_definition cregister_conversion :: \<open>('a,'c) cregister \<Rightarrow> ('b,'c) cregister \<Rightarrow> ('a,'b) cregister\<close> is
  \<open>\<lambda>F G. if cregister_raw F \<and> cregister_raw G \<and> range F \<subseteq> range G then inv G o F else non_cregister_raw\<close>
  by (auto intro: cregister_conversion_raw_register)

lift_definition qregister_conversion :: \<open>('a,'c) qregister \<Rightarrow> ('b,'c) qregister \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>F G. if qregister_raw F \<and> qregister_raw G \<and> range F \<subseteq> range G then inv G o F else non_qregister_raw\<close>
  by (auto intro: qregister_conversion_raw_register)

definition \<open>cregister_le F G = (cregister F \<and> cregister G \<and> CREGISTER_of F \<le> CREGISTER_of G)\<close>
definition \<open>qregister_le F G = (qregister F \<and> qregister G \<and> QREGISTER_of F \<le> QREGISTER_of G)\<close>

lemma cregister_conversion_register: \<open>cregister_le F G \<Longrightarrow> cregister (cregister_conversion F G)\<close>
  apply (auto intro!: cregister_conversion_raw_register 
      simp add: cregister_le_def less_eq_CREGISTER_def CREGISTER_of.rep_eq
      cregister.rep_eq cregister_conversion.rep_eq)
  by auto
lemma qregister_conversion_register: \<open>qregister_le F G \<Longrightarrow> qregister (qregister_conversion F G)\<close>
  apply (auto intro!: qregister_conversion_raw_register 
      simp add: qregister_le_def less_eq_QREGISTER_def QREGISTER_of.rep_eq
      qregister.rep_eq qregister_conversion.rep_eq)
  by auto

lemma qregister_le_pair_leftI[iff]: 
  \<open>qregister_le (qregister_pair F G) H\<close> if \<open>qcompatible F G\<close> \<open>qregister_le F H\<close> \<open>qregister_le G H\<close>
proof -
  define F' G' H' where FGH'_def: \<open>F' = Rep_QREGISTER (QREGISTER_of F)\<close> 
    \<open>G' = Rep_QREGISTER (QREGISTER_of G)\<close> \<open>H' = Rep_QREGISTER (QREGISTER_of H)\<close>
  have \<open>F' \<union> G' \<subseteq> H'\<close>
    by (metis FGH'_def Un_least less_eq_QREGISTER.rep_eq qregister_le_def that(2,3))
  then have \<open>commutant (commutant (F' \<union> G')) \<subseteq> commutant (commutant H')\<close>
    by (auto intro!: commutant_antimono)
  also have \<open>\<dots> = H'\<close>
    using FGH'_def Rep_QREGISTER valid_qregister_range_def by auto
  finally have \<open>commutant (commutant (F' \<union> G')) \<subseteq> H'\<close>
    by -
  then show ?thesis
    using that 
    by (simp add: qregister_le_def QREGISTER_of_qregister_pair QREGISTER_pair.rep_eq 
        less_eq_QREGISTER.rep_eq flip: FGH'_def)
qed
lemma qregister_le_pair_rightI1: \<open>qregister_le F (qregister_pair G H)\<close> if \<open>qcompatible G H\<close> \<open>qregister_le F G\<close>
proof -
  define F' G' H' where FGH'_def: \<open>F' = Rep_QREGISTER (QREGISTER_of F)\<close> 
    \<open>G' = Rep_QREGISTER (QREGISTER_of G)\<close> \<open>H' = Rep_QREGISTER (QREGISTER_of H)\<close>
  have \<open>F' \<subseteq> G' \<union> H'\<close>
    using FGH'_def less_eq_QREGISTER.rep_eq qregister_le_def that(2) by blast
  then have \<open>commutant (commutant (G' \<union> H')) \<supseteq> commutant (commutant F')\<close> (is \<open>_ \<supseteq> \<dots>\<close>)
    by (auto intro!: commutant_antimono)
  also have \<open>\<dots> = F'\<close>
    using FGH'_def Rep_QREGISTER valid_qregister_range_def by auto
  finally have \<open>commutant (commutant (G' \<union> H')) \<supseteq> F'\<close>
    by -
  then show ?thesis
    using that 
    by (simp add: qregister_le_def QREGISTER_of_qregister_pair QREGISTER_pair.rep_eq 
        less_eq_QREGISTER.rep_eq flip: FGH'_def)
qed
lemma qregister_le_pair_rightI2: \<open>qregister_le F (qregister_pair G H)\<close> if \<open>qcompatible G H\<close> \<open>qregister_le F H\<close>
  using qregister_le_pair_rightI1[OF that(1)[THEN qcompatible_sym] that(2)]
  by (auto simp add: qregister_le_def qcompatible_sym QREGISTER_of_qregister_pair
      less_eq_QREGISTER.rep_eq QREGISTER_pair.rep_eq Un_commute)
lemma qregister_le_refl[iff]: \<open>qregister F \<Longrightarrow> qregister_le F F\<close> (* TODO: could replace this by a simp-rule *)
  unfolding qregister_le_def by simp
lemma qregister_le_iso: \<open>qregister F \<Longrightarrow> iso_qregister G \<Longrightarrow> qregister_le F G\<close>
  by (simp add: qregister_le_def QREGISTER_of_iso less_eq_QREGISTER.rep_eq QREGISTER_all.rep_eq
      iso_qregister_def)
lemma qregister_le_id[iff]: \<open>qregister F \<Longrightarrow> qregister_le F qregister_id\<close> (* TODO: could replace this by a simp-rule *)
  by (simp add: iso_qregister_def qregister_le_iso)


lemma cregister_chain_conversion: \<open>cregister_le F G \<Longrightarrow> cregister_chain G (cregister_conversion F G) = F\<close>
  unfolding cregister_le_def
  apply (transfer fixing: F G)
  apply transfer
  by (auto simp: non_cregister_raw cregister_conversion_raw_register f_inv_into_f in_mono intro!: ext)

lemma qregister_chain_conversion: \<open>qregister_le F G  \<Longrightarrow> qregister_chain G (qregister_conversion F G) = F\<close>
  unfolding qregister_le_def
  apply (transfer fixing: F G)
  apply transfer
  by (auto simp: non_qregister_raw qregister_conversion_raw_register f_inv_into_f in_mono intro!: ext)

lemma cregister_apply_conversion:
  assumes \<open>cregister_le F G\<close>
  shows \<open>apply_cregister F x = apply_cregister G (apply_cregister (cregister_conversion F G) x)\<close>
  using assms apply (subst cregister_chain_conversion[where F=F and G=G, symmetric])
  by auto
lemma qregister_apply_conversion:
  assumes \<open>qregister_le F G\<close>
  shows \<open>apply_qregister F x = apply_qregister G (apply_qregister (qregister_conversion F G) x)\<close>
  using assms apply (subst qregister_chain_conversion[where F=F and G=G, symmetric])
  by auto

lemma qregister_projector: \<open>qregister F \<Longrightarrow> is_Proj a \<Longrightarrow> is_Proj (apply_qregister F a)\<close>
  apply (transfer fixing: a)
  by (rule register_projector)

lemma apply_qregister_space_conversion:
  assumes [simp]: \<open>qregister_le F G\<close>
  shows \<open>apply_qregister_space F S = apply_qregister_space G (apply_qregister_space (qregister_conversion F G) S)\<close>
  by (simp add: apply_qregister_space_def qregister_apply_conversion[OF assms] Proj_on_own_range
      qregister_projector qregister_conversion_register)

lemma cregister_conversion_id[simp]: \<open>cregister_conversion F cregister_id = F\<close>
  apply transfer by auto
lemma qregister_conversion_id[simp]: \<open>qregister_conversion F qregister_id = F\<close>
  apply transfer by auto

lemma cregister_conversion_non_reg_right[simp]: \<open>cregister_conversion F non_cregister = non_cregister\<close>
  apply transfer by (auto simp add: non_cregister_raw)
lemma qregister_conversion_non_reg_right[simp]: \<open>qregister_conversion F non_qregister = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)

lemma cregister_conversion_non_reg_left[simp]: \<open>cregister_conversion non_cregister F = non_cregister\<close>
  apply transfer by (auto simp add: non_cregister_raw)
lemma qregister_conversion_non_reg_left[simp]: \<open>qregister_conversion non_qregister F = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)

lemma cregister_conversion_rename:
  fixes F :: \<open>('a,'c) cregister\<close> and G :: \<open>('b,'c) cregister\<close> and H :: \<open>('d, 'c) cregister\<close> and F' G'
  assumes \<open>cregister H\<close>
  assumes \<open>F = cregister_chain H F'\<close> \<open>G = cregister_chain H G'\<close>
  shows \<open>cregister_conversion F G = cregister_conversion F' G'\<close>
proof (cases \<open>cregister F'\<close>, cases \<open>cregister G'\<close>)
  assume \<open>\<not> cregister G'\<close>
  then have [simp]: \<open>G' = non_cregister\<close>
    using non_cregister by blast
  then show ?thesis
    apply (simp add: \<open>G = cregister_chain H G'\<close>)
    by -
next
  assume \<open>\<not> cregister F'\<close>
  then have [simp]: \<open>F' = non_cregister\<close>
    using non_cregister by blast
  then show ?thesis
    by (simp add: \<open>F = cregister_chain H F'\<close>)
next
  have range_le_preserve: \<open>range F' \<subseteq> range G'\<close> if \<open>range (\<lambda>x. H (F' x)) \<subseteq> range (\<lambda>x. H (G' x))\<close> and \<open>cregister_raw H\<close>
    for H :: \<open>'d cupdate \<Rightarrow> 'c cupdate\<close> and F' :: \<open>'a cupdate \<Rightarrow> 'd cupdate\<close> and G' :: \<open>'b cupdate \<Rightarrow> 'd cupdate\<close>
    using cregister_raw_inj[OF \<open>cregister_raw H\<close>] using that(1)
    by (smt (verit, best) image_subset_iff inj_def rangeE rangeI)
  have H_cancel: \<open>inv (H \<circ> G') \<circ> (H \<circ> F') = inv G' \<circ> F'\<close> if \<open>cregister_raw H\<close> and \<open>cregister_raw G'\<close>
    and \<open>range F' \<subseteq> range G'\<close>
    for H :: \<open>'d cupdate \<Rightarrow> 'c cupdate\<close> and F' :: \<open>'a cupdate \<Rightarrow> 'd cupdate\<close> and G' :: \<open>'b cupdate \<Rightarrow> 'd cupdate\<close>
    apply (rule inv_comp_eqI)
    using cregister_raw_inj[OF \<open>cregister_raw H\<close>] cregister_raw_inj[OF \<open>cregister_raw G'\<close>]
    using inj_compose that by (auto simp add: ext f_inv_into_f subset_iff)
  assume [simp]: \<open>cregister F'\<close> \<open>cregister G'\<close>
  then show ?thesis
    using assms apply transfer
    using range_le_preserve H_cancel by (auto simp: cregister_raw_chain)
qed

lemma qregister_conversion_rename:
  fixes F :: \<open>('a,'c) qregister\<close> and G :: \<open>('b,'c) qregister\<close> and H :: \<open>('d, 'c) qregister\<close> and F' G'
  assumes \<open>qregister H\<close>
  assumes \<open>F = qregister_chain H F'\<close> \<open>G = qregister_chain H G'\<close>
  shows \<open>qregister_conversion F G = qregister_conversion F' G'\<close>
proof (cases \<open>qregister F'\<close>, cases \<open>qregister G'\<close>)
  assume \<open>\<not> qregister G'\<close>
  then have [simp]: \<open>G' = non_qregister\<close>
    using non_qregister by blast
  then show ?thesis
    apply (simp add: \<open>G = qregister_chain H G'\<close>)
    by -
next
  assume \<open>\<not> qregister F'\<close>
  then have [simp]: \<open>F' = non_qregister\<close>
    using non_qregister by blast
  then show ?thesis
    by (simp add: \<open>F = qregister_chain H F'\<close>)
next
  have range_le_preserve: \<open>range F' \<subseteq> range G'\<close> if \<open>range (\<lambda>x. H (F' x)) \<subseteq> range (\<lambda>x. H (G' x))\<close> and \<open>qregister_raw H\<close>
    for H :: \<open>'d qupdate \<Rightarrow> 'c qupdate\<close> and F' :: \<open>'a qupdate \<Rightarrow> 'd qupdate\<close> and G' :: \<open>'b qupdate \<Rightarrow> 'd qupdate\<close>
    using qregister_raw_inj[OF \<open>qregister_raw H\<close>] using that(1)
    by (smt (verit, best) image_subset_iff inj_def rangeE rangeI)
  have H_cancel: \<open>inv (H \<circ> G') \<circ> (H \<circ> F') = inv G' \<circ> F'\<close> if \<open>qregister_raw H\<close> and \<open>qregister_raw G'\<close>
    and \<open>range F' \<subseteq> range G'\<close>
    for H :: \<open>'d qupdate \<Rightarrow> 'c qupdate\<close> and F' :: \<open>'a qupdate \<Rightarrow> 'd qupdate\<close> and G' :: \<open>'b qupdate \<Rightarrow> 'd qupdate\<close>
    apply (rule inv_comp_eqI)
    using qregister_raw_inj[OF \<open>qregister_raw H\<close>] qregister_raw_inj[OF \<open>qregister_raw G'\<close>]
    using inj_compose that by (auto simp add: ext f_inv_into_f subset_iff)
  assume [simp]: \<open>qregister F'\<close> \<open>qregister G'\<close>
  then show ?thesis
    using assms apply transfer
    using range_le_preserve H_cancel by (auto simp: qregister_raw_chain)
qed


lemma cregister_conversion_as_register:
  fixes F :: \<open>('a,'c) cregister\<close> and F' G'
  assumes \<open>cregister G\<close>
  assumes \<open>F = cregister_chain G F'\<close>
  shows \<open>cregister_conversion F G = F'\<close>
  apply (subst cregister_conversion_rename[where H=G and G'=cregister_id and F'=F'])
  using assms by auto
lemma qregister_conversion_as_register:
  fixes F :: \<open>('a,'c) qregister\<close> and F' G'
  assumes \<open>qregister G\<close>
  assumes \<open>F = qregister_chain G F'\<close>
  shows \<open>qregister_conversion F G = F'\<close>
  apply (subst qregister_conversion_rename[where H=G and G'=qregister_id and F'=F'])
  using assms by auto

(* lift_definition qregister_of_cregister :: \<open>('a,'b) cregister \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>F a. if cregister F then
      explicit_cblinfun (\<lambda>i j. if same_outside_cregister F i j then Rep_ell2 (a *\<^sub>V ket (getter F j)) (getter F i) else 0)
    else 0\<close>
   *)

lemma qregister_raw_permute_and_tensor1_cblinfun:
  assumes \<open>cregister F\<close>
  shows \<open>qregister_raw (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F))\<close>
proof -
  have \<open>\<forall>\<^sub>\<tau> 'c::type = permute_and_tensor1_cblinfun_basis (same_outside_cregister F).
        qregister_raw (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F))\<close>
  proof (rule with_type_mp[OF permute_and_tensor1_cblinfun_as_register])
    show \<open>equivp (same_outside_cregister F)\<close>
      by simp
    show \<open>bij_betw (getter F) (Collect (same_outside_cregister F a)) UNIV\<close> for a
      apply (rule bij_betw_byWitness[where f'=\<open>\<lambda>b. setter F b a\<close>])
      apply (auto simp add: same_outside_cregister_def[abs_def] assms)
      by (metis setter_getter_same setter_setter_same)
    fix Rep :: \<open>'c \<Rightarrow> 'b set\<close>
    define U where \<open>U = permute_and_tensor1_cblinfun_U Rep (getter F) (same_outside_cregister F)\<close>
    assume asm: \<open>(\<forall>A. sandwich U *\<^sub>V (A \<otimes>\<^sub>o id_cblinfun) =
                  permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) A)
          \<and> unitary U\<close>
    then have \<open>permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) = (sandwich U) o Laws_Quantum.Fst\<close>
      by (auto intro!: ext simp: Laws_Quantum.Fst_def)  
    moreover have \<open>qregister_raw \<dots>\<close>
      apply (rule register_comp)
      using asm by (simp_all add: unitary_sandwich_register)
    ultimately show \<open>qregister_raw (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F))\<close>
      by simp
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed


lift_definition qregister_of_cregister :: \<open>('a,'b) cregister \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>F a. if cregister F then permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) a else 0\<close>
  subgoal for F
    apply (cases \<open>cregister F\<close>)
    using qregister_raw_permute_and_tensor1_cblinfun[of F]
    by (auto simp add: non_qregister_raw_def[abs_def])
  by -

(* TODO remove *)
(* proof -
  fix F :: \<open>('a, 'b) cregister\<close>
  have *: \<open>\<forall>\<^sub>\<tau> 'c::type = permute_and_tensor1_cblinfun_basis (same_outside_cregister F).
        qregister_raw (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F))\<close> if \<open>cregister F\<close>
  proof (rule with_type_mp[OF permute_and_tensor1_cblinfun_as_register])
    show \<open>equivp (same_outside_cregister F)\<close>
      by simp
    show \<open>bij_betw (getter F) (Collect (same_outside_cregister F a)) UNIV\<close> for a
      apply (rule bij_betw_byWitness[where f'=\<open>\<lambda>b. setter F b a\<close>])
      apply (auto simp add: same_outside_cregister_def[abs_def] that)
      by (metis setter_getter_same setter_setter_same)
    fix Rep :: \<open>'c \<Rightarrow> 'b set\<close>
    define U where \<open>U = permute_and_tensor1_cblinfun_U Rep (getter F) (same_outside_cregister F)\<close>
    assume asm: \<open>(\<forall>A. sandwich U *\<^sub>V (A \<otimes>\<^sub>o id_cblinfun) =
                  permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) A)
          \<and> unitary U\<close>
    then have \<open>permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) = (sandwich U) o Laws_Quantum.Fst\<close>
      by (auto intro!: ext simp: Laws_Quantum.Fst_def)  
    moreover have \<open>qregister_raw \<dots>\<close>
      apply (rule register_comp)
      using asm by (simp_all add: unitary_sandwich_register)
    ultimately show \<open>qregister_raw (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F))\<close>
      by simp
  qed
  have \<open>qregister_raw (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F))\<close> if \<open>cregister F\<close>
    using *[OF that, cancel_with_type]
    by assumption
  then show \<open>(\<lambda>a. if cregister F
            then permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) a else 0)
       \<in> Collect qregister_raw \<union> {non_qregister_raw}\<close>
    apply (cases \<open>cregister F\<close>)
    by (auto simp: non_qregister_raw_def)
qed *)

lemma qregister_of_cregister_non_register[simp]: \<open>qregister_of_cregister non_cregister = non_qregister\<close>
proof -
  define t where \<open>t = non_cregister\<close>
  show \<open>qregister_of_cregister t = non_qregister\<close>
    apply (transfer fixing: t)
    apply (simp add: t_def)
    using non_qregister_raw_def by fastforce
qed

lemma qregister_qregister_of_cregister[simp]: \<open>qregister (qregister_of_cregister F) \<longleftrightarrow> cregister F\<close>
  apply (transfer fixing: F)
  apply (cases \<open>cregister F\<close>)
  using qregister_raw_permute_and_tensor1_cblinfun[of F]
  by auto

lemma qregister_of_cregister_Fst: \<open>qregister_of_cregister cFst = qFst\<close>
proof -
  have *: \<open>Rep_ell2 (apply_qregister (qregister_of_cregister cFst) (butterket i j) *\<^sub>V |x\<rangle>) y =
       Rep_ell2 (apply_qregister qFst (butterket i j) *\<^sub>V |x\<rangle>) y\<close> (is \<open>?lhs = ?rhs\<close>)
    for i j :: 'a and x y :: \<open>'a \<times> 'c\<close>
  proof -
    obtain x1 x2 where x12: \<open>x = (x1, x2)\<close> by force
    obtain y1 y2 where y12: \<open>y = (y1, y2)\<close> by force
    have 1: \<open>inj_on fst (Collect (same_outside_cregister cFst x))\<close> for x :: \<open>'a \<times> 'c\<close>
      by (smt (verit) equivp_def equivp_same_outside_cregister getter_cFst inj_onI mem_Collect_eq same_outside_cregister_def)
    have \<open>?lhs = (if same_outside_cregister cFst y x then Rep_ell2 (butterket i j *\<^sub>V |x1\<rangle>) y1 else 0)\<close>
      by (auto intro!: permute_and_tensor1_cblinfun_exists simp add: equivp_implies_part_equivp 
          qregister_of_cregister.rep_eq permute_and_tensor1_cblinfun_ket 1 x12 y12)
    also have \<open>\<dots> = ?rhs\<close>
      apply (auto simp add: qFst.rep_eq Fst_def x12 y12 tensor_op_ell2 cinner_ket
          simp flip: tensor_ell2_ket)
      by (auto simp add: ket.rep_eq zero_ell2.rep_eq same_outside_cregister_def 
          tensor_ell2_ket setter_cFst)
    finally show ?thesis
      by -
  qed
  have \<open>apply_qregister (qregister_of_cregister cFst) (butterket i j) =
           apply_qregister qFst (butterket i j)\<close> for i j :: 'a
    by (auto intro!: equal_ket Rep_ell2_inject[THEN iffD1] ext simp: * )
  then show ?thesis
    apply (auto intro!: apply_qregister_inject[THEN iffD1]
        weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
    using Axioms_Quantum.register_def cFst_register qregister.rep_eq qregister_qregister_of_cregister apply blast
    by (simp add: qFst.rep_eq weak_star_cont_register)
qed

lemma qregister_of_cregister_Snd: \<open>qregister_of_cregister cSnd = qSnd\<close>
proof -
  have *: \<open>Rep_ell2 (apply_qregister (qregister_of_cregister cSnd) (butterket i j) *\<^sub>V |x\<rangle>) y =
       Rep_ell2 (apply_qregister qSnd (butterket i j) *\<^sub>V |x\<rangle>) y\<close> (is \<open>?lhs = ?rhs\<close>)
    for i j :: 'a and x y :: \<open>'c \<times> 'a\<close>
  proof -
    obtain x1 x2 where x12: \<open>x = (x1, x2)\<close> by force
    obtain y1 y2 where y12: \<open>y = (y1, y2)\<close> by force
    have 1: \<open>inj_on snd (Collect (same_outside_cregister cSnd x))\<close> for x :: \<open>'c \<times> 'a\<close>
      by (smt (verit) equivp_def equivp_same_outside_cregister getter_cSnd inj_onI mem_Collect_eq same_outside_cregister_def)
    have \<open>?lhs = (if same_outside_cregister cSnd y x then Rep_ell2 (butterket i j *\<^sub>V |x2\<rangle>) y2 else 0)\<close>
      by (auto intro!: permute_and_tensor1_cblinfun_exists simp add: equivp_implies_part_equivp 
          qregister_of_cregister.rep_eq permute_and_tensor1_cblinfun_ket 1 x12 y12)
    also have \<open>\<dots> = ?rhs\<close>
      apply (auto simp add: qSnd.rep_eq Snd_def x12 y12 tensor_op_ell2 cinner_ket
          simp flip: tensor_ell2_ket)
      by (auto simp add: ket.rep_eq zero_ell2.rep_eq same_outside_cregister_def 
          tensor_ell2_ket setter_cSnd)
    finally show ?thesis
      by -
  qed
  have \<open>apply_qregister (qregister_of_cregister cSnd) (butterket i j) =
           apply_qregister qSnd (butterket i j)\<close> for i j :: 'a
    by (auto intro!: equal_ket Rep_ell2_inject[THEN iffD1] ext simp: * )
  then show ?thesis
    apply (auto intro!: apply_qregister_inject[THEN iffD1]
        weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
    using Axioms_Quantum.register_def cSnd_register qregister.rep_eq qregister_qregister_of_cregister apply blast
    by (simp add: qSnd.rep_eq weak_star_cont_register)
qed

lemmas qcompatible_FS_qregister_of_cregister[simp] =
  qcompatible_Fst_Snd[unfolded qregister_of_cregister_Fst[symmetric]]
  qcompatible_Fst_Snd[unfolded qregister_of_cregister_Snd[symmetric]]
  qcompatible_Fst_Snd[unfolded qregister_of_cregister_Fst[symmetric] qregister_of_cregister_Snd[symmetric]]
  qcompatible_Snd_Fst[unfolded qregister_of_cregister_Fst[symmetric]]
  qcompatible_Snd_Fst[unfolded qregister_of_cregister_Snd[symmetric]]
  qcompatible_Snd_Fst[unfolded qregister_of_cregister_Fst[symmetric] qregister_of_cregister_Snd[symmetric]]

lemma apply_qregister_of_cregister:
  assumes \<open>cregister F\<close>
  shows \<open>apply_qregister (qregister_of_cregister F) a =
          permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) a\<close>
  unfolding qregister_of_cregister.rep_eq using assms by simp


lemma apply_qregister_qregister_of_cregister_butterket:
  assumes \<open>cregister F\<close>
  shows \<open>apply_qregister (qregister_of_cregister F) (butterket x y) (ket z) =
          of_bool (y = getter F z) *\<^sub>C ket (setter F x z)\<close>
proof (rule Rep_ell2_inject[THEN iffD1], rule ext)
  fix w
  have \<open>Rep_ell2 (apply_qregister (qregister_of_cregister F) (butterket x y) *\<^sub>V |z\<rangle>) w
      = Rep_ell2 (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) (butterket x y) (ket z)) w\<close>
    using \<open>cregister F\<close> by (simp add: apply_qregister_of_cregister)
  also have \<open>\<dots> = of_bool (same_outside_cregister F w z) * Rep_ell2 (butterket x y *\<^sub>V |getter F z\<rangle>) (getter F w)\<close>
    apply (subst permute_and_tensor1_cblinfun_ket)
     apply (rule permute_and_tensor1_cblinfun_exists)
      apply (simp add: equivp_implies_part_equivp)
     apply (smt (verit, best) inj_onI mem_Collect_eq same_outside_cregister_def setter_getter_same setter_setter_same)
    by simp
  also have \<open>\<dots> = of_bool (same_outside_cregister F w z \<and> x = getter F w \<and> y = getter F z)\<close>
    by (auto simp add: cinner_ket ket.rep_eq zero_ell2.rep_eq)
  also have \<open>\<dots> = of_bool (w = setter F x z \<and> y = getter F z)\<close>
    apply (rule arg_cong[where f=of_bool])
    by (auto simp: same_outside_cregister_def \<open>cregister F\<close>)
  also have \<open>\<dots> = Rep_ell2 (of_bool (y = getter F z) *\<^sub>C |setter F x z\<rangle>) w\<close>
    by (auto simp add: ket.rep_eq zero_ell2.rep_eq)
  finally show \<open>Rep_ell2 (apply_qregister (qregister_of_cregister F) (butterket x y) *\<^sub>V |z\<rangle>) w
              = Rep_ell2 (of_bool (y = getter F z) *\<^sub>C |setter F x z\<rangle>) w\<close>
    by -
qed

lemma apply_qregister_weak_star_continuous[simp]:
  \<open>continuous_map weak_star_topology weak_star_topology (apply_qregister F)\<close>
  apply transfer
  by (auto simp: non_qregister_raw_def[abs_def] weak_star_cont_register)

lemma qcompatible_qregister_of_cregister[simp]:
  \<open>qcompatible (qregister_of_cregister F) (qregister_of_cregister G) \<longleftrightarrow> ccompatible F G\<close>
proof (rule iffI)
  assume compat: \<open>ccompatible F G\<close>
  then have [simp]: \<open>cregister F\<close> \<open>cregister G\<close>
    using ccompatible_register1 ccompatible_register2 by auto

  have [simp]: \<open>getter F (setter G b m) = getter F m\<close> for b m
    by (simp add: compat)
  have [simp]: \<open>getter G (setter F a m) = getter G m\<close> for a m
    by (simp add: ccompatible_sym compat)
  have [simp]: \<open>setter F a (setter G b z) = setter G b (setter F a z)\<close> for a b z
    by (simp add: compat setter_setter_compat)

  have [simp]: \<open>clinear (\<lambda>a. apply_qregister X a o\<^sub>C\<^sub>L B)\<close> for a B X
    using clinear_compose[OF clinear_apply_qregister[of X] clinear_cblinfun_compose_left[of B]]
    by (simp add: o_def)
  have [simp]: \<open>clinear (\<lambda>a. B o\<^sub>C\<^sub>L apply_qregister X a)\<close> for a B X
    using clinear_compose[OF clinear_apply_qregister[of X] clinear_cblinfun_compose_right[of B]]
    by (simp add: o_def)
  have [intro]: \<open>continuous_map weak_star_topology weak_star_topology 
         (\<lambda>a. apply_qregister X a o\<^sub>C\<^sub>L B)\<close> for B X
    using continuous_map_compose[OF apply_qregister_weak_star_continuous[of X] continuous_map_right_comp_weak_star[of B]]
    by (simp add: o_def)
  have [intro]: \<open>continuous_map weak_star_topology weak_star_topology 
         (\<lambda>a. B o\<^sub>C\<^sub>L apply_qregister X a)\<close> for B X
    using continuous_map_compose[OF apply_qregister_weak_star_continuous[of X] continuous_map_left_comp_weak_star[of B]]
    by (simp add: o_def)

  have *: \<open>apply_qregister (qregister_of_cregister F) (butterket x y) *\<^sub>V apply_qregister (qregister_of_cregister G) (butterket x' y') *\<^sub>V ket z
      = apply_qregister (qregister_of_cregister G) (butterket x' y') *\<^sub>V apply_qregister (qregister_of_cregister F) (butterket x y) *\<^sub>V ket z\<close>
    for x y x' y' z
    by (auto simp add: apply_qregister_qregister_of_cregister_butterket)
  have *: \<open>apply_qregister (qregister_of_cregister F) (butterket x y) o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister G) (butterket x' y')
      = apply_qregister (qregister_of_cregister G) (butterket x' y') o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister F) (butterket x y)\<close>
    for x y x' y'
    apply (rule equal_ket)
    using *[of x y x' y']
    by simp
  have *: \<open>apply_qregister (qregister_of_cregister F) a o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister G) (butterket x' y')
      = apply_qregister (qregister_of_cregister G) (butterket x' y') o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister F) a\<close>
    for x' y' a
    apply (rule fun_cong[where x=a])
    apply (rule weak_star_clinear_eq_butterfly_ketI)
    using * by auto
  have \<open>apply_qregister (qregister_of_cregister F) a o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister G) b
      = apply_qregister (qregister_of_cregister G) b o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister F) a\<close>
    for a b
    apply (rule fun_cong[where x=b])
    apply (rule weak_star_clinear_eq_butterfly_ketI)
    using * by auto
  then show \<open>qcompatible (qregister_of_cregister F) (qregister_of_cregister G)\<close>
    by (simp add: qcompatibleI)
next
  assume compat: \<open>qcompatible (qregister_of_cregister F) (qregister_of_cregister G)\<close>
  then have qqF: \<open>qregister (qregister_of_cregister F)\<close> and qqG: \<open>qregister (qregister_of_cregister G)\<close>
    by (auto simp add: qcompatible_def)
  from qqF have [simp]: \<open>cregister F\<close>
    apply (transfer fixing: F)
    apply (cases \<open>cregister F\<close>)
    by auto
  from qqG have [simp]: \<open>cregister G\<close>
    apply (transfer fixing: G)
    apply (cases \<open>cregister G\<close>)
    by auto

  have \<open>setter F a (setter G b m) = setter G b (setter F a m)\<close> for a b m
  proof (rule ccontr)
    assume assm: \<open>setter F a (setter G b m) \<noteq> setter G b (setter F a m)\<close>
    have *: \<open>(apply_qregister (qregister_of_cregister F) (butterket a a') o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister G) (butterket b b')) *\<^sub>V ket m
      = (apply_qregister (qregister_of_cregister G) (butterket b b') o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister F) (butterket a a')) *\<^sub>V ket m\<close>
      for a' b'
      by (simp add: compat qcompatible_commute)
    have *: \<open>of_bool (b' = getter G m \<and> a' = getter F (setter G b m)) *\<^sub>C |setter F a (setter G b m)\<rangle>
             = of_bool (a' = getter F m \<and> b' = getter G (setter F a m)) *\<^sub>C |setter G b (setter F a m)\<rangle>\<close>
      for a' b'
      using *[of a' b']
      by (simp add: apply_qregister_qregister_of_cregister_butterket cblinfun.scaleC_right flip: of_bool_conj)
    with assm have \<open>\<not> (b' = getter G m \<and> a' = getter F (setter G b m)) \<and> \<not> (a' = getter F m \<and> b' = getter G (setter F a m))\<close> 
      for a' b'
      by (smt (z3) complex_vector.scale_cancel_left ket_injective of_bool_eq(1) of_bool_eq_iff)
    then show False
      by blast
  qed
  then show \<open>ccompatible F G\<close>
    apply (rule setter_setter_compatI[rotated -1])
    by simp_all
qed

lemma cregister_eqI_setter_raw: 
  assumes [simp]: \<open>cregister_raw F\<close> \<open>cregister_raw G\<close>
  assumes eq: \<open>\<And>a m. Axioms_Classical.setter F a m = Axioms_Classical.setter G a m\<close>
  shows \<open>F = G\<close>
proof -
  from eq \<open>cregister_raw F\<close> \<open>cregister_raw G\<close> have \<open>Axioms_Classical.getter F = Axioms_Classical.getter G\<close>
    by (auto simp: Axioms_Classical.getter_def)
  with eq[abs_def]
  have \<open>register_from_getter_setter (Axioms_Classical.getter F) (Axioms_Classical.setter F)
      = register_from_getter_setter (Axioms_Classical.getter G) (Axioms_Classical.setter G)\<close>
    by simp
  then show ?thesis
    by (simp add: register_from_getter_setter_of_getter_setter)
qed

lemma cregister_eqI_setter: 
  assumes \<open>cregister F\<close> \<open>cregister G\<close>
  assumes eq: \<open>\<And>a m. setter F a m = setter G a m\<close>
  shows \<open>F = G\<close>
  using assms apply transfer
  by (auto intro!: cregister_eqI_setter_raw)

lemma separating_butterkey:
  \<open>Laws_Quantum.separating TYPE('b) (range (case_prod butterket))\<close>
proof -
  thm weak_star_clinear_eq_butterfly_ketI
  have \<open>F = G\<close> if \<open>\<And>a b. F (butterket a b) = G (butterket a b)\<close> 
    and \<open>Axioms_Quantum.preregister F\<close> and \<open>Axioms_Quantum.preregister G\<close> for F G :: \<open>'a qupdate \<Rightarrow> 'b qupdate\<close>
    apply (rule weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
    using that
    by (auto simp: Axioms_Quantum.preregister_def bounded_clinear.clinear)
  then show ?thesis
    by (auto simp add: Laws_Quantum.separating_def)
qed

lemma separating_nonempty: \<open>\<not> (X \<subseteq> {0})\<close> if sep: \<open>separating TYPE('b) X\<close> for X :: \<open>'a qupdate set\<close>
proof (rule notI)
  assume \<open>X \<subseteq> {0}\<close>
  have \<open>preregister 0\<close>
    by (simp add: Axioms_Quantum.preregister_def zero_fun_def)
  fix x
  define F :: \<open>'a qupdate \<Rightarrow> 'b qupdate\<close> where \<open>F a = (ket x \<bullet>\<^sub>C (a *\<^sub>V ket x)) *\<^sub>C id_cblinfun\<close> for a
  have \<open>bounded_clinear F\<close>
    unfolding F_def[abs_def]
    by (intro bounded_linear_intros)
  moreover have \<open>continuous_map weak_star_topology weak_star_topology F\<close>
  proof -
    note continuous_map_compose[trans]
    have \<open>continuous_map weak_star_topology cweak_operator_topology (\<lambda>f :: 'a qupdate. f)\<close>
      by (simp add: wot_weaker_than_weak_star)
    also have \<open>continuous_map cweak_operator_topology euclidean (\<lambda>a. ket x \<bullet>\<^sub>C (a *\<^sub>V ket x))\<close>
      by (simp add: cweak_operator_topology_continuous_evaluation)
    also have \<open>continuous_map euclidean euclidean (\<lambda>c. c *\<^sub>C (id_cblinfun :: 'b qupdate))\<close>
      by (auto intro!: continuous_map_iff_continuous2[THEN iffD2] continuous_at_imp_continuous_on)
    also have \<open>continuous_map euclidean weak_star_topology (\<lambda>f :: 'b qupdate. f)\<close>
      by (simp add: weak_star_topology_weaker_than_euclidean)
    finally show ?thesis
      by (simp add: o_def F_def[abs_def])
  qed
  ultimately have \<open>preregister F\<close>
    by (simp add: Axioms_Quantum.preregister_def)
  have \<open>0 a = F a\<close> if \<open>a \<in> X\<close> for a
    using \<open>X \<subseteq> {0}\<close> that
    by (auto simp: F_def)
  with sep have \<open>0 = F\<close>
    by (simp add: Laws_Quantum.register_eqI \<open>Axioms_Quantum.preregister 0\<close> \<open>Axioms_Quantum.preregister F\<close>)
  then have \<open>0 (butterket x x) = F (butterket x x)\<close>
    by simp
  then show False
    by (simp add: F_def)
qed

lemma qregister_eqI_separating:
  fixes F G :: \<open>('a,'b) qregister\<close>
  assumes sep: \<open>Laws_Quantum.separating TYPE('b) X\<close>
  assumes eq: \<open>\<And>x. x\<in>X \<Longrightarrow> apply_qregister F x = apply_qregister G x\<close>
  shows \<open>F = G\<close>
proof -
  obtain x where \<open>x \<in> X\<close> and \<open>x \<noteq> 0\<close>
    using separating_nonempty[OF sep]
    by auto

  consider (reg) \<open>qregister F\<close> \<open>qregister G\<close> | (notreg) \<open>\<not> qregister F\<close> \<open>\<not> qregister G\<close>
    | (notF) \<open>\<not> qregister F\<close> \<open>qregister G\<close> | (notG) \<open>qregister F\<close> \<open>\<not> qregister G\<close>
    by auto
  then show ?thesis
  proof cases
    case reg
    then show ?thesis
      using assms apply transfer
      by (auto simp: Laws_Quantum.separating_def)
  next
    case notreg
    then show ?thesis
      by (simp add: non_qregister)
  next
    case notF
    have \<open>apply_qregister F x = 0\<close>
      using non_qregister notF(1) by force
    moreover have \<open>apply_qregister G x \<noteq> 0\<close>
      using \<open>x \<noteq> 0\<close> inj_qregister[OF notF(2)] injD by fastforce
    moreover have \<open>apply_qregister F x = apply_qregister G x\<close>
      using eq \<open>x \<in> X\<close> by simp
    ultimately have False
      by simp
    then show ?thesis
      by simp
  next
    case notG
    have \<open>apply_qregister G x = 0\<close>
      using non_qregister notG(2) by force
    moreover have \<open>apply_qregister F x \<noteq> 0\<close>
      using \<open>x \<noteq> 0\<close> inj_qregister[OF notG(1)] injD by fastforce
    moreover have \<open>apply_qregister F x = apply_qregister G x\<close>
      using eq \<open>x \<in> X\<close> by simp
    ultimately have False
      by simp
    then show ?thesis
      by simp
  qed
qed


lemma qregister_of_cregister_pair: 
  \<open>qregister_of_cregister (cregister_pair x y) = qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)\<close>
proof (cases \<open>ccompatible x y\<close>)
  case True
  then have [simp]: \<open>ccompatible x y\<close> \<open>cregister x\<close> \<open>cregister y\<close>
    by (auto simp add: ccompatible_def)
  have \<open>apply_qregister (qregister_of_cregister (cregister_pair x y)) (butterket k l) *\<^sub>V ket z =
        apply_qregister (qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)) (butterket k l) *\<^sub>V ket z\<close> for k l z
  proof -
    obtain k1 k2 where [simp]: \<open>k = (k1,k2)\<close>
      by force
    obtain l1 l2 where [simp]: \<open>l = (l1,l2)\<close>
      by force
    show ?thesis
      apply (simp add: apply_qregister_pair flip: tensor_ell2_ket tensor_butterfly)
      by (simp add: apply_qregister_qregister_of_cregister_butterket getter_pair setter_pair
          tensor_ell2_ket tensor_butterfly)
  qed
  then have \<open>apply_qregister (qregister_of_cregister (cregister_pair x y)) (butterket k l) =
        apply_qregister (qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)) (butterket k l)\<close> for k l
    by (simp add: equal_ket)
  then show ?thesis
    apply (rule_tac qregister_eqI_separating[OF separating_butterkey])
    by auto
next
  case False
  then have \<open>\<not> qcompatible (qregister_of_cregister x) (qregister_of_cregister y)\<close>
    by simp
  then have 1: \<open>qregister_pair (qregister_of_cregister x) (qregister_of_cregister y) = non_qregister\<close>
    using non_qregister by blast
  from False have 2: \<open>cregister_pair x y = non_cregister\<close>
    using non_cregister by blast
  from 1 2 show ?thesis
    by simp
qed

lemma qregister_of_cregister_chain: \<open>qregister_of_cregister (cregister_chain x y) = qregister_chain (qregister_of_cregister x) (qregister_of_cregister y)\<close>
  sorry

typedecl cl
typedecl qu
instance qu :: default ..

type_synonym 'a cvariable = \<open>('a,cl) cregister\<close>
type_synonym 'a qvariable = \<open>('a,qu) qregister\<close>

type_synonym QVARIABLE = \<open>qu QREGISTER\<close>
type_synonym CVARIABLE = \<open>cl CREGISTER\<close>

lift_definition transform_qregister :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>(U :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2). if unitary U then cblinfun_apply (sandwich U) else non_qregister_raw\<close>
  by (auto simp: unitary_sandwich_register)

lemma qregister_transform_qregister[simp]: \<open>unitary U \<Longrightarrow> qregister (transform_qregister U)\<close>
  apply (transfer fixing: U) by (auto simp: unitary_sandwich_register)

lemma apply_qregister_transform_qregister: \<open>unitary U \<Longrightarrow> apply_qregister (transform_qregister U) a = sandwich U a\<close>
  apply (transfer fixing: U a) by (auto simp: unitary_sandwich_register sandwich_apply)

(* datatype 'a vtree = VTree_Singleton 'a | VTree_Concat "'a vtree" "'a vtree" | VTree_Unit *)

section \<open>Distinct variables\<close>

abbreviation (input) "distinct_qvars Q == qregister Q" (* LEGACY *)
abbreviation (input) "distinct_cvars Q == cregister Q" (* LEGACY *)

lemma distinct_qvars_split1:
  "distinct_qvars (qregister_pair (qregister_pair Q R) S) = (distinct_qvars (qregister_pair Q R) \<and> distinct_qvars (qregister_pair Q S) \<and> distinct_qvars (qregister_pair R S))"
  using qcompatible3 by blast
lemma distinct_qvars_swap: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> distinct_qvars (qregister_pair R Q)"
  using qcompatible_sym by auto
lemma distinct_qvars_split2: "distinct_qvars (qregister_pair S (qregister_pair Q R)) = (distinct_qvars (qregister_pair Q R) \<and> distinct_qvars (qregister_pair Q S) \<and> distinct_qvars (qregister_pair R S))"
  by (metis qcompatible3 qcompatible_sym)
lemma distinct_qvars_concat_unit1[simp]: "distinct_qvars (qregister_pair Q empty_qregister) = distinct_qvars Q" for Q::"'a qvariable"
  using qcompatible_QQcompatible qcompatible_empty by auto
lemma distinct_qvars_concat_unit2[simp]: "distinct_qvars (qregister_pair empty_qregister Q) = distinct_qvars Q" for Q::"'a::finite qvariable"
  using qcompatible_QQcompatible qcompatible_empty qcompatible_sym by blast
lemma distinct_qvars_unit[simp]: "distinct_qvars empty_qregister"
  by (simp add: )

lemma distinct_qvarsL: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> distinct_qvars Q"
  by (simp add: qcompatible_QQcompatible)
lemma distinct_qvarsR: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> distinct_qvars R"
  by (simp add: qcompatible_def)

lemma distinct_cvars_swap: "distinct_cvars (cregister_pair Q R) \<Longrightarrow> distinct_cvars (cregister_pair R Q)"
  using ccompatible_sym by blast
lemma distinct_cvars_split2: "distinct_cvars (cregister_pair S (cregister_pair Q R)) = (distinct_cvars (cregister_pair Q R) \<and> distinct_cvars (cregister_pair Q S) \<and> distinct_cvars (cregister_pair R S))"
  by (metis ccompatible3 distinct_cvars_swap)

section \<open>Indexed variables\<close>

type_synonym cl2 = \<open>cl \<times> cl\<close>
type_synonym qu2 = \<open>qu \<times> qu\<close>

type_synonym 'a c2variable = \<open>('a,cl2) cregister\<close>
type_synonym 'a q2variable = \<open>('a,qu2) qregister\<close>

definition index_cvar :: \<open>bool \<Rightarrow> 'a cvariable \<Rightarrow> 'a c2variable\<close> where
  \<open>index_cvar b x = cregister_chain (if b then cFst else cSnd) x\<close>
definition index_qvar :: \<open>bool \<Rightarrow> 'a qvariable \<Rightarrow> 'a q2variable\<close> where
  \<open>index_qvar b x = qregister_chain (if b then qFst else qSnd) x\<close>

definition index_flip_cvar :: \<open>'a c2variable \<Rightarrow> 'a c2variable\<close> where
  \<open>index_flip_cvar x = cregister_chain cswap x\<close>
definition index_flip_qvar :: \<open>'a q2variable \<Rightarrow> 'a q2variable\<close> where
  \<open>index_flip_qvar x = qregister_chain qswap x\<close>

lemma index_flip_qvar_register_pair[simp]: \<open>index_flip_qvar (qregister_pair Q R) = qregister_pair (index_flip_qvar Q) (index_flip_qvar R)\<close>
  unfolding index_flip_qvar_def
  apply (cases \<open>qcompatible Q R\<close>)
  by (simp_all add: qregister_chain_pair)

lemma index_flip_qvar_chain[simp]: \<open>index_flip_qvar (qregister_chain Q R) = qregister_chain (index_flip_qvar Q) R\<close>
  unfolding index_flip_qvar_def
  by (simp add: qregister_chain_assoc)

lemma index_flip_qvar_Fst[simp]: \<open>index_flip_qvar qFst = qSnd\<close>
  unfolding index_flip_qvar_def
  by (simp add: qcompatible_Fst_Snd qcompatible_sym qregister_chain_pair_Fst qswap_def)

lemma index_flip_qvar_Snd[simp]: \<open>index_flip_qvar qSnd = qFst\<close>
  by (simp add: index_flip_qvar_def qcompatible_Fst_Snd qcompatible_sym qregister_chain_pair_Snd qswap_def)

definition index_flip_mem2 :: "qu2 \<Rightarrow> qu2" where \<open>index_flip_mem2 = (\<lambda>(x,y). (y,x))\<close>

definition swap_cvariables_mem2 :: "'a c2variable \<Rightarrow> 'a c2variable \<Rightarrow> (cl2 \<Rightarrow> cl2)" where
  \<open>swap_cvariables_mem2 x y m = apply_cregister_total (cregister_pair x y) (\<lambda>(a,b). (b,a)) m\<close>

definition swap_variables_qvars :: \<open>'a q2variable \<Rightarrow> 'a q2variable \<Rightarrow> 'b q2variable \<Rightarrow> 'b q2variable\<close> where
  \<open>swap_variables_qvars Q Q' R = 
    qregister_chain (transform_qregister (apply_qregister (qregister_pair Q Q') swap_ell2)) R\<close>

section \<open>Unsorted\<close>

lemma getter_Snd_chain_swap[simp]: \<open>getter (cregister_chain cSnd G) (prod.swap m) = getter (cregister_chain cFst G) m\<close>
  by (simp add: getter_chain)
lemma getter_Fst_chain_swap[simp]: \<open>getter (cregister_chain cFst G) (prod.swap m) = getter (cregister_chain cSnd G) m\<close>
  by (simp add: getter_chain)

(* axiomatization lift_pure_state :: \<open>('a,'b) qregister \<Rightarrow> 'a ell2 \<Rightarrow> 'b ell2\<close> *)

named_theorems translate_to_index_registers


section \<open>ML code\<close>

(* TODO remove *)
lemma distinct_cvarsL: "distinct_cvars (cregister_pair Q R) \<Longrightarrow> distinct_cvars Q"
  by (rule ccompatible_register1)
lemma distinct_cvarsR: "distinct_cvars (cregister_pair Q R) \<Longrightarrow> distinct_cvars R"
  by (rule ccompatible_register2)

ML_file "prog_variables.ML"

section \<open>Syntax\<close>


nonterminal variable_list_args
nonterminal variable_nth
nonterminal variable_nth'
syntax
  "_qvariable_nth" :: "'a \<Rightarrow> 'b"
  "_cvariable_nth" :: "'a \<Rightarrow> 'b"
  "_qvariable_nth'" :: "'a \<Rightarrow> 'b"
  "_cvariable_nth'" :: "'a \<Rightarrow> 'b"
  "_empty_qregister"      :: "'a"        ("(1'[|'|])")
  "_empty_qregister"      :: "'a"        ("(1'\<lbrakk>'\<rbrakk>)")
  "_empty_qregister"      :: "'a"        ("(1'[|'|]\<^sub>q)")
  "_empty_qregister"      :: "'a"        ("(1'\<lbrakk>'\<rbrakk>\<^sub>q)")
  "_empty_cregister"      :: "'a"        ("(1'[|'|]\<^sub>c)")
  "_empty_cregister"      :: "'a"        ("(1'\<lbrakk>'\<rbrakk>\<^sub>c)")
  "_qvariables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'[|_'|])")
  "_qvariables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'[|_'|]\<^sub>q)")
  "_cvariables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'[|_'|]\<^sub>c)")
  "_qvariables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_'\<rbrakk>)")
  "_qvariables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_'\<rbrakk>\<^sub>q)")
  "_cvariables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_'\<rbrakk>\<^sub>c)")
  "_variable_list_arg_nth"  :: "'a \<Rightarrow> variable_list_args"                   ("#_")  (* Instead of 'a, would like to match only natural numbers *)
  "_variable_list_arg_nth'"  :: "'a \<Rightarrow> variable_list_args"                   ("#_.")
  "_variable_list_arg"  :: "'a \<Rightarrow> variable_list_args"                   ("_")
  "_variable_list_args_nth"  :: "'a \<Rightarrow> variable_list_args \<Rightarrow> variable_list_args"                   ("#_,/ _")
  "_variable_list_args_nth'"  :: "'a \<Rightarrow> variable_list_args \<Rightarrow> variable_list_args"                   ("#_.,/ _")
  "_variable_list_args" :: "'a \<Rightarrow> variable_list_args \<Rightarrow> variable_list_args"     ("_,/ _")

  "_qvariable_conversion"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<mapsto> _'\<rbrakk>)")
  "_qvariable_conversion"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<mapsto> _'\<rbrakk>\<^sub>q)")
  "_cvariable_conversion"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<mapsto> _'\<rbrakk>\<^sub>c)")
  "_qvariable_le"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<le> _'\<rbrakk>)")
  "_qvariable_le"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<le> _'\<rbrakk>\<^sub>q)")
  "_cvariable_le"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<le> _'\<rbrakk>\<^sub>c)")

translations
  "_empty_qregister" \<rightleftharpoons> "CONST empty_qregister :: (unit, _) qregister"
  "_empty_cregister" \<rightleftharpoons> "CONST empty_cregister :: (unit, _) cregister"
  "_qvariables (_variable_list_args x y)" \<rightleftharpoons> "CONST qregister_pair x (_qvariables y)"
  "_cvariables (_variable_list_args x y)" \<rightleftharpoons> "CONST cregister_pair x (_cvariables y)"
  "_qvariables (_variable_list_args_nth x y)" \<rightleftharpoons> "CONST qregister_pair (_qvariable_nth x) (_qvariables y)"
  "_cvariables (_variable_list_args_nth x y)" \<rightleftharpoons> "CONST cregister_pair (_cvariable_nth x) (_cvariables y)"
  "_qvariables (_variable_list_args_nth' x y)" \<rightleftharpoons> "CONST qregister_pair (_qvariable_nth' x) (_qvariables y)"
  "_cvariables (_variable_list_args_nth' x y)" \<rightleftharpoons> "CONST cregister_pair (_cvariable_nth' x) (_cvariables y)"
  "_qvariables (_variable_list_arg x)" \<rightharpoonup> "x"
  "_cvariables (_variable_list_arg x)" \<rightharpoonup> "x"
  "_qvariables (_variable_list_arg_nth x)" \<rightleftharpoons> "_qvariable_nth x"
  "_cvariables (_variable_list_arg_nth x)" \<rightleftharpoons> "_cvariable_nth x"
  "_qvariables (_variable_list_arg_nth' x)" \<rightleftharpoons> "_qvariable_nth' x"
  "_cvariables (_variable_list_arg_nth' x)" \<rightleftharpoons> "_cvariable_nth' x"

  "_qvariables (_variable_list_args x y)" \<leftharpoondown> "CONST qregister_pair x y"
  "_cvariables (_variable_list_args x y)" \<leftharpoondown> "CONST cregister_pair x y"
  "_qvariables (_variable_list_args x (_variable_list_args y z))" \<leftharpoondown> "_qvariables (_variable_list_args x (_qvariables (_variable_list_args y z)))"
  "_cvariables (_variable_list_args x (_variable_list_args y z))" \<leftharpoondown> "_cvariables (_variable_list_args x (_cvariables (_variable_list_args y z)))"

  "_qvariable_conversion x y" \<rightharpoonup> "CONST qregister_conversion (_qvariables x) (_qvariables y)"
  "_qvariable_conversion x y" \<leftharpoondown> "CONST qregister_conversion x y"
  "_qvariable_conversion x y" \<leftharpoondown> "_qvariable_conversion (_qvariables x) y"
  "_qvariable_conversion x y" \<leftharpoondown> "_qvariable_conversion x (_qvariables y)"

  "_cvariable_conversion x y" \<rightharpoonup> "CONST cregister_conversion (_cvariables x) (_cvariables y)"
  "_cvariable_conversion x y" \<leftharpoondown> "CONST cregister_conversion x y"
  "_cvariable_conversion x y" \<leftharpoondown> "_cvariable_conversion (_cvariables x) y"
  "_cvariable_conversion x y" \<leftharpoondown> "_cvariable_conversion x (_cvariables y)"

  "_qvariable_le x y" \<rightharpoonup> "CONST qregister_le (_qvariables x) (_qvariables y)"
  "_qvariable_le x y" \<leftharpoondown> "CONST qregister_le x y"
  "_qvariable_le x y" \<leftharpoondown> "_qvariable_le (_qvariables x) y"
  "_qvariable_le x y" \<leftharpoondown> "_qvariable_le x (_qvariables y)"

  "_cvariable_le x y" \<rightharpoonup> "CONST cregister_le (_cvariables x) (_cvariables y)"
  "_cvariable_le x y" \<leftharpoondown> "CONST cregister_le x y"
  "_cvariable_le x y" \<leftharpoondown> "_cvariable_le (_cvariables x) y"
  "_cvariable_le x y" \<leftharpoondown> "_cvariable_le x (_cvariables y)"

parse_translation
  \<open>let open Prog_Variables in
   [(\<^syntax_const>\<open>_qvariable_nth\<close>,  fn ctxt => fn [nt] => register_n Quantum   false (Misc.dest_number_syntax nt)),
    (\<^syntax_const>\<open>_qvariable_nth'\<close>, fn ctxt => fn [nt] => register_n Quantum   true  (Misc.dest_number_syntax nt)),
    (\<^syntax_const>\<open>_cvariable_nth\<close>,  fn ctxt => fn [nt] => register_n Classical false (Misc.dest_number_syntax nt)),
    (\<^syntax_const>\<open>_cvariable_nth'\<close>, fn ctxt => fn [nt] => register_n Classical true  (Misc.dest_number_syntax nt))] end\<close>

translations
  "_qvariable_nth (CONST Suc CONST zero)" \<leftharpoondown> "CONST qFst"
  "_qvariable_nth' (CONST Suc (CONST Suc CONST zero))" \<leftharpoondown> "CONST qSnd"
(*   "_qvariable_nth (CONST Suc n)" \<leftharpoondown> "CONST qregister_chain (_qvariables (_variable_list_arg_nth' (CONST Suc (CONST Suc CONST zero)))) (_qvariables (_variable_list_arg_nth n))"
  "_qvariable_nth' (CONST Suc n)" \<leftharpoondown> "CONST qregister_chain (_qvariables (_variable_list_arg_nth' (CONST Suc (CONST Suc CONST zero)))) (_qvariables (_variable_list_arg_nth' n))" *)
  "_qvariable_nth (CONST Suc n)" \<leftharpoondown> "CONST qregister_chain (_qvariables (_variable_list_arg_nth' 2)) (_qvariables (_variable_list_arg_nth n))"
  "_qvariable_nth' (CONST Suc n)" \<leftharpoondown> "CONST qregister_chain (_qvariables (_variable_list_arg_nth' 2)) (_qvariables (_variable_list_arg_nth' n))"

  "_cvariable_nth (CONST Suc CONST zero)" \<leftharpoondown> "CONST cFst"
  "_cvariable_nth' (CONST Suc (CONST Suc CONST zero))" \<leftharpoondown> "CONST cSnd"
(*   "_cvariable_nth (CONST Suc n)" \<leftharpoondown> "CONST cregister_chain (_cvariables (_variable_list_arg_nth' (CONST Suc (CONST Suc CONST zero)))) (_cvariables (_variable_list_arg_nth n))"
  "_cvariable_nth' (CONST Suc n)" \<leftharpoondown> "CONST cregister_chain (_cvariables (_variable_list_arg_nth' (CONST Suc (CONST Suc CONST zero)))) (_cvariables (_variable_list_arg_nth' n))" *)
  "_cvariable_nth (CONST Suc n)" \<leftharpoondown> "CONST cregister_chain (_cvariables (_variable_list_arg_nth' 2)) (_cvariables (_variable_list_arg_nth n))"
  "_cvariable_nth' (CONST Suc n)" \<leftharpoondown> "CONST cregister_chain (_cvariables (_variable_list_arg_nth' 2)) (_cvariables (_variable_list_arg_nth' n))"

(* Does not work: *)
print_translation
  \<open>let
    fun count (Const(\<^const_name>\<open>zero\<close>,_)) = 0
      | count (Const(\<^const_name>\<open>Suc\<close>,_) $ t) = count t + 1
  in
  [(\<^syntax_const>\<open>_variable_list_arg_nth'\<close>, fn ctxt => fn [t] => HOLogic.mk_number dummyT (count t))]
  end\<close>

translations
  "_variable_list_arg_nth' 1" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc CONST zero)"
  "_variable_list_arg_nth' 2" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc CONST zero))"
  "_variable_list_arg_nth' 3" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc CONST zero)))"
  "_variable_list_arg_nth' 4" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero))))"
  "_variable_list_arg_nth' 5" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero)))))"
  "_variable_list_arg_nth' 6" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero))))))"
  "_variable_list_arg_nth' 7" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero)))))))"
  "_variable_list_arg_nth' 8" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero))))))))"
  "_variable_list_arg_nth' 9" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero)))))))))"

  "_variable_list_arg_nth' 3" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc 2)"
  "_variable_list_arg_nth' 4" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc 2))"
  "_variable_list_arg_nth' 5" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc 2)))"
  "_variable_list_arg_nth' 6" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc 2))))"
  "_variable_list_arg_nth' 7" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 2)))))"
  "_variable_list_arg_nth' 8" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 2))))))"
  "_variable_list_arg_nth' 9" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 2)))))))"

  "_variable_list_arg_nth 1" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc CONST zero)"
  "_variable_list_arg_nth 2" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc CONST zero))"
  "_variable_list_arg_nth 3" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc CONST zero)))"
  "_variable_list_arg_nth 4" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero))))"
  "_variable_list_arg_nth 5" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero)))))"
  "_variable_list_arg_nth 6" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero))))))"
  "_variable_list_arg_nth 7" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero)))))))"
  "_variable_list_arg_nth 8" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero))))))))"
  "_variable_list_arg_nth 9" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero)))))))))"

  "_variable_list_arg_nth 2" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc 1)"
  "_variable_list_arg_nth 3" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc 1))"
  "_variable_list_arg_nth 4" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc 1)))"
  "_variable_list_arg_nth 5" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc 1))))"
  "_variable_list_arg_nth 6" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 1)))))"
  "_variable_list_arg_nth 7" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 1))))))"
  "_variable_list_arg_nth 8" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 1)))))))"
  "_variable_list_arg_nth 9" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 1))))))))"

term \<open>\<lbrakk>#3\<rbrakk>\<^sub>q\<close>

section \<open>Simprocs\<close>

(* A simproc that utters warnings whenever the simplifier tries to prove a distinct_qvars statement with distinct, explicitly listed variables but can't *)
(* syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars \<lbrakk>_\<rbrakk>")
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars [|_|]") *)
(* LEGACY *)
abbreviation (input) \<open>declared_qvars Q \<equiv> qregister Q\<close>

(* parse_translation \<open>[("_declared_qvars", Prog_Variables.declared_qvars_parse_tr)]\<close> *)

(* simproc_setup warn_declared_qvars ("variable_name q") = Prog_Variables.warn_declared_qvars_simproc *)

(* simproc_setup index_var ("index_var lr v") = Prog_Variables.index_var_simproc *)
(* simproc_setup index_flip_var ("index_flip_var v") = Prog_Variables.index_flip_var_simproc *)

(* Simproc that rewrites a `qregister_conversion F G` into an index-register.
   (Index-registers are registers build from chain, pair, Fst, Snd.) *)
simproc_setup qregister_conversion_to_register (\<open>qregister_conversion x y\<close>) =
  \<open>fn m => fn ctxt => fn ct => SOME (Prog_Variables.qregister_conversion_to_register_conv ctxt ct) handle e => NONE\<close>

(* A hint to the simplifier with the meaning:
    - A is a term of the form x>>Q
    - Q,R are registers
    - Q \<le> R
    - The whole term should be rewritten into x'>>R for some x'
  Rewriting the term is done by the simproc TODO declared below.
*)
definition "register_conversion_hint R A = A" (* LEGACY *)
lemma register_conversion_hint_cong[cong]: "A=A' \<Longrightarrow> register_conversion_hint R A = register_conversion_hint R A'" by simp

(* Simproc that rewrites terms of the form `register_conversion_hint G (apply_qregister F a)` into
  `apply_qregister target (apply_qregister (qregister_conversion \<dots>) A)` for suitable \<dots> *)
simproc_setup register_conversion_hint (\<open>register_conversion_hint G (apply_qregister F a)\<close> | \<open>register_conversion_hint G (apply_qregister_space F S)\<close>) =
  \<open>fn m => fn ctxt => fn ct => let
    (* val _ = \<^print> ct *)
    val target = ct |> Thm.dest_arg1
    val conv = (Prog_Variables.apply_qregister_conversion_conv ctxt target |> Conv.arg_conv)
        then_conv Conv.rewr_conv @{thm register_conversion_hint_def[THEN eq_reflection]}
    in SOME (conv ct) handle e => NONE end\<close>

(* TODO: check if we keep this mechanism. *)
definition \<open>JOIN_REGISTERS F G FG \<equiv> True\<close>

(* TODO: check if we keep this mechanism. *)
definition \<open>REGISTER_SOLVE x \<equiv> x\<close>
lemma REGISTER_SOLVER_cong[cong]: \<open>REGISTER_SOLVE x = REGISTER_SOLVE x\<close>
  by (rule refl)

named_theorems join_registers

(* TODO: remove or move *)
(* Indicates to the simplifier that the (schematic) variable x should be instantiated as y *)
definition \<open>INSTANTIATE_VARIABLE x y = True\<close>
lemma INSTANTIATE_VARIABLE_cong[cong]: \<open>INSTANTIATE_VARIABLE x y = INSTANTIATE_VARIABLE x y\<close>
  by simp
lemma INSTANTIATE_VARIABLE_instantiate: \<open>INSTANTIATE_VARIABLE x x\<close>
  by (simp add: INSTANTIATE_VARIABLE_def)
setup \<open>
map_theory_simpset (fn ctxt => ctxt
    addSolver 
      Simplifier.mk_solver "INSTANTIATE_VARIABLE" (fn ctxt => 
        resolve_tac ctxt @{thms INSTANTIATE_VARIABLE_instantiate}))\<close>

(* 
(* TODO outdated doc comment *)

Simproc that proves a goal of the form \<open>JOIN_REGISTERS F G ?H ?L\<close> where
  F G are qregisters and H,L will be instantiated.
  (Strictly speaking, they will not be instantiated because simprocs cannot do that.
   Instead, the JOIN_REGISTERS term will be rewritten into (?H=\<dots> \<and> ?L=\<dots>).
   Strictly speaking, H,L do not need to be schematic therefore.)

  Both H, L will instantiated to \<open>(\<lambda>F. register_conversion_hint FG F)\<close> where FG is an upper bound (not proven!)
  for F,G (w.r.t., qregister_le).

  (We have two variables H,L because they may need different types.)
  (* TODO: Do they? Do we have cases where the types are different? Let's see in the end and possibly simplify. *)
*)
(* simproc_setup JOIN_REGISTERS (\<open>JOIN_REGISTERS F G H L\<close>) = \<open>fn _ => fn ctxt => fn ct => let
  val (((F,G),H),L) = ct |> Thm.dest_comb |> apfst Thm.dest_comb |> apfst (apfst Thm.dest_comb) |> apfst (apfst (apfst Thm.dest_arg))
  val F' = Thm.term_of F val G' = Thm.term_of G
  val index = Prog_Variables.is_index_qregister F' andalso Prog_Variables.is_index_qregister G'
  val FG_option = if index then NONE else Prog_Variables.join_registers ctxt F' G' |> Option.map (Thm.cterm_of ctxt)
  in case FG_option of
    NONE => NONE
    | SOME FG =>
        SOME \<^instantiate>\<open>FG and F and G and H and L and 'f=\<open>Thm.ctyp_of_cterm F\<close> and 'g=\<open>Thm.ctyp_of_cterm G\<close> and
              'h=\<open>Thm.ctyp_of_cterm H |> Thm.dest_funT |> fst\<close> and 'l=\<open>Thm.ctyp_of_cterm L |> Thm.dest_funT |> fst\<close> and
              'fg=\<open>Thm.ctyp_of_cterm FG\<close> in
              lemma \<open>JOIN_REGISTERS (F::'f) (G::'g) (H::'h\<Rightarrow>'h) (L::'l\<Rightarrow>'l) \<equiv>
              H = (\<lambda>F. register_conversion_hint (FG::'fg) F) \<and> L = (\<lambda>F. register_conversion_hint FG F)\<close>
              by (auto simp add: JOIN_REGISTERS_def register_conversion_hint_def id_def)\<close> (* |> \<^print> *)
end\<close> *)
simproc_setup JOIN_REGISTERS (\<open>JOIN_REGISTERS F G FG\<close>) = \<open>fn _ => fn ctxt => fn ct => let
  val ((F,G),FG) = ct |> Thm.dest_comb |> apfst Thm.dest_comb |> apfst (apfst Thm.dest_arg)
  val F' = Thm.term_of F val G' = Thm.term_of G
  val FG_option = Prog_Variables.join_registers ctxt F' G' |> Option.map (Thm.cterm_of ctxt)
  (* val _ = \<^print> ("JOIN_REGISTERS", Option.map Thm.typ_of_cterm FG_option, Thm.typ_of_cterm FG) *)
  in case FG_option of
    NONE => NONE
    | SOME FG' =>
        SOME \<^instantiate>\<open>FG and FG' and F and G and 'f=\<open>Thm.ctyp_of_cterm F\<close> and 'g=\<open>Thm.ctyp_of_cterm G\<close> and
              'fg=\<open>Thm.ctyp_of_cterm FG\<close> and 'fg'=\<open>Thm.ctyp_of_cterm FG'\<close> in
              lemma \<open>JOIN_REGISTERS (F::'f) (G::'g) (FG::'fg) \<equiv> INSTANTIATE_VARIABLE FG (FG'::'fg')\<close>
              by (auto simp add: JOIN_REGISTERS_def INSTANTIATE_VARIABLE_def)\<close> (* |> \<^print> *)
end\<close>

(* TODO move to .ML *)
ML \<open>
(* ct is of the form REGISTER_SOLVE (X :: bool) *)
fun register_solve_simproc_of_tac ctxt tac ct = let
    val goal = ct |> Thm.dest_arg |> Thm.apply \<^cterm>\<open>Trueprop\<close>
(* val _ = goal |> Thm.term_of |> \<^print> *)
    val thm = SOME (Goal.prove_internal ctxt [] goal (fn _ => tac))
           (* handle _ => NONE *)
(* val _ = \<^print> thm *)
    val lemma = @{lemma \<open>X \<Longrightarrow> REGISTER_SOLVE X \<equiv> True\<close> by (simp add: REGISTER_SOLVE_def)}
    val eq = Option.map (fn thm => lemma OF [thm]) thm
(* val _ = \<^print> eq *)
  in eq end

(* TODO: support cregisters as well *)
fun register_solve_le_simproc (_:morphism) ctxt ct =
  case Thm.term_of ct of
    \<^Const_>\<open>REGISTER_SOLVE _\<close> $ (\<^Const_>\<open>qregister_le _ _ _\<close> $ _ $ _) =>
      register_solve_simproc_of_tac ctxt (Prog_Variables.qregister_le_tac ctxt 1) ct
\<close>

(* TODO: support cregisters as well *)
simproc_setup register_solve_le (\<open>REGISTER_SOLVE (qregister_le Q R)\<close>) = register_solve_le_simproc

(* lemma register_conversion_hint_solve[simp]: 
  \<open>register_conversion_hint R (apply_qregister Q x) = apply_qregister R (apply_qregister (qregister_conversion Q R) x)\<close>
  if \<open>REGISTER_SOLVE (qregister_le Q R)\<close>
   *)

definition \<open>NOT_INDEX_REGISTER x = True\<close>
lemma NOT_INDEX_REGISTER_cong[cong]: \<open>NOT_INDEX_REGISTER x = NOT_INDEX_REGISTER x\<close>
  by simp

simproc_setup NOT_INDEX_REGISTER (\<open>NOT_INDEX_REGISTER R\<close>) = \<open>fn _ => fn ctxt => fn ct => let
  val R = Thm.dest_arg ct
  in
      if Prog_Variables.is_index_qregister (Thm.term_of R) |> \<^print>
      then NONE
      else SOME \<^instantiate>\<open>R and 'r=\<open>Thm.ctyp_of_cterm R\<close> in lemma \<open>NOT_INDEX_REGISTER (R::'r) \<equiv> True\<close> by (simp add: NOT_INDEX_REGISTER_def)\<close> |> \<^print>
  end
\<close>

section \<open>Cleanup\<close>

end
