theory Kraus_Maps
  imports Tensor_Product.Trace_Class Registers2.Missing_Bounded_Operators Wlog.Wlog "HOL-Library.Rewrite"
    Temporary_Compact_Op
begin

unbundle cblinfun_notation

type_synonym ('a,'b,'x) kraus_family = \<open>(('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<times> 'x) set\<close>


definition \<open>kraus_family \<EE> \<longleftrightarrow> bdd_above ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
  for \<EE> :: \<open>(_::chilbert_space, _::chilbert_space, _) kraus_family\<close>
definition \<open>kraus_family_bound \<EE> = (if kraus_family \<EE> then infsum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE> else 0)\<close>
  for \<EE> :: \<open>(_::chilbert_space, _::chilbert_space, _) kraus_family\<close>
definition \<open>kraus_family_norm \<EE> = norm (kraus_family_bound \<EE>)\<close>
(* definition \<open>kraus_family_norm \<EE> = (if kraus_family \<EE> \<and> \<EE> \<noteq> {} then
          SUP F\<in>{M. M \<subseteq> \<EE> \<and> finite M}. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) else 0)\<close>
  for \<EE> :: \<open>(_::chilbert_space, _::chilbert_space, _) kraus_family\<close> *)

lemma kraus_familyI:
  assumes \<open>bdd_above ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
  shows \<open>kraus_family \<EE>\<close>
  by (meson assms kraus_family_def)


lemma kraus_family_norm_bdd: \<open>bdd_above ((\<lambda>F. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)) ` {F. F \<subseteq> \<EE> \<and> finite F})\<close> if \<open>kraus_family \<EE>\<close>
proof -
  from that obtain B where B_bound: \<open>(\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>F \<subseteq> \<EE>\<close> and \<open>finite F\<close> for F
    by (metis (mono_tags, lifting) bdd_above.unfold imageI kraus_family_def mem_Collect_eq)
  have \<open>norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> norm B\<close> if \<open>F \<subseteq> \<EE>\<close> and \<open>finite F\<close> for F
    by (metis (no_types, lifting) B_bound norm_cblinfun_mono positive_cblinfun_squareI split_def sum_nonneg that(1) that(2))
  then show \<open>bdd_above ((\<lambda>F. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)) ` {F. F \<subseteq> \<EE> \<and> finite F})\<close>
  by (metis (mono_tags, lifting) bdd_aboveI2 mem_Collect_eq)
qed

lemma kraus_family_norm_geq0:
  shows \<open>kraus_family_norm \<EE> \<ge> 0\<close>
proof (cases \<open>kraus_family \<EE> \<and> \<EE> \<noteq> {}\<close>)
  case True
  then obtain E where \<open>E \<in> \<EE>\<close> by auto
  have \<open>0 \<le> (\<Squnion>F\<in>{F. F \<subseteq> \<EE> \<and> finite F}. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E))\<close>
    apply (rule cSUP_upper2[where x=\<open>{E}\<close>])
    using True by (simp_all add: \<open>E \<in> \<EE>\<close> kraus_family_norm_bdd)
  then show ?thesis
    by (simp add: kraus_family_norm_def True)
next
  case False
  then show ?thesis
    by (auto simp: kraus_family_norm_def)
qed

  
(* instance conditionally_complete_lattice \<subseteq> Sup_order
proof standard
  show \<open>is_Sup X (Sup X)\<close> if \<open>has_Sup X\<close> for X :: \<open>'a set\<close>
    apply (auto intro!: is_SupI cSup_upper that has_Sup_bdd_above cSup_least simp: )
  proof -
    from that have \<open>bdd_above X\<close>
      try0
      sledgehammer
      using local.has_Sup_def local.is_Sup_def by auto
 *)



lemma kraus_family_bound_has_sum:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>has_sum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE> (kraus_family_bound \<EE>)\<close>
proof -
  from assms
  obtain B where B: \<open>finite F \<Longrightarrow> F \<subseteq> \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> for F
    by (auto intro!: simp: kraus_family_def case_prod_unfold bdd_above_def)
  have \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) \<EE>\<close>
    apply (auto intro!: summable_wot_boundedI positive_cblinfun_squareI simp: kraus_family_def)
    using B by blast
  then show ?thesis
    by (auto intro!: has_sum_in_infsum_in simp: kraus_family_bound_def assms)
qed

lemma kraus_family_Sup:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>is_Sup ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> \<EE>}) (kraus_family_bound \<EE>)\<close>
proof -
  from assms
  obtain B where \<open>finite F \<Longrightarrow> F \<subseteq> \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> for F
    by (metis (mono_tags, lifting) bdd_above.unfold imageI kraus_family_def mem_Collect_eq)
  then have \<open>is_Sup ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> \<EE>})
     (infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) \<EE>)\<close>
    apply (rule infsum_wot_is_Sup[OF summable_wot_boundedI[where B=B]])
    by (auto intro!: summable_wot_boundedI positive_cblinfun_squareI simp: case_prod_beta)
  then show ?thesis
    by (auto intro!: simp: kraus_family_bound_def assms)
qed

(* lemma kraus_family_norm_def2:
  fixes \<EE> :: \<open>('a::{chilbert_space, not_singleton}, 'b::chilbert_space, 'x) kraus_family\<close>
  shows \<open>kraus_family_norm \<EE> = (if kraus_family \<EE> \<and> \<EE> \<noteq> {} then
          norm (SUP M\<in>{M. M \<subseteq> \<EE> \<and> finite M}. \<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) else 0)\<close>
proof (cases \<open>kraus_family \<EE> \<and> \<EE> \<noteq> {}\<close>)
  case True
  show ?thesis
  proof (simp only: True not_False_eq_True conj.left_neutral if_True, rule antisym)
    show \<open>kraus_family_norm \<EE> \<le> norm (\<Squnion> (sum (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) ` {M. M \<subseteq> \<EE> \<and> finite M}))\<close>
      by x
    show \<open>norm (\<Squnion> (sum (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) ` {M. M \<subseteq> \<EE> \<and> finite M})) \<le> kraus_family_norm \<EE> \<close>
      
  qed
next
  case False
  then show ?thesis
    by (auto simp: kraus_family_norm_def)
qed *)

(* lemma kraus_family_norm_def3: 
(* TODO get rid of "not_singleton" *)
  fixes \<EE> :: \<open>('a::{chilbert_space, not_singleton}, 'b::chilbert_space, 'x) kraus_family\<close>
  shows \<open>kraus_family_norm \<EE> = (if kraus_family \<EE> then
  Inf {r. r \<ge> 0 \<and> (\<forall>M\<subseteq>\<EE>. finite M \<longrightarrow> (\<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R id_cblinfun)} else 0)\<close>
proof (cases \<open>kraus_family \<EE> \<and> \<EE> \<noteq> {}\<close>)
  case True
  then have \<open>kraus_family \<EE>\<close> and \<open>\<EE> \<noteq> {}\<close>
    by auto
  show ?thesis
  proof (rule antisym)
    have \<open>kraus_family_norm \<EE> \<le> Inf {r. r \<ge> 0 \<and> (\<forall>M\<subseteq>\<EE>. finite M \<longrightarrow> (\<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R id_cblinfun)}\<close>
    proof (rule cInf_greatest)
      from \<open>kraus_family \<EE>\<close>
      obtain A where \<open>(\<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> A\<close> if \<open>M \<subseteq> \<EE>\<close> and \<open>finite M\<close> for M
        by (metis (mono_tags, lifting) bdd_above_def imageI kraus_family_def mem_Collect_eq)
      moreover have \<open>A \<le> norm A *\<^sub>R id_cblinfun\<close>
        by (smt (verit, best) calculation empty_subsetI finite.intros(1) less_eq_scaled_id_norm positive_hermitianI scaleR_scaleC sum.empty)
      ultimately show \<open>{r. r \<ge> 0 \<and> (\<forall>M\<subseteq>\<EE>. finite M \<longrightarrow> (\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R id_cblinfun)} \<noteq> {}\<close>
        apply (auto intro!: simp: )
        by (meson dual_order.trans norm_ge_zero)
    next
      fix r
      have pos: \<open>(\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) \<ge> 0\<close> for M
        by (simp add: positive_cblinfun_squareI split_def sum_nonneg)
      assume r: \<open>r \<in> {r. r \<ge> 0 \<and> (\<forall>M\<subseteq>\<EE>. finite M \<longrightarrow> (\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R id_cblinfun)}\<close>
      then have *: \<open>(\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R id_cblinfun\<close> if \<open>M \<subseteq> \<EE>\<close> and \<open>finite M\<close> for M
        using that by simp
      from r have \<open>r \<ge> 0\<close>
        by simp
      have \<open>norm (\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r\<close> if \<open>M \<subseteq> \<EE>\<close> and \<open>finite M\<close> for M
        using norm_cblinfun_mono[OF pos *[OF that]] \<open>r \<ge> 0\<close>
        by simp
      then have \<open>(\<Squnion>M\<in>{M. M \<subseteq> \<EE> \<and> finite M}. norm (\<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E)) \<le> r\<close>
        apply (rule_tac cSup_least)
        by auto
      then show \<open>kraus_family_norm \<EE> \<le> r\<close>
        using True by (auto intro!: simp: kraus_family_norm_def)
    qed
    then show \<open>kraus_family_norm \<EE> \<le> (if kraus_family \<EE> then \<Sqinter> {r. r \<ge> 0 \<and> (\<forall>M\<subseteq>\<EE>. finite M \<longrightarrow> (\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R id_cblinfun)} else 0)\<close>
      using True by simp
  next
    have \<open>Inf {r. r \<ge> 0 \<and> (\<forall>M\<subseteq>\<EE>. finite M \<longrightarrow> (\<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R id_cblinfun)} \<le> kraus_family_norm \<EE>\<close>
    proof (rule cInf_lower)
      show \<open>bdd_below {r. 0 \<le> r \<and> (\<forall>M\<subseteq>\<EE>. finite M \<longrightarrow> (\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R id_cblinfun)}\<close>
        by auto
      (* have \<open>(\<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> kraus_family_norm \<EE> *\<^sub>R id_cblinfun\<close> *)
      show \<open>kraus_family_norm \<EE> \<in> {r. 0 \<le> r \<and> (\<forall>M\<subseteq>\<EE>. finite M \<longrightarrow> (\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R id_cblinfun)}\<close>
        apply (auto intro!: kraus_family_norm_geq0 simp: )
by -

        by x
    qed
    then show \<open>(if kraus_family \<EE> then \<Sqinter> {r. r \<ge> 0 \<and> (\<forall>M\<subseteq>\<EE>. finite M \<longrightarrow> (\<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R id_cblinfun)} else 0) \<le> kraus_family_norm \<EE>\<close>
      using True by simp
  qed
next
  case False
  then show ?thesis
    by (auto intro!: cInf_eq_minimum[where z=0] simp: kraus_family_norm_def)
qed *)


definition kraus_family_related_ops :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> ('a,'b,'x) kraus_family\<close> where
  \<open>kraus_family_related_ops \<EE> E = {(F,x)\<in>\<EE>. (\<exists>r>0. E = r *\<^sub>R F)}\<close>

definition kraus_family_op_weight where
  \<open>kraus_family_op_weight \<EE> E = (\<Sum>\<^sub>\<infinity>(F,_)\<in>kraus_family_related_ops \<EE> E. norm (F* o\<^sub>C\<^sub>L F))\<close>

lemma kraus_family_op_weight_geq0[simp]: \<open>kraus_family_op_weight \<EE> E \<ge> 0\<close>
  by (auto intro!: infsum_nonneg simp: kraus_family_op_weight_def)

lemma kraus_family_related_ops_abs_summable:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>(\<lambda>(F,_). F* o\<^sub>C\<^sub>L F) abs_summable_on (kraus_family_related_ops \<EE> E)\<close>
proof (cases \<open>E = 0\<close>)
  case True
  show ?thesis
    apply (rule summable_on_cong[where g=\<open>\<lambda>_. 0\<close>, THEN iffD2])
    by (auto simp: kraus_family_related_ops_def True)
next
  case False
  then obtain \<psi> where E\<psi>: \<open>E \<psi> \<noteq> 0\<close>
    by (metis cblinfun.zero_left cblinfun_eqI)
  define \<phi> where \<open>\<phi> = ((norm E)\<^sup>2 / (\<psi> \<bullet>\<^sub>C (E* *\<^sub>V E *\<^sub>V \<psi>))) *\<^sub>C \<psi>\<close>
  have normFF: \<open>norm (fst Fx* o\<^sub>C\<^sub>L fst Fx) = \<psi> \<bullet>\<^sub>C (fst Fx* *\<^sub>V fst Fx *\<^sub>V \<phi>)\<close>
    if \<open>Fx \<in> kraus_family_related_ops \<EE> E\<close> for Fx
  proof -
    define F where \<open>F = fst Fx\<close>
    from that obtain r where FE: \<open>F = r *\<^sub>R E\<close>
      apply atomize_elim
      apply (auto intro!: simp: kraus_family_related_ops_def F_def)
      by (metis Extra_Ordered_Fields.sign_simps(5) rel_simps(70) right_inverse scaleR_one)
    show \<open>norm (F* o\<^sub>C\<^sub>L F) = \<psi> \<bullet>\<^sub>C (F* *\<^sub>V F *\<^sub>V \<phi>)\<close>
      by (simp add: False \<phi>_def FE cblinfun.scaleR_left cblinfun.scaleR_right
          cblinfun.scaleC_left cblinfun.scaleC_right cinner_adj_right E\<psi>)
  qed

  have \<psi>\<phi>_mono: \<open>mono (\<lambda>A. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>))\<close>
  proof (rule monoI)
    fix A B :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    assume \<open>A \<le> B\<close>
    then have \<open>B - A \<ge> 0\<close>
      by auto
    then have \<open>\<psi> \<bullet>\<^sub>C ((B - A) *\<^sub>V \<psi>) \<ge> 0\<close>
      by (simp add: cinner_pos_if_pos)
    then have \<open>\<psi> \<bullet>\<^sub>C ((B - A) *\<^sub>V \<phi>) \<ge> 0\<close>
      by (auto intro!: mult_nonneg_nonneg square_nneg_complex
          simp: \<phi>_def cblinfun.scaleC_right divide_inverse cinner_adj_right)
    then show \<open>\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>) \<le> \<psi> \<bullet>\<^sub>C (B *\<^sub>V \<phi>)\<close>
      by (simp add: cblinfun.diff_left cinner_diff_right)
  qed

  have \<psi>\<phi>_linear: \<open>clinear (\<lambda>A. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>))\<close>
    by (auto intro!: clinearI simp: cblinfun.add_left cinner_add_right)

  from assms
  have \<open>bdd_above ((\<lambda>M. \<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) ` {M. finite M \<and> M \<subseteq> \<EE>})\<close>
    by (simp add: kraus_family_def)
  then have \<open>bdd_above ((\<lambda>M. \<Sum>(F, x)\<in>M. F* o\<^sub>C\<^sub>L F) ` {M. M \<subseteq> kraus_family_related_ops \<EE> E \<and> finite M})\<close>
    apply (rule bdd_above_mono2[OF _ _ order.refl])
    by (auto simp: kraus_family_related_ops_def)
  then have \<open>bdd_above ((\<lambda>A. \<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>)) ` (\<lambda>M. \<Sum>(F, x)\<in>M. F* o\<^sub>C\<^sub>L F) ` {M. M \<subseteq> kraus_family_related_ops \<EE> E \<and> finite M})\<close>
    by (rule bdd_above_image_mono[OF \<psi>\<phi>_mono])
  then have \<open>bdd_above ((\<lambda>M. \<psi> \<bullet>\<^sub>C ((\<Sum>(F, x)\<in>M. F* o\<^sub>C\<^sub>L F) *\<^sub>V \<phi>)) ` {M. M \<subseteq> kraus_family_related_ops \<EE> E \<and> finite M})\<close>
    by (simp add: image_image)
  then have \<open>bdd_above ((\<lambda>M. \<Sum>(F, x)\<in>M. \<psi> \<bullet>\<^sub>C ((F* o\<^sub>C\<^sub>L F) *\<^sub>V \<phi>)) ` {M. M \<subseteq> kraus_family_related_ops \<EE> E \<and> finite M})\<close>
    unfolding case_prod_beta
    by (subst complex_vector.linear_sum[OF \<psi>\<phi>_linear, symmetric])
  then have \<open>bdd_above ((\<lambda>M. \<Sum>(F, x)\<in>M. complex_of_real (norm (F* o\<^sub>C\<^sub>L F))) ` {M. M \<subseteq> kraus_family_related_ops \<EE> E \<and> finite M})\<close>
    apply (rule bdd_above_mono2[OF _ subset_refl])
    unfolding case_prod_unfold
    apply (subst sum.cong[OF refl normFF])
    by auto
  then have \<open>bdd_above ((\<lambda>M. \<Sum>(F, x)\<in>M. norm (F* o\<^sub>C\<^sub>L F)) ` {M. M \<subseteq> kraus_family_related_ops \<EE> E \<and> finite M})\<close>
    by (auto simp add: bdd_above_def case_prod_unfold less_eq_complex_def)
  then have \<open>(\<lambda>(F,_). norm (F* o\<^sub>C\<^sub>L F)) summable_on (kraus_family_related_ops \<EE> E)\<close>
    apply (rule nonneg_bdd_above_summable_on[rotated])
    by auto
  then show \<open>(\<lambda>(F,_). F* o\<^sub>C\<^sub>L F) abs_summable_on kraus_family_related_ops \<EE> E\<close>
    by (simp add: case_prod_unfold)
(*
  from assms
  have \<open>(\<lambda>(F,_::'x). F* o\<^sub>C\<^sub>L F) summable_on \<EE>\<close>
    using kraus_family_def by blast
  then have \<open>(\<lambda>(F,_::'x). F* o\<^sub>C\<^sub>L F) summable_on (kraus_family_related_ops \<EE> E)\<close>
    apply (rule summable_on_subset_banach)
    by (auto simp: kraus_family_related_ops_def)
  then have \<open>(\<lambda>(F,_::'x). \<psi> \<bullet>\<^sub>C ((F* o\<^sub>C\<^sub>L F) *\<^sub>V \<phi>)) summable_on (kraus_family_related_ops \<EE> E)\<close>
    unfolding case_prod_beta
    apply (rule Infinite_Sum.summable_on_bounded_linear[rotated])
    by (intro bounded_clinear.bounded_linear bounded_clinear_cinner_right_comp bounded_clinear_apply_cblinfun)
  then have \<open>(\<lambda>(F,_::'x). complex_of_real (norm (F* o\<^sub>C\<^sub>L F))) summable_on (kraus_family_related_ops \<EE> E)\<close>
    apply (rule summable_on_cong[THEN iffD2, rotated])
    by (simp add: case_prod_unfold flip: normFF)
  then have \<open>(\<lambda>(F,_::'x). norm (F* o\<^sub>C\<^sub>L F)) summable_on (kraus_family_related_ops \<EE> E)\<close>
    by (metis (mono_tags, lifting) Re_complex_of_real complex_of_real_cmod complex_of_real_mono norm_ge_zero of_real_0 split_def summable_on_cong summable_on_iff_abs_summable_on_complex)
  then show \<open>(\<lambda>x. case x of (F, _) \<Rightarrow> F* o\<^sub>C\<^sub>L F) abs_summable_on kraus_family_related_ops \<EE> E\<close>
    by (simp add: case_prod_unfold)
*)
qed

lemma kraus_family_op_weight_neq0: \<open>kraus_family_op_weight \<EE> E \<noteq> 0\<close> 
  if \<open>kraus_family \<EE>\<close> and \<open>(E,x) \<in> \<EE>\<close> and \<open>E \<noteq> 0\<close>
proof -
  have 1: \<open>(E, x) \<in> kraus_family_related_ops \<EE> E\<close>
    by (auto intro!: exI[where x=1] simp: kraus_family_related_ops_def that)

  have \<open>kraus_family_op_weight \<EE> E = (\<Sum>\<^sub>\<infinity>(F, x)\<in>kraus_family_related_ops \<EE> E. (norm F)\<^sup>2)\<close>
    by (simp add: kraus_family_op_weight_def)
  moreover have \<open>\<dots> \<ge> (\<Sum>\<^sub>\<infinity>(F, x)\<in>{(E,x)}. (norm F)\<^sup>2)\<close> (is \<open>_ \<ge> \<dots>\<close>)
    apply (rule infsum_mono_neutral)
    using kraus_family_related_ops_abs_summable[OF that(1)]
    by (auto intro!: 1 simp: that case_prod_unfold)
  moreover have \<open>\<dots> > 0\<close>
    using that by simp
  ultimately show ?thesis
    by auto
qed

definition kraus_family_flatten :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a, 'b, unit) kraus_family\<close> where
  \<open>kraus_family_flatten \<EE> = {(E,x). norm (E* o\<^sub>C\<^sub>L E) = kraus_family_op_weight \<EE> E \<and> E \<noteq> 0}\<close>

lemma kraus_family_bound_pos[simp]: \<open>kraus_family_bound \<EE> \<ge> 0\<close>
  apply (cases \<open>kraus_family \<EE>\<close>)
  apply (metis (no_types, lifting) empty_subsetI finite.emptyI image_iff is_Sup_def kraus_family_Sup mem_Collect_eq sum.empty)
  by (simp add: kraus_family_bound_def)

lemma kraus_family_sums_bounded_by_bound:
  assumes \<open>kraus_family \<EE>\<close>
  assumes \<open>M \<subseteq> \<EE>\<close>
  shows \<open>(\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> kraus_family_bound \<EE>\<close>
proof (cases \<open>finite M\<close>)
  case True
  then show ?thesis
  using kraus_family_Sup[OF assms(1)]
  apply (simp add: is_Sup_def case_prod_beta)
  using assms(2) by blast
next
  case False
  then show ?thesis
    by simp
qed

lemma kraus_family_sums_bounded_by_norm:
  assumes \<open>kraus_family \<EE>\<close>
  assumes \<open>M \<subseteq> \<EE>\<close>
  shows \<open>norm (\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> kraus_family_norm \<EE>\<close>
  using kraus_family_sums_bounded_by_bound assms
  by (auto intro!: norm_cblinfun_mono sum_nonneg 
      intro: positive_cblinfun_squareI
      simp add: kraus_family_norm_def case_prod_beta)
(* proof (cases \<open>finite (M\<inter>\<EE>)\<close>)
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
qed *)


definition \<open>kraus_family_map \<EE> \<rho> = (\<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>)\<close>

lemma kraus_family_map_0[simp]: \<open>kraus_family_map {} = 0\<close>
  by (auto simp: kraus_family_map_def)

definition \<open>kraus_equivalent \<EE> \<FF> \<longleftrightarrow> kraus_family \<EE> \<and> kraus_family \<FF> \<and> kraus_family_map \<EE> = kraus_family_map \<FF>\<close>

lemma kraus_equivalent_reflI: \<open>kraus_equivalent x x\<close> if \<open>kraus_family x\<close>
  using that by (simp add: kraus_equivalent_def)

lemma kraus_family_zero[simp]: \<open>kraus_family {}\<close>
  by (auto simp: kraus_family_def)

quotient_type (overloaded) ('a,'b) kraus_map = \<open>('a::chilbert_space, 'b::chilbert_space, unit) kraus_family\<close> / partial: kraus_equivalent
  by (auto intro!: part_equivpI exI[of _ \<open>{}\<close>] sympI transpI simp: kraus_equivalent_def)

definition \<open>kraus_family_comp_dependent \<EE> \<FF> = (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (E,F,x,y))) ` (SIGMA (F,y):\<FF>. \<EE> y)\<close> 
  for \<FF> :: \<open>(_::chilbert_space, _::chilbert_space, _) kraus_family\<close>

definition \<open>kraus_family_comp \<EE> \<FF> = kraus_family_comp_dependent (\<lambda>_. \<EE>) \<FF>\<close>

(* definition \<open>kraus_family_comp \<EE> \<FF> = (\<lambda>((E,x), (F,y)). (E o\<^sub>C\<^sub>L F, (E,F,x,y))) ` (\<EE>\<times>\<FF>)\<close> 
  for \<EE> \<FF> :: \<open>(_::chilbert_space, _::chilbert_space, _) kraus_family\<close> *)

definition kraus_family_of_op :: \<open>_ \<Rightarrow> (_::chilbert_space, _::chilbert_space, unit) kraus_family\<close> where
  \<open>kraus_family_of_op E = {(E, ())}\<close>

lemma kraus_family_finite: \<open>kraus_family \<EE>\<close> if \<open>finite \<EE>\<close>
proof -
  define B where \<open>B = (\<Sum>(E,x)\<in>\<EE>. E* o\<^sub>C\<^sub>L E)\<close>
  have \<open>(\<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>finite M\<close> and \<open>M \<subseteq> \<EE>\<close> for M
    unfolding B_def
    using \<open>finite \<EE>\<close> \<open>M \<subseteq> \<EE>\<close> apply (rule sum_mono2)
    by (auto intro!: positive_cblinfun_squareI)
  then show ?thesis
    by (auto intro!: bdd_aboveI[of _ B] simp: kraus_family_def)
qed

lemma kraus_family_bound_finite: \<open>kraus_family_bound \<EE> = (\<Sum>(E,x)\<in>\<EE>. E* o\<^sub>C\<^sub>L E)\<close> if \<open>finite \<EE>\<close>
  by (auto intro!: kraus_family_finite simp: kraus_family_bound_def that infsum_in_finite)

lemma kraus_family_norm_finite: \<open>kraus_family_norm \<EE> = norm (\<Sum>(E,x)\<in>\<EE>. E* o\<^sub>C\<^sub>L E)\<close> if \<open>finite \<EE>\<close>
  by (simp add: kraus_family_norm_def kraus_family_bound_finite that)
(* proof -
  define B where \<open>B = (\<Sum>(E,x)\<in>\<EE>. E* o\<^sub>C\<^sub>L E)\<close>
  have bound_B: \<open>(\<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>finite M\<close> and \<open>M \<subseteq> \<EE>\<close> for M
    unfolding B_def
    using \<open>finite \<EE>\<close> \<open>M \<subseteq> \<EE>\<close> apply (rule sum_mono2)
    by (auto intro!: positive_cblinfun_squareI)
  have \<open>(\<Squnion>x\<in>{F. F \<subseteq> \<EE> \<and> finite F}. norm (\<Sum>(E, x)\<in>x. E* o\<^sub>C\<^sub>L E)) = norm (\<Sum>(E, x)\<in>\<EE>. E* o\<^sub>C\<^sub>L E)\<close>
    apply (rule cSup_eq_maximum)
     apply (auto intro!: image_eqI[where x=\<EE>] simp: case_prod_unfold \<open>finite \<EE>\<close>)
    by (meson norm_cblinfun_mono positive_cblinfun_squareI sum_mono2 sum_nonneg that)
  then show ?thesis
    by (simp add: kraus_family_finite kraus_family_norm_def \<open>finite \<EE>\<close>)
qed *)

lemma kraus_family_kraus_family_of_op[simp]: \<open>kraus_family (kraus_family_of_op E)\<close>
  by (auto intro!: kraus_family_finite simp: kraus_family_of_op_def)

lemma kraus_family_of_op_norm[simp]: \<open>kraus_family_norm (kraus_family_of_op E) = (norm E)\<^sup>2\<close>
  by (simp add: kraus_family_of_op_def kraus_family_norm_finite)
(* proof -
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
qed *)

lift_definition kraus_map_of_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> ('a,'b) kraus_map\<close>
  is kraus_family_of_op
  by (simp add: kraus_equivalent_def)

lemma sandwich_tc_scaleC_right: \<open>sandwich_tc e (c *\<^sub>C t) = c *\<^sub>C sandwich_tc e t\<close>
  apply (transfer fixing: e c)
  by (simp add: cblinfun.scaleC_right)

lemma kraus_family_map_scaleC:
  shows \<open>kraus_family_map \<EE> (c *\<^sub>C x) = c *\<^sub>C kraus_family_map \<EE> x\<close>
  by (simp add: kraus_family_map_def cblinfun.scaleC_right case_prod_unfold sandwich_tc_scaleC_right
      flip: infsum_scaleC_right)

lemma sandwich_tc_plus: \<open>sandwich_tc e (t + u) = sandwich_tc e t + sandwich_tc e u\<close>
  by (simp add: sandwich_tc_def compose_tcr.add_right compose_tcl.add_left)

lemma sandwich_tc_minus: \<open>sandwich_tc e (t - u) = sandwich_tc e t - sandwich_tc e u\<close>
  by (simp add: sandwich_tc_def compose_tcr.diff_right compose_tcl.diff_left)

lemma bounded_clinear_sandwich_tc[bounded_clinear]: \<open>bounded_clinear (sandwich_tc e)\<close>
  using norm_sandwich_tc[of e]
  by (auto intro!: bounded_clinearI[where K=\<open>(norm e)\<^sup>2\<close>]
      simp: sandwich_tc_plus sandwich_tc_scaleC_right cross3_simps)

lemma kraus_family_map_abs_summable:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>(\<lambda>(E,x). sandwich_tc E \<rho>) abs_summable_on \<EE>\<close>
proof -
  wlog \<rho>_pos: \<open>\<rho> \<ge> 0\<close> generalizing \<rho>
  proof -
    obtain \<rho>1 \<rho>2 \<rho>3 \<rho>4 where \<rho>_decomp: \<open>\<rho> = \<rho>1 - \<rho>2 + \<i> *\<^sub>C \<rho>3 - \<i> *\<^sub>C \<rho>4\<close>
      and pos: \<open>\<rho>1 \<ge> 0\<close> \<open>\<rho>2 \<ge> 0\<close> \<open>\<rho>3 \<ge> 0\<close> \<open>\<rho>4 \<ge> 0\<close>
      apply atomize_elim using trace_class_decomp_4pos'[of \<rho>] by blast
    have \<open>norm (sandwich_tc x \<rho>) 
      \<le> norm (sandwich_tc x \<rho>1)
      + norm (sandwich_tc x \<rho>2)
      + norm (sandwich_tc x \<rho>3)
      + norm (sandwich_tc x \<rho>4)\<close> 
      (is \<open>_ \<le> ?S x\<close>) for x
      by (auto simp add: \<rho>_decomp sandwich_tc_plus sandwich_tc_minus  sandwich_tc_scaleC_right
          scaleC_add_right scaleC_diff_right norm_mult
          intro!: norm_triangle_le norm_triangle_le_diff)
    then have *: \<open>norm (sandwich_tc (fst x) \<rho>) \<le> norm (?S (fst x))\<close> for x
      by force
    show ?thesis
      unfolding case_prod_unfold
      apply (rule abs_summable_on_comparison_test[OF _ *])
      apply (intro abs_summable_on_add abs_summable_norm abs_summable_on_scaleC_right  pos)
      using hypothesis
      by (simp_all add: case_prod_unfold pos)
  qed

  have aux: \<open>trace_norm x = Re (trace x)\<close> if \<open>x \<ge> 0\<close> and \<open>trace_class x\<close> for x
    by (metis Re_complex_of_real that(1) trace_norm_pos)
  have trace_EE\<rho>_pos: \<open>trace ((E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>) \<ge> 0\<close> for E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    apply (simp add: cblinfun_assoc_right trace_class_comp_right
        flip: circularity_of_trace)
    by (auto intro!: trace_pos sandwich_pos 
        simp: cblinfun_assoc_left from_trace_class_pos \<rho>_pos 
        simp flip: sandwich_apply)
  have trace_EE\<rho>_lin: \<open>linear (\<lambda>M. Re (trace (M o\<^sub>C\<^sub>L from_trace_class \<rho>)))\<close> for M
    apply (rule linear_compose[where g=Re, unfolded o_def])
    by (auto intro!: bounded_linear.linear bounded_clinear.bounded_linear
        bounded_clinear_trace_duality' bounded_linear_Re)
  have trace_EE\<rho>_mono: \<open>mono_on (Collect ((\<le>) 0)) (\<lambda>A. Re (trace (A o\<^sub>C\<^sub>L from_trace_class \<rho>)))\<close> for M
    apply (auto intro!: mono_onI Re_mono)
    apply (subst diff_ge_0_iff_ge[symmetric])
    apply (subst trace_minus[symmetric])
    by (auto intro!: trace_class_comp_right trace_comp_pos
        simp: from_trace_class_pos \<rho>_pos
        simp flip: cblinfun_compose_minus_left)

  from assms
  have \<open>bdd_above ((\<lambda>F. (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
    by (simp add: kraus_family_def)
  then have \<open>bdd_above ((\<lambda>F. Re (trace ((\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
    apply (rule bdd_above_transform_mono_pos)
    by (auto intro!: sum_nonneg positive_cblinfun_squareI[OF refl] trace_EE\<rho>_mono
        simp: case_prod_unfold)
  then have \<open>bdd_above ((\<lambda>F. \<Sum>(E,x)\<in>F. Re (trace ((E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))) ` {F. F \<subseteq> \<EE> \<and> finite F})\<close>
    apply (subst (asm) real_vector.linear_sum[where f=\<open>\<lambda>M. Re (trace (M o\<^sub>C\<^sub>L from_trace_class \<rho>))\<close>])
    by (auto intro!: trace_EE\<rho>_lin simp: case_prod_unfold conj_commute)
  then have \<open>(\<lambda>(E,_). Re (trace ((E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))) summable_on \<EE>\<close>
    apply (rule nonneg_bdd_above_summable_on[rotated])
    using trace_EE\<rho>_pos 
    by (auto simp: less_eq_complex_def)
 then have \<open>(\<lambda>(E,_). Re (trace (from_trace_class (sandwich_tc E \<rho>)))) summable_on \<EE>\<close>
    by (simp add: from_trace_class_sandwich_tc sandwich_apply cblinfun_assoc_right trace_class_comp_right
        flip: circularity_of_trace)
  then have \<open>(\<lambda>(E,_). trace_norm (from_trace_class (sandwich_tc E \<rho>))) summable_on \<EE>\<close>
    by (simp add: aux from_trace_class_pos \<rho>_pos  sandwich_tc_pos)
  then show \<open>(\<lambda>(E,x). sandwich_tc E \<rho>) abs_summable_on \<EE>\<close>
    by (simp add: norm_trace_class.rep_eq case_prod_unfold)
qed

lemma kraus_family_map_summable:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>(\<lambda>(E,x). sandwich_tc E \<rho>) summable_on \<EE>\<close>
  apply (rule abs_summable_summable)
  using assms by (rule kraus_family_map_abs_summable)

lemma kraus_family_map_has_sum:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum kraus_family_map \<EE> \<rho>) \<EE>\<close>
  using kraus_family_map_summable assms
  by (auto intro!: has_sum_infsum simp add: kraus_family_map_def kraus_family_map_summable case_prod_unfold)

lemma kraus_family_map_plus_right:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_map \<EE> (x + y) = kraus_family_map \<EE> x + kraus_family_map \<EE> y\<close>
  using kraus_family_map_summable[OF assms]
  by (auto intro!: infsum_add
      simp add: kraus_family_map_def sandwich_tc_plus scaleC_add_right case_prod_unfold)

lemma sandwich_tc_uminus_right: \<open>sandwich_tc e (- t) = - sandwich_tc e t\<close>
  by (metis (no_types, lifting) add.right_inverse arith_simps(50) diff_0 group_cancel.sub1 sandwich_tc_minus)

lemma kraus_family_map_uminus_right:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_map \<EE> (- x) = - kraus_family_map \<EE> x\<close>
  using kraus_family_map_summable[OF assms]
  by (auto intro!: infsum_uminus 
      simp add: kraus_family_map_def sandwich_tc_uminus_right scaleC_minus_right case_prod_unfold)


lemma kraus_family_map_minus_right:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_map \<EE> (x - y) = kraus_family_map \<EE> x - kraus_family_map \<EE> y\<close>
  using assms
  by (simp only: diff_conv_add_uminus kraus_family_map_plus_right kraus_family_map_uminus_right)

lemma kraus_family_map_pos:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kraus_family_map \<EE> \<rho> \<ge> 0\<close>
  by (auto intro!: infsum_nonneg_traceclass scaleC_nonneg_nonneg of_nat_0_le_iff
      sandwich_tc_pos assms simp: kraus_family_map_def)

lemma kraus_family_map_bounded_pos:
  assumes \<open>kraus_family \<EE>\<close> and \<open>\<rho> \<ge> 0\<close>
  shows \<open>norm (kraus_family_map \<EE> \<rho>) \<le> kraus_family_norm \<EE> * norm \<rho>\<close>
proof -
  have \<open>norm (kraus_family_map \<EE> \<rho>) = Re (trace_tc (\<Sum>\<^sub>\<infinity>(E,_)\<in>\<EE>. sandwich_tc E \<rho>))\<close>
    apply (subst Re_complex_of_real[symmetric])
    apply (subst norm_tc_pos)
    using \<open>\<rho> \<ge> 0\<close> apply (rule kraus_family_map_pos)
    by (simp add: kraus_family_map_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,_)\<in>\<EE>. Re (trace_tc (sandwich_tc E \<rho>)))\<close>
    using kraus_family_map_summable[OF assms(1)]
    by (simp_all flip: infsum_bounded_linear[of \<open>\<lambda>x. Re (trace_tc x)\<close>] 
        add: case_prod_unfold bounded_linear_compose[of Re trace_tc] bounded_linear_Re
        o_def bounded_clinear.bounded_linear)
  also have \<open>\<dots> \<le> kraus_family_norm \<EE> * norm \<rho>\<close>
  proof (rule infsum_le_finite_sums)
    show \<open>(\<lambda>(E,_). Re (trace_tc (sandwich_tc E \<rho>))) summable_on \<EE>\<close>
      unfolding case_prod_beta
      apply (rule summable_on_bounded_linear[unfolded o_def, where h=\<open>\<lambda>x. Re (trace_tc x)\<close>])
      using kraus_family_map_summable[OF assms(1)]
      by (simp_all flip: infsum_bounded_linear[of \<open>\<lambda>x. Re (trace_tc x)\<close>] 
        add: bounded_linear_compose[of Re trace_tc] bounded_linear_Re bounded_clinear.bounded_linear 
        o_def trace_tc_scaleC assms kraus_family_map_def case_prod_unfold)
    fix M :: \<open>(('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<times> 'c) set\<close> assume \<open>finite M\<close> and \<open>M \<subseteq> \<EE>\<close>
    have \<open>(\<Sum>(E,_)\<in>M. Re (trace_tc (sandwich_tc E \<rho>)))
        = (\<Sum>(E,_)\<in>M. Re (trace (E o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L E*)))\<close>
      by (simp add: trace_tc.rep_eq from_trace_class_sandwich_tc sandwich_apply scaleC_trace_class.rep_eq trace_scaleC)
    also have \<open>\<dots> = (\<Sum>(E,_)\<in>M. Re (trace (E* o\<^sub>C\<^sub>L E o\<^sub>C\<^sub>L from_trace_class \<rho>)))\<close>
      apply (subst circularity_of_trace)
      by (auto intro!: trace_class_comp_right simp: cblinfun_compose_assoc)
    also have \<open>\<dots> = Re (trace ((\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))\<close>
      by (simp only: trace_class_scaleC trace_class_comp_right trace_class_from_trace_class case_prod_unfold
          flip: Re_sum trace_scaleC trace_sum cblinfun.scaleC_left cblinfun_compose_scaleC_left cblinfun_compose_sum_left)
    also have \<open>\<dots> \<le> cmod (trace ((\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L from_trace_class \<rho>))\<close>
      by (rule complex_Re_le_cmod)
    also have \<open>\<dots> \<le> norm (\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) * trace_norm (from_trace_class \<rho>)\<close>
      apply (rule cmod_trace_times)
      by simp
    also have \<open>\<dots> \<le> kraus_family_norm \<EE> * norm \<rho>\<close>
      apply (simp add: flip: norm_trace_class.rep_eq)
      apply (rule mult_right_mono)
      apply (rule kraus_family_sums_bounded_by_norm)
      using assms \<open>M \<subseteq> \<EE>\<close> by auto
    finally show \<open>(\<Sum>(E,_)\<in>M. Re (trace_tc (sandwich_tc E \<rho>))) \<le> kraus_family_norm \<EE> * norm \<rho>\<close>
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

(* definition galois_connection_on :: \<open>'a::order set \<Rightarrow> 'b::order set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool\<close> where
  \<open>galois_connection_on X Y f g \<longleftrightarrow> (\<forall>x\<in>X. \<forall>y\<in>Y. f x \<le> y \<longleftrightarrow> x \<le> g y)\<close>



lemma is_Sup_preserved_mono:
  assumes \<open>is_Sup X s\<close>
  assumes \<open>mono f\<close>
  shows \<open>is_Sup (f ` X) (f s)\<close>
proof (rule is_SupI)
  show \<open>x \<in> f ` X \<Longrightarrow> x \<le> f s\<close> for x
    using assms(1) assms(2) is_Sup_def monoD by fastforce
  show \<open>(\<And>x. x \<in> f ` X \<Longrightarrow> x \<le> y) \<Longrightarrow> f s \<le> y\<close> for y
try0
by - *)

(*
lemma is_Sup_preserved_norm_tc:
  fixes X and s :: \<open>('a::chilbert_space, 'a) trace_class\<close>
  assumes \<open>is_Sup X s\<close>
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> x \<ge> 0\<close>
  shows \<open>is_Sup (norm ` X) (norm s)\<close>
proof (rule is_SupI)
  show \<open>r \<le> norm s\<close> if \<open>r \<in> norm ` X\<close> for r
  proof -
    from that obtain x where rx: \<open>r = norm x\<close> and \<open>x \<in> X\<close>
      by auto
    with assms have \<open>x \<ge> 0\<close> and \<open>x \<le> s\<close>
      by (simp_all add: is_Sup_def)
    then have \<open>norm x \<le> norm s\<close>
      using norm_cblinfun_mono_trace_class by blast
    then show \<open>r \<le> norm s\<close>
      by (simp add: rx)
  qed
  show \<open>norm s \<le> t\<close> if \<open>\<And>r. r \<in> norm ` X \<Longrightarrow> r \<le> t\<close> for t
  proof -
    from assms

*)

(*
lemma kraus_family_map_bounded_tight:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family_norm \<EE> = (\<Squnion>\<rho>\<in>{\<rho>. \<rho>\<ge>0}. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close>
proof (rule antisym)
  from assms
  have bounded: \<open>norm (kraus_family_map \<EE> \<rho>) / norm \<rho> \<le> kraus_family_norm \<EE>\<close> if \<open>\<rho> \<ge> 0\<close> for \<rho>
    apply (cases \<open>\<rho> = 0\<close>)
    by (simp_all add: that kraus_family_norm_geq0 kraus_family_map_bounded_pos linordered_field_class.pos_divide_le_eq)

(* TODO used? *)
  have aux1: \<open>0 \<le> (\<Sum>(E,x)\<in>M. sandwich_tc E (Abs_trace_class (selfbutter \<psi>)))\<close> for \<psi> M
    by (auto intro!: sum_nonneg scaleC_nonneg_nonneg of_nat_0_le_iff Abs_trace_class_geq0I
        trace_class_sandwich sandwich_tc_pos)

  show \<open>(\<Squnion>\<rho>\<in>{\<rho>. \<rho>\<ge>0}. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>) \<le> kraus_family_norm \<EE>\<close>
    apply (rule cSUP_least)
    using bounded by auto
  show \<open>kraus_family_norm \<EE> \<le> (\<Squnion>\<rho>\<in>{\<rho>. \<rho>\<ge>0}. norm (kraus_family_map \<EE> \<rho>) / norm \<rho>)\<close>
    using cSUP_least
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
*)

(* lemma
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>((\<lambda>F. norm (\<Sum>E\<in>F. complex_of_nat (\<EE> E) *\<^sub>C (E* o\<^sub>C\<^sub>L E))) \<longlongrightarrow> kraus_family_norm \<EE>) (finite_subsets_at_top UNIV)\<close> *)

lemma kraus_family_bound_from_map:
  assumes \<open>kraus_family \<EE>\<close>
  shows \<open>\<psi> \<bullet>\<^sub>C kraus_family_bound \<EE> \<phi> = trace_tc (kraus_family_map \<EE> (tc_butterfly \<phi> \<psi>))\<close>
proof -
  from assms
  have \<open>has_sum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE> (kraus_family_bound \<EE>)\<close>
    by (simp add: kraus_family_bound_has_sum)
  then have \<open>((\<lambda>(E, x). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum \<psi> \<bullet>\<^sub>C kraus_family_bound \<EE> \<phi>) \<EE>\<close>
    by (auto intro!: simp: has_sum_in_cweak_operator_topology_pointwise case_prod_unfold)
  moreover have \<open>((\<lambda>(E, x). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum trace_tc (kraus_family_map \<EE> (tc_butterfly \<phi> \<psi>))) \<EE>\<close>
  proof -
    have *: \<open>trace_tc (sandwich_tc E (tc_butterfly \<phi> \<psi>)) = \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>\<close> for E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      by (auto intro!: simp: trace_tc.rep_eq from_trace_class_sandwich_tc
          sandwich_apply tc_butterfly.rep_eq circularity_of_trace[symmetric, of _ E]
          trace_class_comp_left cblinfun_compose_assoc trace_butterfly_comp)
    from kraus_family_map_has_sum[OF assms]
    have \<open>((\<lambda>(E,x). sandwich_tc E (tc_butterfly \<phi> \<psi>)) has_sum kraus_family_map \<EE> (tc_butterfly \<phi> \<psi>)) \<EE>\<close>
      by blast
    then have \<open>((\<lambda>(E,x). trace_tc (sandwich_tc E (tc_butterfly \<phi> \<psi>))) has_sum trace_tc (kraus_family_map \<EE> (tc_butterfly \<phi> \<psi>))) \<EE>\<close>
      unfolding case_prod_unfold
      apply (rule has_sum_bounded_linear[rotated, unfolded o_def])
      by (simp add: bounded_clinear.bounded_linear)
    then
    show ?thesis
      by (simp add: * )
  qed
  ultimately show ?thesis
    using has_sum_unique by blast
qed


lemma kraus_family_bound_welldefined:
  assumes \<open>kraus_equivalent \<EE> \<FF>\<close>
  shows \<open>kraus_family_bound \<EE> = kraus_family_bound \<FF>\<close>
  using assms by (auto intro!: cblinfun_cinner_eqI simp: kraus_equivalent_def kraus_family_bound_from_map)

lemma kraus_family_norm_welldefined:
  assumes \<open>kraus_equivalent \<EE> \<FF>\<close>
  shows \<open>kraus_family_norm \<EE> = kraus_family_norm \<FF>\<close>
  using assms
  by (simp add: kraus_family_norm_def kraus_family_bound_welldefined)

lift_definition kraus_map_norm :: \<open>('a::chilbert_space, 'b::chilbert_space) kraus_map \<Rightarrow> real\<close> is
  kraus_family_norm
  by (rule kraus_family_norm_welldefined)

lemma kraus_map_of_op_norm[simp]:
  \<open>kraus_map_norm (kraus_map_of_op E) = (norm E)\<^sup>2\<close>
  apply (transfer fixing: E)
  by simp

(* lemma kraus_family_comp_finite:
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
  also have \<open>\<dots> = norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C sandwich (F* )
                             (\<Sum>E\<in>SE. of_nat (\<EE> E) *\<^sub>C ((E* o\<^sub>C\<^sub>L E))))\<close>
    by (simp add: sum.cartesian_product scaleC_sum_right 
        sandwich_apply Extra_Ordered_Fields.sign_simps(5)
        cblinfun_compose_assoc cblinfun_compose_sum_right cblinfun_compose_sum_left)
  also have \<open>\<dots> \<le> norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C sandwich (F* ) (BE *\<^sub>C id_cblinfun))\<close>
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
qed *)

lemma kraus_family_kraus_family_comp_dependent:
  fixes \<EE> :: \<open>'y \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('c::chilbert_space, 'a, 'y) kraus_family\<close>
  assumes \<EE>_family: \<open>\<And>y. kraus_family (\<EE> y)\<close> and \<FF>_family: \<open>kraus_family \<FF>\<close>
  assumes \<EE>_uniform: \<open>\<And>y. kraus_family_norm (\<EE> y) \<le> B\<close>
  shows \<open>kraus_family (kraus_family_comp_dependent \<EE> \<FF>)\<close>
proof -
  obtain BF where BF: \<open>(\<Sum>(F, y)\<in>M. (F* o\<^sub>C\<^sub>L F)) \<le> BF\<close> if \<open>M \<subseteq> \<FF>\<close> and \<open>finite M\<close> for M
    by (metis (mono_tags, lifting) assms(2) bdd_above.unfold imageI kraus_family_def mem_Collect_eq)
  define BE :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>BE = B *\<^sub>R id_cblinfun\<close>
  define \<FF>x\<EE> where \<open>\<FF>x\<EE> = (SIGMA (F,y):\<FF>. \<EE> y)\<close>
  from \<EE>_uniform
  have BE: \<open>(\<Sum>(E, x)\<in>M. (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> if \<open>M \<subseteq> \<EE> y\<close> and \<open>finite M\<close> for M y
    using that
    using kraus_family_sums_bounded_by_norm[OF \<EE>_family[where y=y]]
    apply (auto intro!: simp: BE_def case_prod_beta)
    by (smt (verit) adj_0 comparable_hermitean less_eq_scaled_id_norm positive_cblinfun_squareI scaleR_scaleC sum_nonneg)
  have [simp]: \<open>B \<ge> 0\<close>
    using kraus_family_norm_geq0[of \<open>\<EE> undefined\<close>] \<EE>_uniform[of undefined] by auto

  have \<open>bdd_above ((\<lambda>M. \<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) `
            {M. M \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (E,F,x,y))) ` \<FF>x\<EE> \<and> finite M})\<close>
  proof (rule bdd_aboveI, rename_tac A)
    fix A :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'c\<close>
    assume \<open>A \<in> (\<lambda>M. \<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) ` {M. M \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, E, F, x, y)) ` \<FF>x\<EE> \<and> finite M}\<close>
    then obtain C where A_def: \<open>A = (\<Sum>(E,x)\<in>C. E* o\<^sub>C\<^sub>L E)\<close>
      and C\<FF>\<EE>: \<open>C \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, E, F, x, y)) ` \<FF>x\<EE>\<close>
      and [simp]: \<open>finite C\<close>
      by auto
    define CE CF where \<open>CE y = (\<lambda>(_,(E,F,x,y)). (E,x)) ` Set.filter (\<lambda>(_,(E,F,x,y')). y'=y) C\<close> 
      and \<open>CF = (\<lambda>(_,(E,F,x,y)). (F,y)) ` C\<close> for y
    then have [simp]: \<open>finite (CE y)\<close> \<open>finite CF\<close> for y
      by auto
    have C_C1C2: \<open>C \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, E, F, x, y)) ` (SIGMA (F,y):CF. CE y)\<close>
    proof (rule subsetI)
      fix c assume \<open>c \<in> C\<close>
      then obtain EF E F x y where c_def: \<open>c = (EF,E,F,x,y)\<close>
        by (metis surj_pair)
      from \<open>c \<in> C\<close> have EF_def: \<open>EF = E o\<^sub>C\<^sub>L F\<close>
        using C\<FF>\<EE> by (auto intro!: simp: c_def)
      from \<open>c \<in> C\<close> have 1: \<open>(F,y) \<in> CF\<close>
        apply (simp add: CF_def c_def)
        by force
      from \<open>c \<in> C\<close> have 2: \<open>(E,x) \<in> CE y\<close>
        apply (simp add: CE_def c_def)
        by force
      from 1 2 show \<open>c \<in> (\<lambda>((F, y), E, x). (E o\<^sub>C\<^sub>L F, E, F, x, y)) ` (SIGMA (F, y):CF. CE y)\<close>
        apply (simp add: c_def EF_def)
        by force
    qed

    have CE_sub_\<EE>: \<open>CE y \<subseteq> \<EE> y\<close> and \<open>CF \<subseteq> \<FF>\<close> for y
      using C\<FF>\<EE> by (auto simp add: CE_def CF_def \<FF>x\<EE>_def case_prod_unfold)
    have CE_BE: \<open>(\<Sum>(E, x)\<in>CE y. (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> for y
      using BE[where y=y] CE_sub_\<EE>[of y]
      by auto
      
    have \<open>A \<le> (\<Sum>(E,x) \<in> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, E, F, x, y)) ` (SIGMA (F,y):CF. CE y). E* o\<^sub>C\<^sub>L E)\<close>
      using C_C1C2 apply (auto intro!: finite_imageI sum_mono2 simp: A_def )
      by (metis adj_cblinfun_compose positive_cblinfun_squareI)
    also have \<open>\<dots> = (\<Sum>((F,y), (E,x))\<in>(SIGMA (F,y):CF. CE y). (F* o\<^sub>C\<^sub>L (E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L F))\<close>
      apply (subst sum.reindex)
      by (auto intro!: inj_onI simp: case_prod_unfold cblinfun_compose_assoc)
    also have \<open>\<dots> = (\<Sum>(F, y)\<in>CF. sandwich (F*) (\<Sum>(E, x)\<in>CE y. (E* o\<^sub>C\<^sub>L E)))\<close>
      apply (subst sum.Sigma[symmetric])
      by (auto intro!: simp: case_prod_unfold sandwich_apply cblinfun_compose_sum_right cblinfun_compose_sum_left simp flip: )
    also have \<open>\<dots> \<le> (\<Sum>(F, y)\<in>CF. sandwich (F*) BE)\<close>
      using CE_BE by (auto intro!: sum_mono sandwich_mono simp: case_prod_unfold scaleR_scaleC)
    also have \<open>\<dots> = B *\<^sub>R (\<Sum>(F, y)\<in>CF. F* o\<^sub>C\<^sub>L F)\<close>
      by (simp add: scaleR_sum_right case_prod_unfold sandwich_apply BE_def)
    also have \<open>\<dots> \<le> B *\<^sub>R BF\<close>
      using BF by (simp add: \<open>CF \<subseteq> \<FF>\<close> scaleR_left_mono case_prod_unfold)
    finally show \<open>A \<le> B *\<^sub>R BF\<close>
      by -
  qed
  then show ?thesis
    by (simp add: \<FF>x\<EE>_def kraus_family_def kraus_family_comp_dependent_def case_prod_beta conj_commute 
        case_prod_unfold)
qed

lemma kraus_family_kraus_family_comp[intro]:
  fixes \<EE> :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('c::chilbert_space, 'a, 'y) kraus_family\<close>
  assumes \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family (kraus_family_comp \<EE> \<FF>)\<close>
  using assms by (auto intro!: kraus_family_kraus_family_comp_dependent simp: kraus_family_comp_def)

(*
proof -
  from assms obtain BE where BE: \<open>norm (\<Sum>(E,_)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> BE\<close> if \<open>finite S\<close> and \<open>S \<subseteq> \<EE>\<close> for S
    apply (auto simp: kraus_family_def case_prod_unfold)
    by xxx
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
    also have \<open>\<dots> = norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C sandwich (F* )
                             (\<Sum>E\<in>SE. of_nat (\<EE> E) *\<^sub>C ((E* o\<^sub>C\<^sub>L E))))\<close>
      by (simp add: case_prod_beta sum.cartesian_product scaleC_sum_right scaleC_scaleC
          sandwich_apply Extra_Ordered_Fields.sign_simps(5)
          cblinfun_compose_assoc cblinfun_compose_sum_right cblinfun_compose_sum_left)
    also have \<open>\<dots> \<le> norm (\<Sum>F\<in>SF. of_nat (\<FF> F) *\<^sub>C sandwich (F* ) (BE *\<^sub>C id_cblinfun))\<close>
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
*)

lemma kraus_family_map_mono:
  assumes \<open>kraus_family \<EE>\<close> and \<open>\<rho> \<ge> \<tau>\<close>
  shows \<open>kraus_family_map \<EE> \<rho> \<ge> kraus_family_map \<EE> \<tau>\<close>
  apply (subst diff_ge_0_iff_ge[symmetric])
  apply (subst kraus_family_map_minus_right[symmetric])
   apply (fact assms)
  apply (rule kraus_family_map_pos)
  using assms(2) by (subst diff_ge_0_iff_ge)

lemma kraus_family_map_geq_sum:
  assumes \<open>kraus_family \<EE>\<close> and \<open>\<rho> \<ge> 0\<close> and \<open>M \<subseteq> \<EE>\<close>
  shows \<open>kraus_family_map \<EE> \<rho> \<ge> (\<Sum>(E,_)\<in>M. sandwich_tc E \<rho>)\<close>
proof (cases \<open>finite M\<close>)
  case True
  have *: \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on X\<close> if \<open>X \<subseteq> \<EE>\<close> for X
    apply (rule summable_on_subset_banach[where A=\<EE>])
     apply (rule kraus_family_map_summable[unfolded case_prod_unfold])
    using assms that by auto
  show ?thesis
    apply (subst infsum_finite[symmetric])
    using assms 
    by (auto intro!: infsum_mono_neutral_traceclass * scaleC_nonneg_nonneg of_nat_0_le_iff 
        True sandwich_tc_pos
        simp: kraus_family_map_def case_prod_unfold)
next
  case False
  with assms show ?thesis
    by (simp add: kraus_family_map_pos) 
qed

lemma kraus_family_comp_dependent_apply:
  fixes \<EE> :: \<open>'y \<Rightarrow> ('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space \<times> 'x) set\<close>
    and \<FF> :: \<open>('c::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a \<times> 'y) set\<close>
  assumes kraus\<EE>: \<open>\<And>x. kraus_family (\<EE> x)\<close> and kraus\<FF>: \<open>kraus_family \<FF>\<close>
  assumes \<open>\<And>y. kraus_family_norm (\<EE> y) \<le> B\<close>
  shows \<open>kraus_family_map (kraus_family_comp_dependent \<EE> \<FF>) \<rho> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>\<FF>. kraus_family_map (\<EE> y) (sandwich_tc F \<rho>))\<close>
proof -
  have family: \<open>kraus_family (kraus_family_comp_dependent \<EE> \<FF>)\<close>
    by (auto intro!: kraus_family_kraus_family_comp_dependent assms)

  have sum2: \<open>(\<lambda>(F, x). sandwich_tc F \<rho>) summable_on \<FF>\<close>
    using kraus_family_map_summable[of \<FF> \<rho>] kraus\<FF> by (simp add: case_prod_unfold)
  from family have \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on 
          (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, E, F, x, y)) ` (SIGMA (F,y):\<FF>. \<EE> y)\<close>
    using kraus_family_map_summable by (simp add: kraus_family_comp_dependent_def kraus_family_comp_def case_prod_unfold)
  then have sum1: \<open>(\<lambda>((F,y), (E,x)). sandwich_tc (E o\<^sub>C\<^sub>L F) \<rho>) summable_on (SIGMA (F,y):\<FF>. \<EE> y)\<close>
    apply (subst (asm) summable_on_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)

  have \<open>kraus_family_map (kraus_family_comp_dependent \<EE> \<FF>) \<rho>
          = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, E, F, x, y)) ` (SIGMA (F,y):\<FF>. \<EE> y). sandwich_tc (fst E) \<rho>)\<close>
    by (simp add: kraus_family_map_def kraus_family_comp_dependent_def kraus_family_comp_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((F,y), (E,x))\<in>(SIGMA (F,y):\<FF>. \<EE> y). sandwich_tc (E o\<^sub>C\<^sub>L F) \<rho>)\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>\<FF>. \<Sum>\<^sub>\<infinity>(E,x)\<in>\<EE> y. sandwich_tc (E o\<^sub>C\<^sub>L F) \<rho>)\<close>
    apply (subst infsum_Sigma'_banach[symmetric])
    using sum1 by (auto simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>\<FF>. \<Sum>\<^sub>\<infinity>(E,x)\<in>\<EE> y. sandwich_tc E (sandwich_tc F \<rho>))\<close>
    by (simp add: sandwich_tc_compose)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>\<FF>. kraus_family_map (\<EE> y) (sandwich_tc F \<rho>))\<close>
    by (simp add: kraus_family_map_def case_prod_unfold)
  finally show ?thesis
    by -
qed

lemma kraus_family_comp_apply:
  fixes \<EE> :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space \<times> 'x) set\<close>
    and \<FF> :: \<open>('c::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a \<times> 'y) set\<close>
  assumes \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) = kraus_family_map \<EE> \<circ> kraus_family_map \<FF>\<close>
proof (rule ext, rename_tac \<rho>)
  fix \<rho> :: \<open>('c, 'c) trace_class\<close>

  from \<open>kraus_family \<FF>\<close>
  have sumF: \<open>(\<lambda>(F, y). sandwich_tc F \<rho>) summable_on \<FF>\<close>
    by (rule kraus_family_map_summable)
  have \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) \<rho> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>\<FF>. kraus_family_map \<EE> (sandwich_tc F \<rho>))\<close>
    by (auto intro!: kraus_family_comp_dependent_apply simp: kraus_family_comp_def \<open>kraus_family \<EE>\<close> \<open>kraus_family \<FF>\<close>)
  also have \<open>\<dots> = kraus_family_map \<EE> (\<Sum>\<^sub>\<infinity>(F,y)\<in>\<FF>. sandwich_tc F \<rho>)\<close>
    apply (subst infsum_bounded_linear[symmetric, where f=\<open>kraus_family_map \<EE>\<close>])
    using sumF by (auto intro!: bounded_clinear.bounded_linear kraus_family_map_bounded_clinear
        simp: o_def case_prod_unfold \<open>kraus_family \<EE>\<close>)
  also have \<open>\<dots> = (kraus_family_map \<EE> \<circ> kraus_family_map \<FF>) \<rho>\<close>
    by (simp add: o_def kraus_family_map_def case_prod_unfold)
  finally show \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) \<rho> = (kraus_family_map \<EE> \<circ> kraus_family_map \<FF>) \<rho>\<close>
    by -
qed
(*
  have family: \<open>kraus_family (kraus_family_comp \<EE> \<FF>)\<close>
    by (auto intro!: kraus_family_kraus_family_comp)

  have sum2: \<open>(\<lambda>(F, x). sandwich_tc F *\<^sub>V \<rho>) summable_on \<FF>\<close>
    by (simp add: kraus_family_map_summable split_def)
  from family have \<open>(\<lambda>E. sandwich_tc (fst E) *\<^sub>V \<rho>) summable_on (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, E, F, x, y)) ` (\<FF> \<times> \<EE>)\<close>
    by (auto intro!: kraus_family_map_summable simp: kraus_family_comp_dependent_def kraus_family_comp_def case_prod_unfold)
  then have \<open>(\<lambda>((F,y), (E,x)). sandwich_tc (E o\<^sub>C\<^sub>L F) *\<^sub>V \<rho>) summable_on \<FF> \<times> \<EE>\<close>
    apply (subst (asm) summable_on_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  then have sum1: \<open>(\<lambda>((E,x), (F,y)). sandwich_tc (E o\<^sub>C\<^sub>L F) *\<^sub>V \<rho>) summable_on \<EE> \<times> \<FF>\<close>
    apply (rule_tac summable_on_reindex_bij_betw[where g=prod.swap and A=\<open>\<FF> \<times> \<EE>\<close>, THEN iffD1])
     apply (auto intro!: simp: case_prod_unfold)
    using bij_betw_def by fastforce
  have \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) \<rho>
          = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, E, F, x, y)) ` (\<FF> \<times> \<EE>). sandwich_tc (fst E) *\<^sub>V \<rho>)\<close>
    by (simp add: kraus_family_map_def kraus_family_comp_dependent_def kraus_family_comp_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((F,y), (E,x))\<in>\<FF> \<times> \<EE>. sandwich_tc (E o\<^sub>C\<^sub>L F) *\<^sub>V \<rho>)\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((E,x), (F,y))\<in>\<EE> \<times> \<FF>. sandwich_tc (E o\<^sub>C\<^sub>L F) *\<^sub>V \<rho>)\<close>
    apply (subst infsum_reindex_bij_betw[where g=prod.swap and A=\<open>\<EE> \<times> \<FF>\<close>, symmetric])
     apply (auto intro!: simp: case_prod_unfold)
    by (metis bij_betw_def inj_swap product_swap)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>\<EE>. \<Sum>\<^sub>\<infinity>(F,x)\<in>\<FF>. sandwich_tc (E o\<^sub>C\<^sub>L F) *\<^sub>V \<rho>)\<close>
    apply (subst infsum_Sigma'_banach[symmetric])
    using sum1 by (auto simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>\<EE>. \<Sum>\<^sub>\<infinity>(F,x)\<in>\<FF>. sandwich_tc E *\<^sub>V sandwich_tc F *\<^sub>V \<rho>)\<close>
    by (simp add: sandwich_tc_compose)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>\<EE>. sandwich_tc E *\<^sub>V (\<Sum>\<^sub>\<infinity>(F,x)\<in>\<FF>. sandwich_tc F *\<^sub>V \<rho>))\<close>
    apply (subst infsum_cblinfun_apply[symmetric])
    using sum2 by (auto simp add: case_prod_unfold)
  also have \<open>\<dots> = kraus_family_map \<EE> (kraus_family_map \<FF> \<rho>)\<close>
    by (simp add: kraus_family_map_def case_prod_unfold)
  finally show \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) \<rho> = (kraus_family_map \<EE> \<circ> kraus_family_map \<FF>) \<rho>\<close>
    by (simp add: o_def)
qed
*)

(*   fix \<rho> :: \<open>('c, 'c) trace_class\<close>
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
 *)
(*   define EF where \<open>EF G = {(E, F). \<EE> E \<noteq> 0 \<and> \<FF> F \<noteq> 0 \<and> E o\<^sub>C\<^sub>L F = G}\<close> for G
  have finite_EF: \<open>finite (EF G)\<close> if \<open>G \<noteq> 0\<close> for G
    unfolding EF_def
    using assms that by (rule kraus_family_comp_finite) *)

(*  have sum1: \<open>(\<lambda>(E, F). (sandwich_tc E *\<^sub>V complex_of_nat (\<FF> F) *\<^sub>C (sandwich_tc F *\<^sub>V \<rho>))) summable_on U\<close> for U
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
*)
(*   show \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) \<rho> = (kraus_family_map \<EE> \<circ> kraus_family_map \<FF>) \<rho>\<close>
    
qed *)

lemma kraus_family_op_weight_scale:
  assumes \<open>r > 0\<close>
  shows \<open>kraus_family_op_weight \<EE> (r *\<^sub>R E) = kraus_family_op_weight \<EE> E\<close>
proof -
  have [simp]: \<open>(\<exists>r'>0. r *\<^sub>R E = r' *\<^sub>R F) \<longleftrightarrow> (\<exists>r'>0. E = r' *\<^sub>R F)\<close> for F
    apply (rule Ex_iffI[where f=\<open>\<lambda>r'. r' /\<^sub>R r\<close> and g=\<open>\<lambda>r'. r *\<^sub>R r'\<close>])
    using assms apply auto
    by (metis divideR_right mult_zero_right not_square_less_zero pth_5)
  show ?thesis
    using assms
    by (simp add: kraus_family_related_ops_def kraus_family_op_weight_def)
qed

(* instantiation cblinfun_wot :: (complex_normed_vector, complex_inner) uniform_topological_group_add begin
lift_definition uniformity_cblinfun_wot :: \<open>(('a, 'b) cblinfun_wot \<times> ('a, 'b) cblinfun_wot) filter\<close> is
  \<open>SUP \<psi> \<phi>. (INF e\<in>{0 <..}. principal {(x, y). \<psi> \<bullet>\<^sub>C (x-y :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b) \<phi> < e})\<close>.
instance
proof
  have \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)\<close> for U :: \<open>('a, 'b) cblinfun_wot set\<close>
    apply transfer
    apply (simp add: openin_cweak_operator_topology eventually_Sup)
  thm uniformi *)

lemma kraus_family_def2:
  \<open>kraus_family \<EE> \<longleftrightarrow> summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE>\<close>
proof (rule iffI)
  assume \<open>kraus_family \<EE>\<close>
  show \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE>\<close>
    using \<open>kraus_family \<EE>\<close> kraus_family_bound_has_sum summable_on_in_def by blast
next
  assume \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE>\<close>
  then show \<open>kraus_family \<EE>\<close>
    by (auto intro!: summable_wot_bdd_above[where X=\<EE>] positive_cblinfun_squareI simp: kraus_family_def)
qed

lemma kraus_family_def2':
  \<open>kraus_family \<EE> \<longleftrightarrow> (\<lambda>(E,x). Abs_cblinfun_wot (E* o\<^sub>C\<^sub>L E)) summable_on \<EE>\<close>
  apply (transfer' fixing: \<EE>)
  by (simp add: kraus_family_def2)

lemma 
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  assumes \<open>kraus_family \<EE>\<close>
  shows kraus_family_flatten_same_map: \<open>kraus_family_map (kraus_family_flatten \<EE>) = kraus_family_map \<EE>\<close>
    and kraus_family_kraus_family_flatten[intro]: \<open>kraus_family (kraus_family_flatten \<EE>)\<close>
    and kraus_family_flatten_bound: \<open>kraus_family_bound (kraus_family_flatten \<EE>) = kraus_family_bound \<EE>\<close>
    and kraus_family_flatten_norm: \<open>kraus_family_norm (kraus_family_flatten \<EE>) = kraus_family_norm \<EE>\<close>
proof (rule ext)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  define good normal \<sigma> B B' where \<open>good E \<longleftrightarrow> (norm E)\<^sup>2 = kraus_family_op_weight \<EE> E \<and> E \<noteq> 0\<close>
    and \<open>normal E = E /\<^sub>R sqrt (kraus_family_op_weight \<EE> E)\<close>
    and \<open>\<sigma> = kraus_family_map \<EE> \<rho>\<close>
    and \<open>B = kraus_family_bound \<EE>\<close> 
    and \<open>B' = Abs_cblinfun_wot B\<close> 
  for E
  have E_inv: \<open>kraus_family_op_weight \<EE> E \<noteq> 0\<close> if \<open>good E\<close> for E
    using that by (auto simp:  good_def)

  have inj_snd: \<open>inj_on snd (SIGMA p:{E::_\<times>unit. good (fst E)}. kraus_family_related_ops \<EE> (fst p))\<close>
  proof (rule inj_onI)
    fix EFx EFx' :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> unit) \<times> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x\<close>
    assume EFx_in: \<open>EFx \<in> (SIGMA p:{E. good (fst E)}. kraus_family_related_ops \<EE> (fst p))\<close>
      and EFx'_in: \<open>EFx' \<in> (SIGMA p:{E. good (fst E)}. kraus_family_related_ops \<EE> (fst p))\<close>
    assume snd_eq: \<open>snd EFx = snd EFx'\<close>
    obtain E F x where [simp]: \<open>EFx = ((E,()),F,x)\<close>
      by (metis (full_types) old.unit.exhaust surj_pair)
    obtain E' F' x' where [simp]: \<open>EFx' = ((E',()),F',x')\<close> 
      by (metis (full_types) old.unit.exhaust surj_pair)
    from snd_eq have [simp]: \<open>F' = F\<close> and [simp]: \<open>x' = x\<close>
      by auto
    from EFx_in have \<open>good E\<close> and F_rel_E: \<open>(F, x) \<in> kraus_family_related_ops \<EE> E\<close>
      by auto
    from EFx'_in have \<open>good E'\<close> and F_rel_E': \<open>(F, x) \<in> kraus_family_related_ops \<EE> E'\<close>
      by auto
    from \<open>good E\<close> have \<open>E \<noteq> 0\<close>
      by (simp add: good_def)
    from \<open>good E'\<close> have \<open>E' \<noteq> 0\<close>
      by (simp add: good_def)
    from F_rel_E obtain r where ErF: \<open>E = r *\<^sub>R F\<close> and \<open>r > 0\<close>
      by (auto intro!: simp: kraus_family_related_ops_def)
    from F_rel_E' obtain r' where E'rF: \<open>E' = r' *\<^sub>R F\<close> and \<open>r' > 0\<close>
      by (auto intro!: simp: kraus_family_related_ops_def)

    define r'' where \<open>r'' = r' / r\<close>
    with E'rF ErF \<open>E \<noteq> 0\<close>
    have E'_E: \<open>E' = r'' *\<^sub>R E\<close>
      by auto
    with \<open>r' > 0\<close> \<open>r > 0\<close> \<open>E' \<noteq> 0\<close>
    have [simp]: \<open>r'' > 0\<close>
      by (fastforce simp: r''_def)
    from E'_E have \<open>kraus_family_op_weight \<EE> E' = kraus_family_op_weight \<EE> E\<close>
      by (simp add: kraus_family_op_weight_scale)
    with \<open>good E\<close> \<open>good E'\<close> have \<open>(norm E')\<^sup>2 = (norm E)\<^sup>2\<close>
      by (auto intro!: simp: good_def)
    with \<open>E' = r'' *\<^sub>R E\<close>
    have \<open>E' = E\<close>
      using \<open>0 < r''\<close> by force
    then show \<open>EFx = EFx'\<close>
      by simp
  qed

  have snd_sigma: \<open>snd ` (SIGMA (E, x):{E::_\<times>unit. good (fst E)}. kraus_family_related_ops \<EE> E)
      = {(F, x). (F, x) \<in> \<EE> \<and> F \<noteq> 0}\<close>
  proof (intro Set.set_eqI iffI)
    fix Fx
    assume asm: \<open>Fx \<in> snd ` (SIGMA (E, x):{E. good (fst E)}. kraus_family_related_ops \<EE> E)\<close>
    obtain F x where Fx_def: \<open>Fx = (F,x)\<close> by fastforce
    with asm obtain E where Fx_rel_E: \<open>(F, x) \<in> kraus_family_related_ops \<EE> E\<close> and \<open>good E\<close>
      by auto
    then have \<open>(F, x) \<in> \<EE>\<close>
      by (simp add: kraus_family_related_ops_def)
    from Fx_rel_E obtain r where \<open>E = r *\<^sub>R F\<close>
      by (smt (verit) kraus_family_related_ops_def mem_Collect_eq prod.sel(1) split_def)
    with \<open>good E\<close> have \<open>F \<noteq> 0\<close>
      by (simp add: good_def)
    with \<open>(F, x) \<in> \<EE>\<close> show \<open>Fx \<in> {(F, x). (F, x) \<in> \<EE> \<and> F \<noteq> 0}\<close>
      by (simp add: Fx_def)
  next
    fix Fx
    assume asm: \<open>Fx \<in> {(F, x). (F, x) \<in> \<EE> \<and> F \<noteq> 0}\<close>
    obtain F x where Fx_def: \<open>Fx = (F,x)\<close> by fastforce
    from asm have \<open>(F, x) \<in> \<EE>\<close> and \<open>F \<noteq> 0\<close>
      by (auto simp: Fx_def)
    then have [simp]: \<open>kraus_family_op_weight \<EE> F \<noteq> 0\<close>
      by (simp add: assms kraus_family_op_weight_neq0)
    then have [simp]: \<open>kraus_family_op_weight \<EE> F > 0\<close>
      using kraus_family_op_weight_geq0 
      by (metis less_eq_real_def)
    define E where \<open>E = (sqrt (kraus_family_op_weight \<EE> F) / norm F) *\<^sub>R F\<close>
    have \<open>good E\<close>
      by (auto intro!: simp: good_def E_def \<open>F \<noteq> 0\<close> kraus_family_op_weight_scale)
    have \<open>(F, x) \<in> kraus_family_related_ops \<EE> E\<close>
      by (auto intro!: \<open>(F, x) \<in> \<EE>\<close> simp: kraus_family_related_ops_def E_def \<open>F \<noteq> 0\<close>)
    with \<open>good E\<close>
    show \<open>Fx \<in> snd ` (SIGMA (E, x):{E::_\<times>unit. good (fst E)}. kraus_family_related_ops \<EE> E)\<close>
      by (auto intro!: image_eqI[where x=\<open>((E,()),F,x)\<close>] simp: Fx_def)
  qed

  show \<open>kraus_family_map (kraus_family_flatten \<EE>) \<rho> = \<sigma>\<close>
  proof -
    from \<open>kraus_family \<EE>\<close>
    have \<open>(\<lambda>(F,x). sandwich_tc F \<rho>) summable_on \<EE>\<close>
      using kraus_family_map_summable by (simp add: case_prod_unfold)
    then have \<open>((\<lambda>(F,x). sandwich_tc F \<rho>) has_sum \<sigma>) \<EE>\<close>
      by (simp add: \<sigma>_def kraus_family_map_def split_def)
    then have \<open>((\<lambda>(F,x). sandwich_tc F \<rho>) has_sum \<sigma>) {(F,x)\<in>\<EE>. F \<noteq> 0}\<close>
      apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
      by auto
    then have \<open>((\<lambda>(F,x). sandwich_tc F \<rho>) has_sum \<sigma>)
           (snd ` (SIGMA (E,x::unit):{E. good (fst E)}. kraus_family_related_ops \<EE> E))\<close>
      by (simp add: snd_sigma)
    then have \<open>((\<lambda>((E,x::unit), (F,y)). sandwich_tc F \<rho>) has_sum \<sigma>)
       (SIGMA (E,x):{E. good (fst E)}. kraus_family_related_ops \<EE> E)\<close>
      apply (subst (asm) has_sum_reindex)
      by (auto intro!: inj_on_def inj_snd simp: o_def case_prod_unfold)
    then have sum1: \<open>((\<lambda>((E,x::unit), (F,x)). (norm F)\<^sup>2 *\<^sub>R sandwich_tc (normal E) \<rho>) has_sum \<sigma>)
    (SIGMA (E,x):{p. good (fst p)}. kraus_family_related_ops \<EE> E)\<close>
      apply (rule has_sum_cong[THEN iffD2, rotated])
      apply (auto intro!: simp: good_def normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv
          kraus_family_related_ops_def kraus_family_op_weight_scale)
      by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(5) linorder_not_less more_arith_simps(11) mult_eq_0_iff norm_le_zero_iff order.refl power2_eq_square right_inverse scale_one)
    then have \<open>((\<lambda>(E,_). \<Sum>\<^sub>\<infinity>(F, x)\<in>kraus_family_related_ops \<EE> E.
                (norm F)\<^sup>2 *\<^sub>R sandwich_tc (normal E) \<rho>) has_sum \<sigma>) {(E, x::unit). good E}\<close>
      by (auto intro!: has_sum_Sigma'_banach simp add: case_prod_unfold)
    then have \<open>((\<lambda>(E,_). (\<Sum>\<^sub>\<infinity>(F, x)\<in>kraus_family_related_ops \<EE> E. (norm F)\<^sup>2) *\<^sub>R sandwich_tc (normal E) \<rho>)
                        has_sum \<sigma>) {(E, x::unit). good E}\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      apply auto
      by (smt (verit) Complex_Vector_Spaces.infsum_scaleR_left cblinfun.scaleR_left infsum_cong split_def)
    then have \<open>((\<lambda>(E,_). kraus_family_op_weight \<EE> E *\<^sub>R sandwich_tc (normal E) \<rho>) has_sum \<sigma>) {(E, x::unit). good E}\<close>
      by (simp add: kraus_family_op_weight_def)
    then have \<open>((\<lambda>(E,_). sandwich_tc E \<rho>) has_sum \<sigma>) {(E, x::unit). good E}\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      by (auto intro!: simp: normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv)
    then have \<open>((\<lambda>(E,_). sandwich_tc E \<rho>) has_sum \<sigma>) (kraus_family_flatten \<EE>)\<close>
      by (simp add: kraus_family_flatten_def good_def)
    then show \<open>kraus_family_map (kraus_family_flatten \<EE>) \<rho> = \<sigma>\<close>
      by (simp add: kraus_family_map_def case_prod_unfold infsumI)
  qed

  have bound_has_sum: \<open>has_sum_in cweak_operator_topology (\<lambda>(E,_). E* o\<^sub>C\<^sub>L E) (kraus_family_flatten \<EE>) B\<close>
  proof (unfold has_sum_in_cweak_operator_topology_pointwise, intro allI)
    fix \<psi> \<phi> :: 'a
    define B' where \<open>B' = \<psi> \<bullet>\<^sub>C B \<phi>\<close>
    have \<open>has_sum_in cweak_operator_topology (\<lambda>(F,x). F* o\<^sub>C\<^sub>L F) \<EE> B\<close>
      using B_def assms kraus_family_bound_has_sum by blast
    then have \<open>((\<lambda>(F,x). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B') \<EE>\<close>
      by (simp add: B'_def has_sum_in_cweak_operator_topology_pointwise case_prod_unfold)
    then have \<open>((\<lambda>(F,x). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B') {(F,x)\<in>\<EE>. F \<noteq> 0}\<close>
      apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
      by (auto simp: zero_cblinfun_wot_def)
    then have \<open>((\<lambda>(F,x). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B')
           (snd ` (SIGMA (E,x::unit):{E. good (fst E)}. kraus_family_related_ops \<EE> E))\<close>
      by (simp add: snd_sigma)
    then have \<open>((\<lambda>((E,x::unit), (F,y)). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B')
       (SIGMA (E,x):{E. good (fst E)}. kraus_family_related_ops \<EE> E)\<close>
      apply (subst (asm) has_sum_reindex)
      by (auto intro!: inj_on_def inj_snd simp: o_def case_prod_unfold)
    then have sum1: \<open>((\<lambda>((E,x::unit), (F,x)). (norm F)\<^sup>2 *\<^sub>R (\<psi> \<bullet>\<^sub>C (normal E* o\<^sub>C\<^sub>L normal E) \<phi>)) has_sum B')
    (SIGMA (E,x):{p. good (fst p)}. kraus_family_related_ops \<EE> E)\<close>
      apply (rule has_sum_cong[THEN iffD2, rotated])
      apply (auto intro!: simp: good_def normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv
          kraus_family_related_ops_def kraus_family_op_weight_scale 
          cblinfun.scaleC_left cblinfun.scaleC_right cinner_scaleC_right scaleR_scaleC) 
      by (smt (verit, ccfv_threshold) Extra_Ordered_Fields.sign_simps(4) Extra_Ordered_Fields.sign_simps(5) assms complex_of_real_pos_iff inverse_mult_distrib kraus_family_op_weight_geq0 kraus_family_op_weight_neq0 kraus_family_op_weight_scale less_irrefl of_real_mult power2_eq_square real_sqrt_pow2 right_inverse scaleR_scaleC)
    then have \<open>((\<lambda>(E,_). \<Sum>\<^sub>\<infinity>(F, x)\<in>kraus_family_related_ops \<EE> E.
                (norm F)\<^sup>2 *\<^sub>R (\<psi> \<bullet>\<^sub>C (normal E* o\<^sub>C\<^sub>L normal E) \<phi>)) has_sum B') {(E, x::unit). good E}\<close>
      by (auto intro!: has_sum_Sigma'_banach simp add: case_prod_unfold)
    then have \<open>((\<lambda>(E,_). (\<Sum>\<^sub>\<infinity>(F, x)\<in>kraus_family_related_ops \<EE> E. (norm F)\<^sup>2) *\<^sub>R (\<psi> \<bullet>\<^sub>C (normal E* o\<^sub>C\<^sub>L normal E) \<phi>))
                        has_sum B') {(E, x::unit). good E}\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      apply auto
      by (smt (verit) Complex_Vector_Spaces.infsum_scaleR_left cblinfun.scaleR_left infsum_cong split_def)
    then have \<open>((\<lambda>(E,_). kraus_family_op_weight \<EE> E *\<^sub>R (\<psi> \<bullet>\<^sub>C (normal E* o\<^sub>C\<^sub>L normal E) \<phi>)) has_sum B') {(E, x::unit). good E}\<close>
      by (simp add: kraus_family_op_weight_def)
    then have \<open>((\<lambda>(E,_). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum B') {(E, x::unit). good E}\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      apply (auto intro!: simp: normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv
          cblinfun.scaleR_left scaleR_scaleC
          simp flip: inverse_mult_distrib semigroup_mult.mult_assoc)
      by (metis E_inv field_class.field_inverse kraus_family_op_weight_geq0 mult.commute of_real_eq_0_iff of_real_hom.hom_mult power2_eq_square real_sqrt_pow2)
    then have \<open>((\<lambda>(E,_). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum B') (kraus_family_flatten \<EE>)\<close>
      by (simp add: kraus_family_flatten_def good_def)
    then show \<open>((\<lambda>x. \<psi> \<bullet>\<^sub>C ((case x of (E, uu_) \<Rightarrow> E* o\<^sub>C\<^sub>L E) *\<^sub>V \<phi>)) has_sum B') (kraus_family_flatten \<EE>)\<close>
      by (simp add: case_prod_unfold)
  qed

  from bound_has_sum show family: \<open>kraus_family (kraus_family_flatten \<EE>)\<close>
    by (auto simp: kraus_family_def2 summable_on_in_def)

  from family bound_has_sum show bound: \<open>kraus_family_bound (kraus_family_flatten \<EE>) = B\<close>
    apply (auto intro!: simp: kraus_family_bound_def)
    using has_sum_in_infsum_in has_sum_in_unique hausdorff_cweak_operator_topology summable_on_in_def by blast

  from bound show \<open>kraus_family_norm (kraus_family_flatten \<EE>) = kraus_family_norm \<EE>\<close>
    by (simp add: kraus_family_norm_def B_def)
qed


lift_definition kraus_map_comp :: \<open>('a::chilbert_space,'b::chilbert_space) kraus_map
                                \<Rightarrow> ('c::chilbert_space,'a) kraus_map \<Rightarrow> ('c,'b) kraus_map\<close>
  is \<open>\<lambda>\<EE> \<FF>. kraus_family_flatten (kraus_family_comp \<EE> \<FF>)\<close>
  by (auto intro!: kraus_family_kraus_family_comp kraus_family_kraus_family_flatten
      simp add: kraus_equivalent_def kraus_family_comp_apply kraus_family_flatten_same_map kraus_family_kraus_family_comp)

definition \<open>kraus_map_id = kraus_map_of_op id_cblinfun\<close>

lemma kraus_map_norm_id_le: \<open>kraus_map_norm kraus_map_id \<le> 1\<close>
  apply (simp add: kraus_map_id_def)
  apply transfer
  by (auto intro!: power_le_one onorm_pos_le onorm_id_le)

lemma kraus_map_norm_id[simp]: \<open>kraus_map_norm (kraus_map_id :: ('a :: {chilbert_space, not_singleton},'a) kraus_map) = 1\<close>
  by (auto intro!: antisym kraus_map_norm_id_le simp: kraus_map_id_def)

definition kraus_family_plus :: \<open>('a,'b,'x) kraus_family \<Rightarrow> ('a,'b,'y) kraus_family \<Rightarrow> ('a,'b,'x+'y) kraus_family\<close> where
  \<open>kraus_family_plus \<EE> \<FF> = (\<lambda>(E,x). (E, Inl x)) ` \<EE> \<union> (\<lambda>(F,y). (F, Inr y)) ` \<FF>\<close>

lemma kraus_family_plus:
  assumes \<open>kraus_family \<EE>\<close>
  assumes \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family (kraus_family_plus \<EE> \<FF>)\<close>
  using assms
  by (auto intro!: summable_on_Un_disjoint 
      summable_on_reindex[THEN iffD2] inj_onI
      simp: kraus_family_def2' kraus_family_plus_def o_def case_prod_unfold conj_commute)


lemma kraus_family_map_plus:
  fixes \<EE> :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space \<times> 'x) set\<close>
    and \<FF> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'y) set\<close>
  assumes \<open>kraus_family \<EE>\<close>
  assumes \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family_map (kraus_family_plus \<EE> \<FF>) \<rho> = kraus_family_map \<EE> \<rho> + kraus_family_map \<FF> \<rho>\<close>
proof -
  have \<open>kraus_family_map (kraus_family_plus \<EE> \<FF>) \<rho> = 
    (\<Sum>\<^sub>\<infinity>EF\<in>(\<lambda>(E,x). (E, Inl x)) ` \<EE> \<union> (\<lambda>(F,y). (F, Inr y)) ` \<FF>. sandwich_tc (fst EF) \<rho>)\<close>
    by (simp add: kraus_family_plus_def kraus_family_map_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>EF\<in>(\<lambda>(E,x). (E, Inl x :: 'x+'y)) ` \<EE>. sandwich_tc (fst EF) \<rho>)
                + (\<Sum>\<^sub>\<infinity>EF\<in>(\<lambda>(F,y). (F, Inr y :: 'x+'y)) ` \<FF>. sandwich_tc (fst EF) \<rho>)\<close>
    apply (subst infsum_Un_disjoint)
    using assms kraus_family_map_summable
    by (auto intro!: summable_on_reindex[THEN iffD2] inj_onI
        simp: o_def case_prod_unfold kraus_family_map_summable)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>) + (\<Sum>\<^sub>\<infinity>F\<in>\<FF>. sandwich_tc (fst F) \<rho>)\<close>
    apply (subst infsum_reindex)
     apply (auto intro!: inj_onI)[1]
    apply (subst infsum_reindex)
     apply (auto intro!: inj_onI)[1]
    by (simp add:  o_def case_prod_unfold)
  also have \<open>\<dots> = kraus_family_map \<EE> \<rho> + kraus_family_map \<FF> \<rho>\<close>
    by (simp add: kraus_family_map_def)
  finally show ?thesis
    by -
qed

definition kraus_family_scale :: \<open>real \<Rightarrow> ('a::chilbert_space,'b::chilbert_space,'x) kraus_family \<Rightarrow> ('a,'b,'x) kraus_family\<close> where
  \<open>kraus_family_scale r \<EE> = (if r \<le> 0 then {} else (\<lambda>(E,x). (sqrt r *\<^sub>R E, x)) ` \<EE>)\<close>

(* lemma kraus_family_scale_neg: \<open>kraus_family_scale r = {}\<close> if \<open>r \<le> 0\<close>
  using that by (auto intro!: ext simp add: kraus_family_scale_def) *)

lemma kraus_family_kraus_family_scale:
  assumes kraus\<EE>: \<open>kraus_family \<EE>\<close>
  shows \<open>kraus_family (kraus_family_scale r \<EE>)\<close>
proof (cases \<open>r > 0\<close>)
  case True
  from assms
  obtain B where B: \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>M \<subseteq> \<EE>\<close> and \<open>finite M\<close> for M
    by (auto intro!: simp: kraus_family_def bdd_above_def)
  have \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R B\<close> if Mr\<EE>: \<open>M \<subseteq> kraus_family_scale r \<EE>\<close> and \<open>finite M\<close> for M
  proof -
    define M' where \<open>M' = (\<lambda>(E,x). (E /\<^sub>R sqrt r, x)) ` M\<close>
    then have \<open>finite M'\<close>
      using that(2) by blast
    moreover have \<open>M' \<subseteq> \<EE>\<close>
      using Mr\<EE> True by (auto intro!: simp: M'_def kraus_family_scale_def)
    ultimately have 1: \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M'. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
      using B by auto
    have 2: \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) = r *\<^sub>R (\<Sum>\<^sub>\<infinity>(E,x)\<in>M'. E* o\<^sub>C\<^sub>L E)\<close>
      apply (simp add: M'_def case_prod_unfold)
      apply (subst infsum_reindex)
      using True
      by (auto intro!: inj_onI simp: o_def infsum_scaleR_right
          simp flip: inverse_mult_distrib)

    show ?thesis
      using 1 2 True
      apply auto
      using True scaleR_le_cancel_left_pos by blast
  qed
  then show ?thesis
    by (auto intro!: simp: kraus_family_def bdd_above_def)
next
  case False
  then show ?thesis
    by (simp add: kraus_family_scale_def)
qed

lemma kraus_family_scale_map:
  assumes \<open>r \<ge> 0\<close>
  shows \<open>kraus_family_map (kraus_family_scale r \<EE>) \<rho> = r *\<^sub>R kraus_family_map \<EE> \<rho>\<close>
proof (cases \<open>r > 0\<close>)
  case True
  then show ?thesis
    apply (simp add: kraus_family_scale_def kraus_family_map_def)
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI
        simp: kraus_family_scale_def kraus_family_map_def case_prod_unfold
        o_def sandwich_tc_scaleR_left cblinfun.scaleR_left infsum_scaleR_right)
next
  case False
  with assms show ?thesis
    by (simp add: kraus_family_scale_def)
qed

instantiation kraus_map :: (chilbert_space, chilbert_space) \<open>{zero,plus,scaleR}\<close> begin
lift_definition zero_kraus_map :: \<open>('a,'b) kraus_map\<close> is \<open>{}\<close>
  by (simp add: kraus_equivalent_def)
lift_definition plus_kraus_map :: \<open>('a,'b) kraus_map \<Rightarrow> ('a,'b) kraus_map \<Rightarrow> ('a,'b) kraus_map\<close> is
  \<open>\<lambda>\<EE> \<FF>. kraus_family_flatten (kraus_family_plus \<EE> \<FF>)\<close>
  by (auto intro!: kraus_family_kraus_family_comp kraus_family_kraus_family_flatten
      simp add: kraus_family_map_plus kraus_family_plus kraus_equivalent_def kraus_family_comp_apply kraus_family_flatten_same_map kraus_family_kraus_family_comp)
lift_definition scaleR_kraus_map :: \<open>real \<Rightarrow> ('a,'b) kraus_map \<Rightarrow> ('a,'b) kraus_map\<close> is
  kraus_family_scale
proof (unfold kraus_equivalent_def, intro conjI kraus_family_kraus_family_scale)
  fix r :: real and \<EE> \<FF> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> unit) set\<close>
  assume \<open>kraus_family \<EE> \<and> kraus_family \<FF> \<and> kraus_family_map \<EE> = kraus_family_map \<FF>\<close>
  then show \<open>kraus_family_map (kraus_family_scale r \<EE>) = kraus_family_map (kraus_family_scale r \<FF>)\<close>
    apply (cases \<open>r < 0\<close>)
     apply (simp add: kraus_family_scale_def)
    by (auto intro!: ext simp: kraus_family_scale_map)
qed auto
instance..
end

instantiation kraus_map :: (chilbert_space, chilbert_space) comm_monoid_add begin
instance
proof intro_classes
  fix a b c :: \<open>('a, 'b) kraus_map\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer
    by (auto intro!: ext
        simp add: kraus_equivalent_def kraus_family_flatten_same_map kraus_family_plus  kraus_family_kraus_family_flatten
        kraus_family_map_plus)
  show \<open>a + b = b + a\<close>
    apply transfer
    by (auto intro!: ext
        simp add: kraus_equivalent_def kraus_family_flatten_same_map kraus_family_plus  kraus_family_kraus_family_flatten
        kraus_family_map_plus)
  show \<open>0 + a = a\<close>
    apply transfer
    by (auto intro!: ext
        simp add: kraus_equivalent_def kraus_family_flatten_same_map kraus_family_plus  kraus_family_kraus_family_flatten
        kraus_family_map_plus)
qed
end


lift_definition kraus_map_apply :: \<open>('a::chilbert_space,'b::chilbert_space) kraus_map \<Rightarrow> ('a,'a) trace_class \<Rightarrow> ('b,'b) trace_class\<close> is
  \<open>kraus_family_map\<close>
  by (auto simp: kraus_equivalent_def)

lemma kraus_map_apply_bounded_clinear[bounded_clinear]:
  \<open>bounded_clinear (kraus_map_apply \<EE>)\<close>
  apply transfer
  using kraus_equivalent_def kraus_family_map_bounded_clinear by blast

lemma kraus_family_of_op_apply: \<open>kraus_family_map (kraus_family_of_op E) \<rho> = sandwich_tc E \<rho>\<close>
  by (simp add: kraus_family_map_def kraus_family_of_op_def)


lemma kraus_map_of_op_apply: \<open>kraus_map_apply (kraus_map_of_op E) \<rho> = sandwich_tc E \<rho>\<close>
  apply (transfer' fixing: \<rho>)
  by (simp add: kraus_family_of_op_apply)

lemma kraus_map_id_apply[simp]: \<open>kraus_map_apply kraus_map_id \<rho> = \<rho>\<close>
  by (simp add: kraus_map_id_def kraus_map_of_op_apply)

lemma kraus_family_rep_kraus_map[simp]: \<open>kraus_family (rep_kraus_map \<EE>)\<close>
  using Quotient_rep_reflp[OF Quotient_kraus_map]
  by (auto simp add: kraus_equivalent_def)

lemma kraus_map_scaleR:
  assumes \<open>r \<ge> 0\<close>
  shows \<open>kraus_map_apply (r *\<^sub>R \<EE>) \<rho> = r *\<^sub>R kraus_map_apply \<EE> \<rho>\<close>
proof -
  have \<open>kraus_map_apply (r *\<^sub>R \<EE>) \<rho> = kraus_family_map (kraus_family_scale r (rep_kraus_map \<EE>)) \<rho>\<close>
    by (simp add: scaleR_kraus_map_def kraus_map_apply.abs_eq kraus_equivalent_reflI kraus_family_kraus_family_scale)
  also have \<open>\<dots> = r *\<^sub>R kraus_family_map (rep_kraus_map \<EE>) \<rho>\<close>
    by (simp add: kraus_family_scale_map assms)
  also have \<open>\<dots> = r *\<^sub>R kraus_map_apply \<EE> \<rho>\<close>
    by (simp flip: kraus_map_apply.rep_eq add: cblinfun.scaleR_left)
  finally show \<open>kraus_map_apply (r *\<^sub>R \<EE>) \<rho> = r *\<^sub>R kraus_map_apply \<EE> \<rho>\<close>
    by -
qed

lemma kraus_map_scaleR_neg:
  assumes \<open>r \<le> 0\<close>
  shows \<open>kraus_map_apply (r *\<^sub>R \<EE>) = 0\<close>
  apply (transfer fixing: r)
  using assms
  by (auto intro!: ext simp: kraus_family_scale_def kraus_family_map_def)

lemma kraus_map_norm_0[simp]: \<open>kraus_map_norm 0 = 0\<close>
  apply transfer
  by (auto intro!: simp: kraus_family_norm_def kraus_family_bound_def infsum_in_finite)

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

lemma dist_kraus_map_bdd: \<open>bdd_above (range (\<lambda>\<rho>. dist (kraus_map_apply x \<rho>) (kraus_map_apply y \<rho>) / norm \<rho>))\<close>
proof (rule bdd_aboveI)
  fix r
  assume \<open>r \<in> range (\<lambda>\<rho>. dist (kraus_map_apply x \<rho>) (kraus_map_apply y \<rho>) / norm \<rho>)\<close>
  then obtain \<rho> where r_\<rho>: \<open>r = dist (kraus_map_apply x \<rho>) (kraus_map_apply y \<rho>) / norm \<rho>\<close>
    by auto
  have \<open>dist (kraus_map_apply x \<rho>) (kraus_map_apply y \<rho>) \<le> 
        norm (kraus_map_apply x \<rho>) + norm (kraus_map_apply y \<rho>)\<close>
    by (metis dist_0_norm dist_triangle3)
  also have \<open>\<dots> \<le> 4 * kraus_map_norm x * norm \<rho> + 4 * kraus_map_norm y * norm \<rho>\<close>
    by (auto intro!: add_mono norm_kraus_map_apply)
  also have \<open>\<dots> \<le> (4 * kraus_map_norm x + 4 * kraus_map_norm y) * norm \<rho>\<close>
    by (simp add: cross3_simps(23))
  finally show \<open>r \<le> 4 * kraus_map_norm x + 4 * kraus_map_norm y\<close>
    apply (cases \<open>norm \<rho> = 0\<close>)
    by (auto simp: r_\<rho> linordered_field_class.pos_divide_le_eq)
qed

lemma kraus_map_apply_0_left[iff]: \<open>kraus_map_apply 0 \<rho> = 0\<close>
proof -
  have \<open>kraus_map_apply 0 \<rho> = x\<close> if \<open>x = 0\<close> for x
    apply (transfer fixing: \<rho> x)
    by (simp add: that)
  then show ?thesis
    by simp
qed

lemma kraus_map_apply_0_right[iff]: \<open>kraus_map_apply \<EE> 0 = 0\<close>
  by (intro Linear_Algebra.linear_simps bounded_clinear.bounded_linear kraus_map_apply_bounded_clinear)


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
    have \<open>dist (kraus_map_apply x \<rho>) (kraus_map_apply y \<rho>) / norm \<rho> \<le> 0\<close> for \<rho>
      by (auto intro!: cSUP_upper dist_kraus_map_bdd simp: dist_kraus_map_def simp flip: dist_0)
    then have \<open>dist (kraus_map_apply x \<rho>) (kraus_map_apply y \<rho>) = 0\<close> for \<rho>
      apply (cases \<open>norm \<rho> = 0\<close>)
      apply simp
      using order_antisym by fastforce
    then have \<open>kraus_map_apply x \<rho> = kraus_map_apply y \<rho>\<close> for \<rho>
      by simp
    then have \<open>kraus_map_apply x = kraus_map_apply y\<close>
      by blast
    then show \<open>x = y\<close>
      by (simp add: kraus_map_apply_inj)
  qed
  show \<open>dist x y \<le> dist x z + dist y z\<close>
  proof (unfold dist_kraus_map_def, rule cSUP_least)
    show \<open>UNIV \<noteq> {}\<close> by simp
    fix \<rho>
    have \<open>dist (kraus_map_apply x \<rho>) (kraus_map_apply y \<rho>) / norm \<rho>
            \<le> (dist (kraus_map_apply x \<rho>) (kraus_map_apply z \<rho>) +
                dist (kraus_map_apply y \<rho>) (kraus_map_apply z \<rho>)) / norm \<rho>\<close>
      apply (rule divide_right_mono)
      using dist_triangle2 by auto
    also have \<open>\<dots> = dist (kraus_map_apply x \<rho>) (kraus_map_apply z \<rho>) / norm \<rho> +
                    dist (kraus_map_apply y \<rho>) (kraus_map_apply z \<rho>) / norm \<rho>\<close>
      by (simp add: add_divide_distrib)
    also have \<open>\<dots> \<le> (\<Squnion>\<rho>. dist (kraus_map_apply x \<rho>) (kraus_map_apply z \<rho>) / norm \<rho>) +
                  (\<Squnion>\<rho>. dist (kraus_map_apply y \<rho>) (kraus_map_apply z \<rho>) / norm \<rho>)\<close>
      by (auto intro!: add_mono cSUP_upper2 dist_kraus_map_bdd)
    finally show \<open>dist (kraus_map_apply x \<rho>) (kraus_map_apply y \<rho>) / norm \<rho> \<le> \<dots>\<close>
      by -
  qed
qed
end

lemma kraus_map_apply_comp: \<open>kraus_map_apply (kraus_map_comp E F) = kraus_map_apply E o kraus_map_apply F\<close>
  apply transfer
  by (simp add: kraus_family_kraus_family_comp kraus_equivalent_def kraus_family_flatten_same_map
      kraus_family_comp_apply)

lemma kraus_map_comp_assoc: \<open>kraus_map_comp (kraus_map_comp E F) G = kraus_map_comp E (kraus_map_comp F G)\<close>
  apply (rule kraus_map_apply_inj)
  by (simp add: kraus_map_apply_comp o_def)

(* (* TODO move *)
lift_definition tc_tensor :: \<open>('a ell2, 'b ell2) trace_class \<Rightarrow> ('c ell2, 'd ell2) trace_class \<Rightarrow> 
      (('a \<times> 'c) ell2, ('b \<times> 'd) ell2) trace_class\<close> is
  tensor_op
  by (auto intro!: trace_class_tensor) *)


(* (* TODO move *)
lemma tc_tensor_scaleC_left: \<open>tc_tensor (c *\<^sub>C a) b = c *\<^sub>C tc_tensor a b\<close>
  apply transfer'
  by (simp add: tensor_op_scaleC_left)
lemma tc_tensor_scaleC_right: \<open>tc_tensor a (c *\<^sub>C b) = c *\<^sub>C tc_tensor a b\<close>
  apply transfer'
  by (simp add: tensor_op_scaleC_right) *)
  
(* (* TODO move *)
lemma comp_tc_tensor: \<open>tc_compose (tc_tensor a b) (tc_tensor c d) = tc_tensor (tc_compose a c) (tc_compose b d)\<close>
  apply transfer'
  by (rule comp_tensor_op) *)

(* (* TODO move *)
lift_definition tc_butterfly :: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space \<Rightarrow> ('b,'a) trace_class\<close>
  is butterfly
  by simp *)

(* (* TODO move *)
lemma norm_tc_butterfly: \<open>norm (tc_butterfly \<psi> \<phi>) = norm \<psi> * norm \<phi>\<close>
  apply (transfer fixing: \<psi> \<phi>)
  by (simp add: trace_norm_butterfly) *)

(* (* TODO move *)
lemma norm_tc_tensor: \<open>norm (tc_tensor a b) = norm a * norm b\<close>
  apply transfer'
  apply (rule of_real_hom.injectivity[where 'a=complex])
  by (simp add: abs_op_tensor trace_tensor flip: trace_abs_op)
 *)

(* lemma comp_tc_butterfly[simp]: \<open>tc_compose (tc_butterfly a b) (tc_butterfly c d) = (b \<bullet>\<^sub>C c) *\<^sub>C tc_butterfly a d\<close>
  apply transfer'
  by simp *)

(* lemma cspan_trace_class_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_trace_class ===> rel_set cr_trace_class) cspan cspan\<close>
  by - *)

definition trace_kraus_family :: \<open>'a set \<Rightarrow> ('a::chilbert_space, 'b::one_dim, 'a) kraus_family\<close> where
  \<open>trace_kraus_family B = (\<lambda>x. (vector_to_cblinfun x*, x)) ` B\<close>

lemma trace_kraus_family_is_kraus_family: \<open>kraus_family (trace_kraus_family B)\<close> if \<open>is_onb B\<close>
proof -
  have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> id_cblinfun\<close> if \<open>finite F\<close> and FB: \<open>F \<subseteq> trace_kraus_family B\<close> for F :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'a) set\<close>
  proof -
    obtain G where \<open>finite G\<close> and \<open>G \<subseteq> B\<close> and FG: \<open>F = (\<lambda>x. (vector_to_cblinfun x*, x)) ` G\<close>
      apply atomize_elim
      using \<open>finite F\<close> and FB
      apply (simp add: trace_kraus_family_def)
      by (meson finite_subset_image)
    from \<open>G \<subseteq> B\<close> have [simp]: \<open>is_ortho_set G\<close>
      by (meson \<open>is_onb B\<close> is_onb_def is_ortho_set_antimono)
    from \<open>G \<subseteq> B\<close> have [simp]: \<open>e \<in> G \<Longrightarrow> norm e = 1\<close> for e
      by (meson Set.basic_monos(7) \<open>is_onb B\<close> is_onb_def)
    have [simp]: \<open>inj_on (\<lambda>x. (vector_to_cblinfun x*, x)) G\<close>
      by (meson inj_onI prod.inject)
    have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) = (\<Sum>x\<in>G. selfbutter x)\<close>
      by (simp add: FG sum.reindex flip: butterfly_def_one_dim)
    also have \<open>(\<Sum>x\<in>G. selfbutter x) \<le> id_cblinfun\<close>
      apply (rule sum_butterfly_leq_id)
      by auto
    finally show ?thesis
      by -
  qed
  then show ?thesis
    by (auto intro!: bdd_aboveI[where M=id_cblinfun] kraus_familyI)
qed


lemma trace_kraus_family_is_trace: 
  assumes \<open>is_onb B\<close>
  shows \<open>kraus_family_map (trace_kraus_family B) \<rho> = one_dim_iso (trace_tc \<rho>)\<close>
proof -
  define \<rho>' where \<open>\<rho>' = from_trace_class \<rho>\<close>
  have \<open>kraus_family_map (trace_kraus_family B) \<rho> = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (vector_to_cblinfun x*) \<rho>)\<close>
    apply (simp add: kraus_family_map_def trace_kraus_family_def)
    apply (subst infsum_reindex)
     apply (meson inj_onI prod.simps(1))
    by (simp add: o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B. one_dim_iso (x \<bullet>\<^sub>C (\<rho>' x)))\<close>
    apply (intro infsum_cong from_trace_class_inject[THEN iffD1])
    apply (subst from_trace_class_sandwich_tc)
    by (simp add: sandwich_apply flip: \<rho>'_def)
  also have \<open>\<dots> = one_dim_iso (\<Sum>\<^sub>\<infinity>x\<in>B. (x \<bullet>\<^sub>C (\<rho>' x)))\<close>
    by (metis (mono_tags, lifting) \<rho>'_def infsum_cblinfun_apply infsum_cong assms one_cblinfun.rep_eq trace_class_from_trace_class trace_exists)
  also have \<open>\<dots> = one_dim_iso (trace \<rho>')\<close>
    by (metis \<rho>'_def trace_class_from_trace_class trace_alt_def[OF assms])
  also have \<open>\<dots> = one_dim_iso (trace_tc \<rho>)\<close>
    by (simp add: \<rho>'_def trace_tc.rep_eq)
  finally show ?thesis
    by -
qed

lemma kraus_equivalent_trace_kraus_family:
  assumes \<open>is_onb A\<close> and \<open>is_onb B\<close>
  shows \<open>kraus_equivalent (trace_kraus_family A) (trace_kraus_family B)\<close>
  by (auto intro!: trace_kraus_family_is_kraus_family
      simp: kraus_equivalent_def trace_kraus_family_is_trace assms)


lift_definition trace_kraus_map :: \<open>('a::chilbert_space, 'b::one_dim) kraus_map\<close> is
  \<open>kraus_family_flatten (trace_kraus_family some_chilbert_basis)\<close>
  by (simp add: kraus_equivalent_reflI kraus_family_kraus_family_flatten trace_kraus_family_is_kraus_family)

lemma trace_kraus_map_is_trace: \<open>kraus_map_apply trace_kraus_map \<rho> = one_dim_iso (trace_tc \<rho>)\<close>
  apply (transfer' fixing: \<rho>)
  by (simp add: kraus_family_flatten_same_map trace_kraus_family_is_kraus_family trace_kraus_family_is_trace)

definition \<open>trace_preserving \<EE> \<longleftrightarrow> (\<forall>\<rho>. trace_tc (kraus_map_apply \<EE> \<rho>) = trace_tc \<rho>)\<close>

(* lemma \<open>kraus_map_norm \<EE> \<le> 1\<close> if \<open>trace_preserving \<EE>\<close>
by -

lemma \<open>kraus_map_norm \<EE> = 1\<close> if \<open>trace_preserving \<EE>\<close> 
  for \<EE> :: \<open>('a::{not_singleton, chilbert_space}, 'b::chilbert_space) kraus_map\<close>
by - *)

lemma trace_preserving_id[iff]: \<open>trace_preserving kraus_map_id\<close>
  by (simp add: trace_preserving_def trace_kraus_map_is_trace)


lemma trace_preserving_trace_kraus_map[iff]: \<open>trace_preserving trace_kraus_map\<close>
  by (simp add: trace_preserving_def trace_kraus_map_is_trace)


lemma kraus_equivalent_kraus_family_flatten_left: \<open>kraus_equivalent (kraus_family_flatten F) G\<close> if \<open>kraus_equivalent F G\<close>
  using that by (simp add: kraus_equivalent_def kraus_family_flatten_same_map kraus_family_kraus_family_flatten)
lemma kraus_equivalent_kraus_family_flatten_right: \<open>kraus_equivalent F (kraus_family_flatten G)\<close> if \<open>kraus_equivalent F G\<close>
  using that by (simp add: kraus_equivalent_def kraus_family_flatten_same_map kraus_family_kraus_family_flatten)

lemma kraus_family_comp_cong: \<open>kraus_equivalent (kraus_family_comp F G) (kraus_family_comp F' G')\<close>
  if \<open>kraus_equivalent F F'\<close> and \<open>kraus_equivalent G G'\<close>
  by (metis kraus_equivalent_def kraus_family_comp_apply kraus_family_kraus_family_comp that(1) that(2))

lemma kraus_equivalent_trans[trans]:
  \<open>kraus_equivalent F G \<Longrightarrow> kraus_equivalent G H \<Longrightarrow> kraus_equivalent F H\<close>
  by (simp add: kraus_equivalent_def)

definition kraus_family_tensor :: \<open>('a ell2, 'b ell2, 'x) kraus_family \<Rightarrow> ('c ell2, 'd ell2, 'y) kraus_family \<Rightarrow> (('a\<times>'c) ell2, ('b\<times>'d) ell2, (_\<times>_\<times>'x\<times>'y)) kraus_family\<close> where
  \<open>kraus_family_tensor \<EE> \<FF> = (\<lambda>((E,x), (F,y)). (E \<otimes>\<^sub>o F, (E,F,x,y))) ` (\<EE>\<times>\<FF>)\<close>

lemma tc_butterfly_add_left: \<open>tc_butterfly (a + a') b = tc_butterfly a b + tc_butterfly a' b\<close>
  apply transfer
  by (rule butterfly_add_left)

lemma tc_butterfly_add_right: \<open>tc_butterfly a (b + b') = tc_butterfly a b + tc_butterfly a b'\<close>
  apply transfer
  by (rule butterfly_add_right)

lemma tc_butterfly_sum_left: \<open>tc_butterfly (\<Sum>i\<in>M. \<psi> i) \<phi> = (\<Sum>i\<in>M. tc_butterfly (\<psi> i) \<phi>)\<close>
  apply transfer
  by (rule butterfly_sum_left)

lemma tc_butterfly_sum_right: \<open>tc_butterfly \<psi> (\<Sum>i\<in>M. \<phi> i) = (\<Sum>i\<in>M. tc_butterfly \<psi> (\<phi> i))\<close>
  apply transfer
  by (rule butterfly_sum_right)

lemma tc_butterfly_scaleC_left[simp]: "tc_butterfly (c *\<^sub>C \<psi>) \<phi> = c *\<^sub>C tc_butterfly \<psi> \<phi>"
  apply transfer by simp

lemma tc_butterfly_scaleC_right[simp]: "tc_butterfly \<psi> (c *\<^sub>C \<phi>) = cnj c *\<^sub>C tc_butterfly \<psi> \<phi>"
  apply transfer by simp

lemma onb_butterflies_span_trace_class:
  fixes A :: \<open>'a::chilbert_space set\<close> and B :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_onb A\<close> and \<open>is_onb B\<close>
  shows \<open>ccspan ((\<lambda>(x, y). tc_butterfly x y) ` (A\<times>B)) = \<top>\<close>
proof -
  have \<open>closure (cspan ((\<lambda>(x, y). tc_butterfly x y) ` (A\<times>B))) \<supseteq> Collect rank1_tc\<close>
  proof (rule subsetI)
    \<comment> \<open>This subproof is almost identical to the corresponding one in
        @{thm [source] finite_rank_dense_compact}, and lengthy. Can they be merged into one subproof?\<close>
    fix x :: \<open>('b, 'a) trace_class\<close> assume \<open>x \<in> Collect rank1_tc\<close>
    then obtain a b where xab: \<open>x = tc_butterfly a b\<close>
      apply transfer using rank1_iff_butterfly by fastforce
    define f where \<open>f F G = tc_butterfly (Proj (ccspan F) a) (Proj (ccspan G) b)\<close> for F G
    have lim: \<open>(case_prod f \<longlongrightarrow> x) (finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B)\<close>
    proof (rule tendstoI, subst dist_norm)
      fix e :: real assume \<open>e > 0\<close>
      define d where \<open>d = (if norm a = 0 \<and> norm b = 0 then 1 
                                  else e / (max (norm a) (norm b)) / 4)\<close>
      have d: \<open>norm a * d + norm a * d + norm b * d < e\<close>
      proof -
        have \<open>norm a * d \<le> e/4\<close>
          using \<open>e > 0\<close> apply (auto simp: d_def)
           apply (simp add: divide_le_eq)
          by (smt (z3) Extra_Ordered_Fields.mult_sign_intros(3) \<open>0 < e\<close> antisym_conv divide_le_eq less_imp_le linordered_field_class.mult_imp_div_pos_le mult_left_mono nice_ordered_field_class.dense_le nice_ordered_field_class.divide_nonneg_neg nice_ordered_field_class.divide_nonpos_pos nle_le nonzero_mult_div_cancel_left norm_imp_pos_and_ge ordered_field_class.sign_simps(5) split_mult_pos_le)
        moreover have \<open>norm b * d \<le> e/4\<close>
          using \<open>e > 0\<close> apply (auto simp: d_def)
           apply (simp add: divide_le_eq)
          by (smt (verit) linordered_field_class.mult_imp_div_pos_le mult_left_mono norm_le_zero_iff ordered_field_class.sign_simps(5))
        ultimately have \<open>norm a * d + norm a * d + norm b * d \<le> 3 * e / 4\<close>
          by linarith
        also have \<open>\<dots> < e\<close>
          by (simp add: \<open>0 < e\<close>)
        finally show ?thesis
          by -
      qed
      have [simp]: \<open>d > 0\<close>
        using \<open>e > 0\<close> apply (auto simp: d_def)
         apply (smt (verit, best) nice_ordered_field_class.divide_pos_pos norm_eq_zero norm_not_less_zero)
        by (smt (verit) linordered_field_class.divide_pos_pos zero_less_norm_iff)
      from Proj_onb_limit[where \<psi>=a, OF assms(1)]
      have \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. norm (Proj (ccspan F) a - a) < d\<close>
        by (metis Lim_null \<open>0 < d\<close> order_tendstoD(2) tendsto_norm_zero_iff)
      moreover from Proj_onb_limit[where \<psi>=b, OF assms(2)]
      have \<open>\<forall>\<^sub>F G in finite_subsets_at_top B. norm (Proj (ccspan G) b - b) < d\<close>
        by (metis Lim_null \<open>0 < d\<close> order_tendstoD(2) tendsto_norm_zero_iff)
      ultimately have FG_close: \<open>\<forall>\<^sub>F (F,G) in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B. 
              norm (Proj (ccspan F) a - a) < d \<and> norm (Proj (ccspan G) b - b) < d\<close>
        unfolding case_prod_beta
        by (rule eventually_prodI)
      have fFG_dist: \<open>norm (f F G - x) < e\<close> 
        if \<open>norm (Proj (ccspan F) a - a) < d\<close> and \<open>norm (Proj (ccspan G) b - b) < d\<close>
          and \<open>F \<subseteq> A\<close> and \<open>G \<subseteq> B\<close> for F G
      proof -
        have a_split: \<open>a = Proj (ccspan F) a + Proj (ccspan (A-F)) a\<close>
          using assms apply (simp add: is_onb_def is_ortho_set_def that Proj_orthog_ccspan_union flip: cblinfun.add_left)
          apply (subst Proj_orthog_ccspan_union[symmetric])
           apply (metis DiffD1 DiffD2 in_mono that(3))
          using \<open>F \<subseteq> A\<close> by (auto intro!: simp: Un_absorb1)
        have b_split: \<open>b = Proj (ccspan G) b + Proj (ccspan (B-G)) b\<close>
          using assms apply (simp add: is_onb_def is_ortho_set_def that Proj_orthog_ccspan_union flip: cblinfun.add_left)
          apply (subst Proj_orthog_ccspan_union[symmetric])
           apply (metis DiffD1 DiffD2 in_mono that(4))
          using \<open>G \<subseteq> B\<close> by (auto intro!: simp: Un_absorb1)
        have n1: \<open>norm (f F (B-G)) \<le> norm a * d\<close> for F
        proof -
          have \<open>norm (f F (B-G)) \<le> norm a * norm (Proj (ccspan (B-G)) b)\<close>
            by (auto intro!: mult_right_mono is_Proj_reduces_norm simp add: f_def norm_tc_butterfly)
          also have \<open>\<dots> \<le> norm a * norm (Proj (ccspan G) b - b)\<close>
            by (metis add_diff_cancel_left' b_split less_eq_real_def norm_minus_commute)
          also have \<open>\<dots> \<le> norm a * d\<close>
            by (meson less_eq_real_def mult_left_mono norm_ge_zero that(2))
          finally show ?thesis
            by -
        qed
        have n2: \<open>norm (f (A-F) G) \<le> norm b * d\<close> for G
        proof -
          have \<open>norm (f (A-F) G) \<le> norm b * norm (Proj (ccspan (A-F)) a)\<close>
            by (auto intro!: mult_right_mono is_Proj_reduces_norm simp add: f_def norm_tc_butterfly mult.commute)
          also have \<open>\<dots> \<le> norm b * norm (Proj (ccspan F) a - a)\<close>
            by (smt (verit, best) a_split add_diff_cancel_left' minus_diff_eq norm_minus_cancel)
          also have \<open>\<dots> \<le> norm b * d\<close>
            by (meson less_eq_real_def mult_left_mono norm_ge_zero that(1))
          finally show ?thesis
            by -
        qed
        have \<open>norm (f F G - x) = norm (- f F (B-G) - f (A-F) (B-G) - f (A-F) G)\<close>
          unfolding xab
          apply (subst a_split, subst b_split)
          by (simp add: f_def tc_butterfly_add_right tc_butterfly_add_left)
        also have \<open>\<dots> \<le> norm (f F (B-G)) + norm (f (A-F) (B-G)) + norm (f (A-F) G)\<close>
          by (smt (verit, best) norm_minus_cancel norm_triangle_ineq4)
        also have \<open>\<dots> \<le> norm a * d + norm a * d + norm b * d\<close>
          using n1 n2
          by (meson add_mono_thms_linordered_semiring(1))
        also have \<open>\<dots> < e\<close>
          by (fact d)
        finally show ?thesis
          by -
      qed
      show \<open>\<forall>\<^sub>F FG in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B. norm (case_prod f FG - x) < e\<close>
        apply (rule eventually_elim2)
          apply (rule eventually_prodI[where P=\<open>\<lambda>F. finite F \<and> F \<subseteq> A\<close> and Q=\<open>\<lambda>G. finite G \<and> G \<subseteq> B\<close>])
           apply auto[2]
         apply (rule FG_close)
        using fFG_dist by fastforce
    qed
    have nontriv: \<open>finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B \<noteq> \<bottom>\<close>
      by (simp add: prod_filter_eq_bot)
    have inside: \<open>\<forall>\<^sub>F x in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B. 
              case_prod f x \<in> cspan ((\<lambda>(\<xi>,\<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))\<close>
    proof (rule eventually_mp[where P=\<open>\<lambda>(F,G). finite F \<and> finite G\<close>])
      show \<open>\<forall>\<^sub>F (F,G) in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B. finite F \<and> finite G\<close>
        by (smt (verit) case_prod_conv eventually_finite_subsets_at_top_weakI eventually_prod_filter)
      have f_in_span: \<open>f F G \<in> cspan ((\<lambda>(\<xi>,\<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))\<close> if [simp]: \<open>finite F\<close> \<open>finite G\<close> and \<open>F \<subseteq> A\<close> \<open>G \<subseteq> B\<close> for F G
      proof -
        have \<open>Proj (ccspan F) a \<in> cspan F\<close>
          by (metis Proj_range cblinfun_apply_in_image ccspan_finite that(1))
        then obtain r where ProjFsum: \<open>Proj (ccspan F) a = (\<Sum>x\<in>F. r x *\<^sub>C x)\<close>
          apply atomize_elim
          using complex_vector.span_finite[OF \<open>finite F\<close>]
          by auto
        have \<open>Proj (ccspan G) b \<in> cspan G\<close>
          by (metis Proj_range cblinfun_apply_in_image ccspan_finite that(2))
        then obtain s where ProjGsum: \<open>Proj (ccspan G) b = (\<Sum>x\<in>G. s x *\<^sub>C x)\<close>
          apply atomize_elim
          using complex_vector.span_finite[OF \<open>finite G\<close>]
          by auto
        have \<open>tc_butterfly \<xi> \<eta> \<in> (\<lambda>(\<xi>, \<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B)\<close>
          if \<open>\<eta> \<in> G\<close> and \<open>\<xi> \<in> F\<close> for \<eta> \<xi>
          using \<open>F \<subseteq> A\<close> \<open>G \<subseteq> B\<close> that by (auto intro!: pair_imageI)
        then show ?thesis
          by (auto intro!: complex_vector.span_sum complex_vector.span_scale
              intro: complex_vector.span_base[where a=\<open>tc_butterfly _ _\<close>]
              simp add: f_def ProjFsum ProjGsum tc_butterfly_sum_left tc_butterfly_sum_right)
      qed
      show \<open>\<forall>\<^sub>F x in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B.
                      (case x of (F, G) \<Rightarrow> finite F \<and> finite G) \<longrightarrow> (case x of (F, G) \<Rightarrow> f F G) \<in> cspan ((\<lambda>(\<xi>, \<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))\<close>
        apply (rule eventually_mono)
        apply (rule eventually_prodI[where P=\<open>\<lambda>F. finite F \<and> F \<subseteq> A\<close> and Q=\<open>\<lambda>G. finite G \<and> G \<subseteq> B\<close>])
        by (auto intro!: f_in_span)
    qed
    show \<open>x \<in> closure (cspan ((\<lambda>(\<xi>, \<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B)))\<close>
      using lim nontriv inside by (rule limit_in_closure)
  qed
  moreover have \<open>cspan (Collect rank1_tc :: ('b,'a) trace_class set) = Collect finite_rank_tc\<close>
    using finite_rank_tc_def' by fastforce
  moreover have \<open>closure (Collect finite_rank_tc :: ('b,'a) trace_class set) = UNIV\<close>
    by (rule finite_rank_tc_dense)
  ultimately have \<open>closure (cspan ((\<lambda>(x, y). tc_butterfly x y) ` (A\<times>B))) \<supseteq> UNIV\<close>
    by (smt (verit, del_insts) Un_UNIV_left closed_sum_closure_left closed_sum_cspan closure_closure closure_is_csubspace complex_vector.span_eq_iff complex_vector.subspace_span subset_Un_eq)
  then show ?thesis
    by (metis ccspan.abs_eq ccspan_UNIV closure_UNIV complex_vector.span_UNIV top.extremum_uniqueI)
qed


lemma tensor_op_mono_left:
  fixes a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and c :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  assumes \<open>a \<le> b\<close> and \<open>c \<ge> 0\<close>
  shows \<open>a \<otimes>\<^sub>o c \<le> b \<otimes>\<^sub>o c\<close>
proof -
  have \<open>b - a \<ge> 0\<close>
    by (simp add: assms(1))
  with \<open>c \<ge> 0\<close> have \<open>(b - a) \<otimes>\<^sub>o c \<ge> 0\<close>
    by (intro tensor_op_pos)
  then have \<open>b \<otimes>\<^sub>o c - a \<otimes>\<^sub>o c \<ge> 0\<close>
    by (simp add: tensor_op_cbilinear.diff_left)
  then show ?thesis
    by simp
qed

lemma tensor_op_mono_right:
  fixes a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  assumes \<open>b \<le> c\<close> and \<open>a \<ge> 0\<close>
  shows \<open>a \<otimes>\<^sub>o b \<le> a \<otimes>\<^sub>o c\<close>
proof -
  have \<open>c - b \<ge> 0\<close>
    by (simp add: assms(1))
  with \<open>a \<ge> 0\<close> have \<open>a \<otimes>\<^sub>o (c - b) \<ge> 0\<close>
    by (intro tensor_op_pos)
  then have \<open>a \<otimes>\<^sub>o c - a \<otimes>\<^sub>o b \<ge> 0\<close>
    by (simp add: tensor_op_cbilinear.diff_right)
  then show ?thesis
    by simp
qed


lemma tensor_op_mono:
  fixes a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> and c :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  assumes \<open>a \<le> b\<close> and \<open>c \<le> d\<close> and \<open>b \<ge> 0\<close> and \<open>c \<ge> 0\<close>
  shows \<open>a \<otimes>\<^sub>o c \<le> b \<otimes>\<^sub>o d\<close>
proof -
  have \<open>a \<otimes>\<^sub>o c \<le> b \<otimes>\<^sub>o c\<close>
    using \<open>a \<le> b\<close> and \<open>c \<ge> 0\<close>
    by (rule tensor_op_mono_left)
  also have \<open>\<dots> \<le> b \<otimes>\<^sub>o d\<close>
    using \<open>c \<le> d\<close> and \<open>b \<ge> 0\<close>
    by (rule tensor_op_mono_right)
  finally show ?thesis
    by -
qed

lemma kraus_family_kraus_family_tensor:
  assumes \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family (kraus_family_tensor \<EE> \<FF>)\<close>
proof (intro kraus_familyI)
  from \<open>kraus_family \<EE>\<close>
  obtain B where B: \<open>(\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>finite S\<close> and \<open>S \<subseteq> \<EE>\<close> for S
    using kraus_family_sums_bounded_by_bound by blast
  from B[where S=\<open>{}\<close>] have [simp]: \<open>B \<ge> 0\<close>
    by simp
  from \<open>kraus_family \<FF>\<close>
  obtain C where C: \<open>(\<Sum>(F, x)\<in>T. F* o\<^sub>C\<^sub>L F) \<le> C\<close> if \<open>finite T\<close> and \<open>T \<subseteq> \<FF>\<close> for T
    using kraus_family_sums_bounded_by_bound by blast
  have \<open>(\<Sum>(G, z)\<in>U. G* o\<^sub>C\<^sub>L G) \<le> B \<otimes>\<^sub>o C\<close> if \<open>finite U\<close> and \<open>U \<subseteq> kraus_family_tensor \<EE> \<FF>\<close> for U
  proof -
    define f :: \<open>(('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'c) \<times> 'd ell2 \<Rightarrow>\<^sub>C\<^sub>L 'e ell2 \<times> 'f) \<Rightarrow> _\<close>
      where \<open>f = (\<lambda>((E,x), (F,y)). (E \<otimes>\<^sub>o F, (E,F,x,y)))\<close>
    from that
    obtain V where V_subset: \<open>V \<subseteq> \<EE> \<times> \<FF>\<close> and [simp]: \<open>finite V\<close> and \<open>U = f ` V\<close>
      apply (simp only: kraus_family_tensor_def flip: f_def)
      by (meson finite_subset_image)
    define W where \<open>W = fst ` V \<times> snd ` V\<close>
    have \<open>inj_on f W\<close>
      by (auto intro!: inj_onI simp: f_def)
    from \<open>finite V\<close> have [simp]: \<open>finite W\<close>
      using W_def by blast
    have \<open>W \<supseteq> V\<close>
      by (auto intro!: image_eqI simp: W_def)
    have \<open>(\<Sum>(G, z)\<in>U. G* o\<^sub>C\<^sub>L G) \<le> (\<Sum>(G, z)\<in>f ` W. G* o\<^sub>C\<^sub>L G)\<close>
      using \<open>U = f ` V\<close> \<open>V \<subseteq> W\<close>
      by (auto intro!: sum_mono2 positive_cblinfun_squareI)
    also have \<open>\<dots> = (\<Sum>((E,x),(F,y))\<in>W. (E \<otimes>\<^sub>o F)* o\<^sub>C\<^sub>L (E \<otimes>\<^sub>o F))\<close>
      apply (subst sum.reindex)
      using \<open>inj_on f W\<close>
      by (auto simp: case_prod_unfold f_def)
    also have \<open>\<dots> = (\<Sum>((E,x),(F,y))\<in>W. (E* o\<^sub>C\<^sub>L E) \<otimes>\<^sub>o (F* o\<^sub>C\<^sub>L F))\<close>
      by (simp add: comp_tensor_op tensor_op_adjoint)
    also have \<open>\<dots> = (\<Sum>(E,x)\<in>fst`V. E* o\<^sub>C\<^sub>L E) \<otimes>\<^sub>o (\<Sum>(F,y)\<in>snd`V. F* o\<^sub>C\<^sub>L F)\<close>
      unfolding W_def
      apply (subst sum.Sigma[symmetric])
        apply (auto intro!: simp: case_prod_beta)
      by (metis (mono_tags, lifting) sum.cong tensor_op_cbilinear.sum_left tensor_op_cbilinear.sum_right)
    also have \<open>\<dots> \<le> B \<otimes>\<^sub>o C\<close>
      using V_subset
      by (auto intro!: tensor_op_mono B C sum_nonneg intro: positive_cblinfun_squareI)
    finally show ?thesis
      by-
  qed
  then show \<open>bdd_above ((\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> kraus_family_tensor \<EE> \<FF>})\<close>
    by fast
qed

lemma sandwich_tc_tensor: \<open>sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor t u) = tc_tensor (sandwich_tc E t) (sandwich_tc F u)\<close>
  apply (transfer fixing: E F)
  by (simp add: sandwich_tensor_op)

lemma kraus_family_map_tensor:
  assumes \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
  shows \<open>kraus_family_map (kraus_family_tensor \<EE> \<FF>) (tc_tensor \<rho> \<sigma>) = tc_tensor (kraus_family_map \<EE> \<rho>) (kraus_family_map \<FF> \<sigma>)\<close>
proof -
  have inj: \<open>inj_on (\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)) (\<EE> \<times> \<FF>)\<close>
    by (auto intro!: inj_onI)
  have [simp]: \<open>bounded_linear (\<lambda>x. tc_tensor x (kraus_family_map \<FF> \<sigma>))\<close>
    by (intro bounded_linear_intros)
  have [simp]: \<open>bounded_linear (tc_tensor (sandwich_tc E \<rho>))\<close> for E
    by (intro bounded_linear_intros)
  have sum2: \<open>(\<lambda>(E, x). sandwich_tc E \<rho>) summable_on \<EE>\<close>
    using assms(1) kraus_family_map_summable by blast
  have sum3: \<open>(\<lambda>(F, y). sandwich_tc F \<sigma>) summable_on \<FF>\<close>
    using assms(2) kraus_family_map_summable by blast

  have \<open>kraus_family (kraus_family_tensor \<EE> \<FF>)\<close>
    by (simp add: assms kraus_family_kraus_family_tensor)
  from this[THEN kraus_family_map_summable]
  have sum1: \<open>(\<lambda>((E, x), F, y). sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>)) summable_on \<EE> \<times> \<FF>\<close>
    apply (simp add: kraus_family_map_def kraus_family_tensor_def summable_on_reindex inj o_def)
    by (simp add: case_prod_unfold)


  have \<open>kraus_family_map (kraus_family_tensor \<EE> \<FF>) (tc_tensor \<rho> \<sigma>)
      = (\<Sum>\<^sub>\<infinity>((E,x),(F,y))\<in>\<EE> \<times> \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>))\<close>
    apply (simp add: kraus_family_map_def kraus_family_tensor_def infsum_reindex inj o_def)
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>\<EE>. \<Sum>\<^sub>\<infinity>(F,y)\<in>\<FF>. sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>))\<close>
    apply (subst infsum_Sigma_banach[symmetric])
    using sum1 by (auto intro!: simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>\<EE>. \<Sum>\<^sub>\<infinity>(F,y)\<in>\<FF>. tc_tensor (sandwich_tc E \<rho>) (sandwich_tc F \<sigma>))\<close>
    by (simp add: sandwich_tc_tensor)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>\<EE>. tc_tensor (sandwich_tc E \<rho>) (\<Sum>\<^sub>\<infinity>(F,y)\<in>\<FF>. (sandwich_tc F \<sigma>)))\<close>
    apply (subst infsum_bounded_linear[where f=\<open>tc_tensor (sandwich_tc _ \<rho>)\<close>, symmetric])
      apply (auto intro!: sum3)[2]
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>\<EE>. tc_tensor (sandwich_tc E \<rho>) (kraus_family_map \<FF> \<sigma>))\<close>
    by (simp add: kraus_family_map_def case_prod_unfold)
  also have \<open>\<dots> = tc_tensor (\<Sum>\<^sub>\<infinity>(E,x)\<in>\<EE>. sandwich_tc E \<rho>) (kraus_family_map \<FF> \<sigma>)\<close>
    apply (subst infsum_bounded_linear[where f=\<open>\<lambda>x. tc_tensor x (kraus_family_map \<FF> \<sigma>)\<close>, symmetric])
      apply (auto intro!: sum2)[2]
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = tc_tensor (kraus_family_map \<EE> \<rho>) (kraus_family_map \<FF> \<sigma>)\<close>
    by (simp add: kraus_family_map_def case_prod_unfold)
  finally show ?thesis
    by -
qed


lemma tensor_tc_butterfly: "tc_tensor (tc_butterfly \<psi> \<psi>') (tc_butterfly \<phi> \<phi>') = tc_butterfly (tensor_ell2 \<psi> \<phi>) (tensor_ell2 \<psi>' \<phi>')"
  apply (transfer fixing: \<phi> \<phi>' \<psi> \<psi>') by simp


definition separating_set :: \<open>(('a \<Rightarrow> 'b) \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
  \<open>separating_set P S \<longleftrightarrow> (\<forall>f g. P f \<longrightarrow> P g \<longrightarrow> (\<forall>x\<in>S. f x = g x) \<longrightarrow> f = g)\<close>

lemma separating_set_mono: \<open>S \<subseteq> T \<Longrightarrow> separating_set P S \<Longrightarrow> separating_set P T\<close>
  unfolding separating_set_def by fast

lemma separating_set_UNIV[simp]: \<open>separating_set P UNIV\<close>
  by (auto intro!: ext simp: separating_set_def)


lemma eq_from_separatingI:
  assumes \<open>separating_set P S\<close>
  assumes \<open>P f\<close> and \<open>P g\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> f x = g x\<close>
  shows \<open>f = g\<close>
  using assms by (simp add: separating_set_def)

lemma cblinfun_eq_from_separatingI:
  fixes a b :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>separating_set (bounded_clinear :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) S\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> a x = b x\<close>
  shows \<open>a = b\<close>
  apply (rule cblinfun_eqI, rule fun_cong[where f=\<open>cblinfun_apply _\<close>])
  using assms(1) apply (rule eq_from_separatingI)
  using assms(2) by (auto intro!: bounded_cbilinear_apply_bounded_clinear cblinfun.bounded_cbilinear_axioms simp: )

lemma eq_from_separatingI2:
  assumes \<open>separating_set P ((\<lambda>(x,y). h x y) ` (S\<times>T))\<close>
  assumes \<open>P f\<close> and \<open>P g\<close>
  assumes \<open>\<And>x y. x \<in> S \<Longrightarrow> y \<in> T \<Longrightarrow> f (h x y) = g (h x y)\<close>
  shows \<open>f = g\<close>
  apply (rule eq_from_separatingI[OF assms(1)])
  using assms(2-4) by auto

lemma cblinfun_eq_from_separatingI2:
  fixes a b :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>separating_set (bounded_clinear :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) ((\<lambda>(x,y). h x y) ` (S\<times>T))\<close>
  assumes \<open>\<And>x y. x \<in> S \<Longrightarrow> y \<in> T \<Longrightarrow> a (h x y) = b (h x y)\<close>
  shows \<open>a = b\<close>
  apply (rule cblinfun_eqI, rule fun_cong[where f=\<open>cblinfun_apply _\<close>])
  using assms(1) apply (rule eq_from_separatingI2)
  using assms(2) by (auto intro!: bounded_cbilinear_apply_bounded_clinear cblinfun.bounded_cbilinear_axioms simp: )


(* lemma separating_set_bounded_clinear_tc_tensor_basis:
  assumes \<open>ccspan A = \<top>\<close> \<open>ccspan B = \<top>\<close> \<open>ccspan C = \<top>\<close> \<open>ccspan D = \<top>\<close>
  shows \<open>separating_set bounded_clinear ((\<lambda>(a,b,c,d). tc_tensor (tc_butterfly a b) (tc_butterfly c d)) ` (A\<times>B\<times>C\<times>D))\<close>
  by - *)

lemma separating_set_bounded_clinear_dense:
  assumes \<open>ccspan S = \<top>\<close>
  shows \<open>separating_set bounded_clinear S\<close>
  using assms
  apply (auto intro!: ext simp: separating_set_def)
  apply (rule bounded_clinear_eq_on_closure[where G=S])
  apply auto
  using ccspan.rep_eq by force


lemma separating_set_bounded_clinear_tc_tensor:
  shows \<open>separating_set bounded_clinear ((\<lambda>(\<rho>,\<sigma>). tc_tensor \<rho> \<sigma>) ` (UNIV \<times> UNIV))\<close>
proof -
  have \<open>\<top> = ccspan ((\<lambda>(x, y). tc_butterfly x y) ` (range ket \<times> range ket))\<close>
    by (simp add: onb_butterflies_span_trace_class)
  also have \<open>\<dots> = ccspan ((\<lambda>(x, y, z, w). tc_butterfly (x \<otimes>\<^sub>s y) (z \<otimes>\<^sub>s w)) ` (range ket \<times> range ket \<times> range ket \<times> range ket))\<close>
    by (auto intro!: arg_cong[where f=ccspan] image_eqI simp: tensor_ell2_ket)
  also have \<open>\<dots> = ccspan ((\<lambda>(x, y, z, w). tc_tensor (tc_butterfly x z) (tc_butterfly y w)) ` (range ket \<times> range ket \<times> range ket \<times> range ket))\<close>
    by (simp add: tensor_tc_butterfly)
  also have \<open>\<dots> \<le> ccspan ((\<lambda>(\<rho>, \<sigma>). tc_tensor \<rho> \<sigma>) ` (UNIV \<times> UNIV))\<close>
    by (auto intro!: ccspan_mono)
  finally show ?thesis
    apply (rule_tac separating_set_bounded_clinear_dense)
    using top_le by blast
qed

lemma separating_setI:
  assumes \<open>\<And>f g. P f \<Longrightarrow> P g \<Longrightarrow> (\<And>x. x\<in>S \<Longrightarrow> f x = g x) \<Longrightarrow> f = g\<close>
  shows \<open>separating_set P S\<close>
  by (simp add: assms separating_set_def)

lemma separating_set_bounded_cbilinear_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) ((\<lambda>(x, y). h x y) ` (UNIV \<times> UNIV))\<close>
  assumes \<open>bounded_cbilinear h\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) A\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) ((\<lambda>(x,y). h x y) ` (A \<times> B))\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  have [simp]: \<open>bounded_clinear (\<lambda>x. f (h x y))\<close> for y
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>x. g (h x y))\<close> for y
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>y. f (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_right)
  have [simp]: \<open>bounded_clinear (\<lambda>y. g (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_cbilinear.bounded_clinear_right)

  assume \<open>z \<in> (\<lambda>(x, y). h x y) ` (A \<times> B) \<Longrightarrow> f z = g z\<close> for z
  then have \<open>f (h x y) = g (h x y)\<close> if \<open>x \<in> A\<close> and \<open>y \<in> B\<close> for x y
    using that by auto
  then have \<open>(\<lambda>x. f (h x y)) = (\<lambda>x. g (h x y))\<close> if \<open>y \<in> B\<close> for y
    apply (rule_tac eq_from_separatingI[OF assms(3)])
    using that by auto
  then have \<open>(\<lambda>y. f (h x y)) = (\<lambda>y. g (h x y))\<close> for x
    apply (rule_tac eq_from_separatingI[OF assms(4)])
    apply auto by meson
  then have \<open>f (h x y) = g (h x y)\<close> for x y
    by meson
  with \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  show \<open>f = g\<close>
    apply (rule eq_from_separatingI2[where f=f and g=g and P=bounded_clinear and S=UNIV and T=UNIV, rotated 1])
    using assms(1) by -
qed

lemma separating_set_bounded_clinear_antilinear:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector conjugate_space) \<Rightarrow> _) A\<close>
  shows \<open>separating_set (bounded_antilinear :: (_ => 'e) \<Rightarrow> _) A\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume \<open>bounded_antilinear f\<close>
  then have lin_f: \<open>bounded_clinear (to_conjugate_space o f)\<close>
    by (simp add: bounded_antilinear_o_bounded_antilinear')
  assume \<open>bounded_antilinear g\<close>
  then have lin_g: \<open>bounded_clinear (to_conjugate_space o g)\<close>
    by (simp add: bounded_antilinear_o_bounded_antilinear')
  assume \<open>f x = g x\<close> if \<open>x \<in> A\<close> for x
  then have \<open>(to_conjugate_space o f) x = (to_conjugate_space o g) x\<close> if \<open>x \<in> A\<close> for x
    by (simp add: that)
  with lin_f lin_g
  have \<open>to_conjugate_space o f = to_conjugate_space o g\<close>
    by (rule eq_from_separatingI[OF assms])
  then show \<open>f = g\<close>
    by (metis UNIV_I fun.inj_map_strong to_conjugate_space_inverse)
qed

lemma separating_set_bounded_sesquilinear_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) ((\<lambda>(x, y). h x y) ` (UNIV \<times> UNIV))\<close>
  assumes \<open>bounded_sesquilinear h\<close>
  assumes sep_A: \<open>separating_set (bounded_clinear :: (_ => 'e conjugate_space) \<Rightarrow> _) A\<close>
  assumes sep_B: \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ => 'e) \<Rightarrow> _) ((\<lambda>(x,y). h x y) ` (A \<times> B))\<close>
proof (rule separating_setI)
  fix f g :: \<open>'a \<Rightarrow> 'e\<close>
  assume [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  have [simp]: \<open>bounded_antilinear (\<lambda>x. f (h x y))\<close> for y
    apply (rule bounded_clinear_o_bounded_antilinear[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_antilinear_left)
  have [simp]: \<open>bounded_antilinear (\<lambda>x. g (h x y))\<close> for y
    apply (rule bounded_clinear_o_bounded_antilinear[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_antilinear_left)
  have [simp]: \<open>bounded_clinear (\<lambda>y. f (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear f\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_clinear_right)
  have [simp]: \<open>bounded_clinear (\<lambda>y. g (h x y))\<close> for x
    apply (rule bounded_clinear_compose[OF \<open>bounded_clinear g\<close>])
    using assms(2) by (rule bounded_sesquilinear.bounded_clinear_right)

  from sep_A have sep_A': \<open>separating_set (bounded_antilinear :: (_ => 'e) \<Rightarrow> _) A\<close>
    by (rule separating_set_bounded_clinear_antilinear)
  assume \<open>z \<in> (\<lambda>(x, y). h x y) ` (A \<times> B) \<Longrightarrow> f z = g z\<close> for z
  then have \<open>f (h x y) = g (h x y)\<close> if \<open>x \<in> A\<close> and \<open>y \<in> B\<close> for x y
    using that by auto
  then have \<open>(\<lambda>x. f (h x y)) = (\<lambda>x. g (h x y))\<close> if \<open>y \<in> B\<close> for y
    apply (rule_tac eq_from_separatingI[OF sep_A'])
    using that by auto
  then have \<open>(\<lambda>y. f (h x y)) = (\<lambda>y. g (h x y))\<close> for x
    apply (rule_tac eq_from_separatingI[OF sep_B])
    apply auto by meson
  then have \<open>f (h x y) = g (h x y)\<close> for x y
    by meson
  with \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  show \<open>f = g\<close>
    apply (rule eq_from_separatingI2[where f=f and g=g and P=bounded_clinear and S=UNIV and T=UNIV, rotated 1])
    using assms(1) by -
qed


(* TODO generalize: this just needs that tc_tensor is bounded_bilinear *)
lemma separating_set_bounded_clinear_tc_tensor_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) A\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ => 'e::complex_normed_vector) \<Rightarrow> _) ((\<lambda>(\<rho>,\<sigma>). tc_tensor \<rho> \<sigma>) ` (A \<times> B))\<close>
  using separating_set_bounded_clinear_tc_tensor bounded_cbilinear_tc_tensor assms
  by (rule separating_set_bounded_cbilinear_nested)
(* proof (rule separating_setI)
  fix f g :: \<open>(('a \<times> 'c) ell2, ('b \<times> 'd) ell2) trace_class \<Rightarrow> 'e\<close>
  assume [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  have [simp]: \<open>bounded_clinear (\<lambda>\<rho>. f (tc_tensor \<rho> \<sigma>))\<close> for \<sigma>
    by -
  have [simp]: \<open>bounded_clinear (\<lambda>\<rho>. g (tc_tensor \<rho> \<sigma>))\<close> for \<sigma>
    by -
  have [simp]: \<open>bounded_clinear (\<lambda>\<sigma>. f (tc_tensor \<rho> \<sigma>))\<close> for \<rho>
    by -
  have [simp]: \<open>bounded_clinear (\<lambda>\<sigma>. g (tc_tensor \<rho> \<sigma>))\<close> for \<rho>
    by -

  assume \<open>x \<in> (\<lambda>(\<rho>, \<sigma>). tc_tensor \<rho> \<sigma>) ` (A \<times> B) \<Longrightarrow> f x = g x\<close> for x
  then have \<open>f (tc_tensor \<rho> \<sigma>) = g (tc_tensor \<rho> \<sigma>)\<close> if \<open>\<rho> \<in> A\<close> and \<open>\<sigma> \<in> B\<close> for \<rho> \<sigma>
    using that by auto
  then have \<open>(\<lambda>\<rho>. f (tc_tensor \<rho> \<sigma>)) = (\<lambda>\<rho>. g (tc_tensor \<rho> \<sigma>))\<close> if \<open>\<sigma> \<in> B\<close> for \<sigma>
    apply (rule eq_from_separatingI[OF assms(1), rotated -1])
    using that by auto
  then have \<open>(\<lambda>\<sigma>. f (tc_tensor \<rho> \<sigma>)) = (\<lambda>\<sigma>. g (tc_tensor \<rho> \<sigma>))\<close> for \<rho>
    apply (rule_tac eq_from_separatingI[OF assms(2)])
    apply auto by meson
  then have \<open>f (tc_tensor \<rho> \<sigma>) = g (tc_tensor \<rho> \<sigma>)\<close> for \<rho> \<sigma>
    by meson
  with \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  show \<open>f = g\<close>
    by (rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
qed *)


lemma bounded_sesquilinear_tc_butterfly[iff]: \<open>bounded_sesquilinear (\<lambda>a b. tc_butterfly b a)\<close>
  by (auto intro!: bounded_sesquilinear.intro exI[of _ 1]
      simp: tc_butterfly_add_left tc_butterfly_add_right norm_tc_butterfly)

lemma separating_set_tc_butterfly: \<open>separating_set bounded_clinear ((\<lambda>(g,h). tc_butterfly g h) ` (UNIV \<times> UNIV))\<close>
  apply (rule separating_set_mono[where S=\<open>(\<lambda>(g, h). tc_butterfly g h) ` (some_chilbert_basis \<times> some_chilbert_basis)\<close>])
  by (auto intro!: separating_set_bounded_clinear_dense onb_butterflies_span_trace_class) 

lemma separating_set_tc_butterfly_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c::complex_normed_vector) \<Rightarrow> _) A\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c conjugate_space) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c) \<Rightarrow> _) ((\<lambda>(g,h). tc_butterfly g h) ` (A \<times> B))\<close>
proof -
  from separating_set_tc_butterfly
  have \<open>separating_set bounded_clinear ((\<lambda>(g,h). tc_butterfly g h) ` prod.swap ` (UNIV \<times> UNIV))\<close>
    by simp
  then have \<open>separating_set bounded_clinear ((\<lambda>(g,h). tc_butterfly h g) ` (UNIV \<times> UNIV))\<close>
    unfolding image_image by simp
  then have \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c) \<Rightarrow> _) ((\<lambda>(g,h). tc_butterfly h g) ` (B \<times> A))\<close>
    apply (rule separating_set_bounded_sesquilinear_nested)
    apply (rule bounded_sesquilinear_tc_butterfly)
    using assms by auto
  then have \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c) \<Rightarrow> _) ((\<lambda>(g,h). tc_butterfly h g) ` prod.swap ` (A \<times> B))\<close>
    by (smt (verit, del_insts) SigmaE SigmaI eq_from_separatingI image_iff pair_in_swap_image separating_setI)
  then show ?thesis
    unfolding image_image by simp
qed

(* proof (rule separating_setI)
  fix f g :: \<open>('b, 'a) trace_class \<Rightarrow> 'c\<close>
  assume [simp]: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  have [simp]: \<open>bounded_clinear (\<lambda>\<rho>. f (tc_butterfly \<rho> \<sigma>))\<close> for \<sigma>
try0
sledgehammer [dont_slice]
by -
  have [simp]: \<open>bounded_clinear (\<lambda>\<rho>. g (tc_butterfly \<rho> \<sigma>))\<close> for \<sigma>
try0
sledgehammer [dont_slice]
by -
  have [simp]: \<open>bounded_clinear (\<lambda>\<sigma>. f (tc_butterfly \<rho> \<sigma>))\<close> for \<rho>
try0
sledgehammer [dont_slice]
by -
  have [simp]: \<open>bounded_clinear (\<lambda>\<sigma>. g (tc_butterfly \<rho> \<sigma>))\<close> for \<rho>
try0
sledgehammer [dont_slice]
by -

  assume \<open>x \<in> (\<lambda>(g, h). tc_butterfly g h) ` (A \<times> B) \<Longrightarrow> f x = g x\<close> for x
  then have \<open>f (tc_butterfly \<rho> \<sigma>) = g (tc_butterfly \<rho> \<sigma>)\<close> if \<open>\<rho> \<in> A\<close> and \<open>\<sigma> \<in> B\<close> for \<rho> \<sigma>
    using that by auto
  then have \<open>(\<lambda>\<rho>. f (tc_butterfly \<rho> \<sigma>)) = (\<lambda>\<rho>. g (tc_butterfly \<rho> \<sigma>))\<close> if \<open>\<sigma> \<in> B\<close> for \<sigma>
    apply (rule eq_from_separatingI[OF assms(1), rotated -1])
    using that by auto
  then have \<open>(\<lambda>\<sigma>. f (tc_butterfly \<rho> \<sigma>)) = (\<lambda>\<sigma>. g (tc_butterfly \<rho> \<sigma>))\<close> for \<rho>
    apply (rule_tac eq_from_separatingI[OF assms(2)])
    apply auto by meson
  then have \<open>f (tc_butterfly \<rho> \<sigma>) = g (tc_butterfly \<rho> \<sigma>)\<close> for \<rho> \<sigma>
    by meson
  with \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close>
  show \<open>f = g\<close>
    by (rule eq_from_separatingI2[OF separating_set_tc_butterfly])
qed *)


lemma kraus_tensor_cong:
  assumes \<open>kraus_equivalent \<EE> \<EE>'\<close>
  assumes \<open>kraus_equivalent \<FF> \<FF>'\<close>
  shows \<open>kraus_equivalent (kraus_family_tensor \<EE> \<FF>) (kraus_family_tensor \<EE>' \<FF>')\<close>
proof (intro kraus_equivalent_def[THEN iffD2] conjI)
  have [iff]: \<open>kraus_family \<EE>\<close> \<open>kraus_family \<FF>\<close>
    using assms kraus_equivalent_def by auto
  then show family_\<EE>\<FF>: \<open>kraus_family (kraus_family_tensor \<EE> \<FF>)\<close>
    by (simp add: kraus_family_kraus_family_tensor)
  have [iff]: \<open>kraus_family \<EE>'\<close> \<open>kraus_family \<FF>'\<close>
    using assms kraus_equivalent_def by auto
  then show family_\<EE>'\<FF>': \<open>kraus_family (kraus_family_tensor \<EE>' \<FF>')\<close>
    by (simp add: kraus_family_kraus_family_tensor)
  show \<open>kraus_family_map (kraus_family_tensor \<EE> \<FF>) = kraus_family_map (kraus_family_tensor \<EE>' \<FF>')\<close>
  proof (rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
    show \<open>bounded_clinear (kraus_family_map (kraus_family_tensor \<EE> \<FF>))\<close>
      by (simp add: family_\<EE>\<FF> kraus_family_map_bounded_clinear)
    show \<open>bounded_clinear (kraus_family_map (kraus_family_tensor \<EE>' \<FF>'))\<close>
      by (simp add: family_\<EE>'\<FF>' kraus_family_map_bounded_clinear)
    have \<EE>\<EE>': \<open>kraus_family_map \<EE> \<rho> = kraus_family_map \<EE>' \<rho>\<close> for \<rho>
      by (metis assms(1) kraus_equivalent_def)
    have \<FF>\<FF>': \<open>kraus_family_map \<FF> \<rho> = kraus_family_map \<FF>' \<rho>\<close> for \<rho>
      by (metis assms(2) kraus_equivalent_def)
    fix \<rho> :: \<open>('a ell2, 'a ell2) trace_class\<close> and \<sigma> :: \<open>('e ell2, 'e ell2) trace_class\<close>
    show \<open>kraus_family_map (kraus_family_tensor \<EE> \<FF>) (tc_tensor \<rho> \<sigma>) = kraus_family_map (kraus_family_tensor \<EE>' \<FF>') (tc_tensor \<rho> \<sigma>)\<close>
      by (auto intro!: simp: kraus_family_map_tensor \<EE>\<EE>' \<FF>\<FF>'
          simp flip: tensor_ell2_ket tensor_tc_butterfly)
  qed
qed

lift_definition kraus_map_tensor :: \<open>('a ell2, 'b ell2) kraus_map \<Rightarrow> ('c ell2, 'd ell2) kraus_map \<Rightarrow> (('a\<times>'c) ell2, ('b\<times>'d) ell2) kraus_map\<close> is
  \<open>\<lambda>\<EE> \<FF>. kraus_family_flatten (kraus_family_tensor \<EE> \<FF>)\<close>
  by (intro kraus_equivalent_kraus_family_flatten_left kraus_equivalent_kraus_family_flatten_right kraus_tensor_cong)

lemma kraus_map_tensor:
  shows \<open>kraus_map_apply (kraus_map_tensor \<EE> \<FF>) (tc_tensor \<rho> \<sigma>) = tc_tensor (kraus_map_apply \<EE> \<rho>) (kraus_map_apply \<FF> \<sigma>)\<close>
  apply (transfer fixing: \<rho> \<sigma>)
  by (simp add: kraus_equivalent_def kraus_family_flatten_same_map kraus_family_kraus_family_tensor kraus_family_map_tensor)

lemma kraus_map_tensor_compose_distribute:
  shows \<open>kraus_map_tensor (kraus_map_comp \<EE> \<FF>) (kraus_map_comp \<GG> \<HH>) = kraus_map_comp (kraus_map_tensor \<EE> \<GG>) (kraus_map_tensor \<FF> \<HH>)\<close>
  apply (intro kraus_map_apply_inj cblinfun_apply_inject[THEN iffD1] eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
  by (auto intro!: bounded_linear_intros simp: kraus_map_tensor kraus_map_apply_comp o_def)

(* definition kraus_family_trace :: \<open>('a::chilbert_space, 'b::one_dim, 'a) kraus_family\<close> where
  \<open>kraus_family_trace = (\<lambda>b. (vector_to_cblinfun b*, b)) ` some_chilbert_basis\<close>

lemma kraus_family_trace[iff]: \<open>kraus_family (kraus_family_trace :: ('a::chilbert_space, 'b::one_dim, 'a) kraus_family)\<close>
proof (intro kraus_familyI bdd_aboveI)
  fix M assume \<open>M \<in> (\<lambda>F. \<Sum>(E :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> kraus_family_trace}\<close>
  then obtain F where M_sum: \<open>M = (\<Sum>(E :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b, x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close> and \<open>finite F\<close> and \<open>F \<subseteq> kraus_family_trace\<close>
    by blast
  define F' where \<open>F' = snd ` F\<close>
  from \<open>F \<subseteq> kraus_family_trace\<close>
  have \<open>inj_on snd F\<close>
    apply (auto intro!: inj_onI simp: kraus_family_trace_def)
    using subsetD by fastforce
  from \<open>F \<subseteq> kraus_family_trace\<close>
  have ortho_F': \<open>is_ortho_set F'\<close>
    apply (auto intro!: simp: F'_def kraus_family_trace_def image_image elim!: subset_imageE)
    using is_ortho_set_antimono is_ortho_set_some_chilbert_basis by blast
  from \<open>F \<subseteq> kraus_family_trace\<close>
  have norm_F': \<open>b \<in> F' \<Longrightarrow> norm b = 1\<close> for b
    apply (auto intro!: simp: F'_def kraus_family_trace_def image_image elim!: subset_imageE)
    using is_normal_some_chilbert_basis by blast
  have \<open>a* o\<^sub>C\<^sub>L a = (vector_to_cblinfun b* )* o\<^sub>C\<^sub>L (vector_to_cblinfun b* :: _ \<Rightarrow>\<^sub>C\<^sub>L 'b)\<close> if \<open>(a,b) \<in> F\<close> for a b
    using \<open>F \<subseteq> kraus_family_trace\<close> that
    by (simp add: kraus_family_trace_def subset_iff image_def)
  then have \<open>M = (\<Sum>b\<in>F'. vector_to_cblinfun b o\<^sub>C\<^sub>L (vector_to_cblinfun b* :: _ \<Rightarrow>\<^sub>C\<^sub>L 'b))\<close>
    by (auto intro!: sum.cong simp: M_sum F'_def sum.reindex \<open>inj_on snd F\<close>)
  then have \<open>M = (\<Sum>b\<in>F'. butterfly b b)\<close>
    by (metis (mono_tags, lifting) Finite_Cartesian_Product.sum_cong_aux butterfly_def_one_dim)
  also from ortho_F' norm_F' have \<open>\<dots> \<le> id_cblinfun\<close>
    by (rule sum_butterfly_leq_id)
  finally show \<open>M \<le> id_cblinfun\<close>
    by -
qed *)

lemma infsum_bounded_linear_invertible:
  assumes \<open>bounded_linear f\<close>
  assumes \<open>bounded_linear f'\<close>
  assumes \<open>f' o f = id\<close>
  shows \<open>infsum (f \<circ> g) S = f (infsum g S)\<close>
proof (cases \<open>g summable_on S\<close>)
  case True
  then show ?thesis
    using assms(1) infsum_bounded_linear by blast
next
  case False
  have \<open>\<not> (f o g) summable_on S\<close>
  proof (rule ccontr)
    assume \<open>\<not> \<not> f \<circ> g summable_on S\<close>
    with \<open>bounded_linear f'\<close> have \<open>f' o f o g summable_on S\<close>
      by (auto intro: summable_on_bounded_linear simp: o_def)
    then have \<open>g summable_on S\<close>
      by (simp add: assms(3))
    with False show False
      by blast
  qed
  then show ?thesis
    by (simp add: False assms(1) infsum_not_exists linear_simps(3))
qed


(* lemma kraus_family_map_trace: \<open>trace_tc t = one_dim_iso (kraus_family_map (kraus_family_trace :: ('a::chilbert_space, 'b::one_dim, 'a) kraus_family) t)\<close>
proof -
  note infsum_one_dim = infsum_bounded_linear_invertible[symmetric, OF 
      bounded_clinear.bounded_linear[OF bounded_clinear_one_dim_iso]
      bounded_clinear.bounded_linear[OF bounded_clinear_one_dim_iso]]
  have \<open>(one_dim_iso (kraus_family_map (kraus_family_trace :: ('a::chilbert_space, 'b::one_dim, 'a) kraus_family) t) :: complex) = 
      (\<Sum>\<^sub>\<infinity>x\<in>some_chilbert_basis. one_dim_iso (from_trace_class (sandwich_tc (vector_to_cblinfun x* :: _ \<Rightarrow>\<^sub>C\<^sub>L 'b) *\<^sub>V t)))\<close>
    apply (simp add: kraus_family_map_def kraus_family_trace_def infsum_reindex inj_on_def o_def trace_tc.rep_eq)
    apply (subst infsum_one_dim)
    by (auto simp: o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>some_chilbert_basis. x \<bullet>\<^sub>C (from_trace_class t *\<^sub>V x))\<close>
    apply (simp only: from_trace_class_sandwich_tc sandwich_apply)
    by simp
  also have \<open>\<dots> = trace_tc t\<close>
    by (simp add: infsum_reindex inj_on_def o_def trace_tc.rep_eq trace_alt_def[OF is_onb_some_chilbert_basis])
  finally show ?thesis
    by simp
qed *)

(* lift_definition kraus_map_trace :: \<open>('a::chilbert_space, 'b::one_dim) kraus_map\<close> is \<open>kraus_family_flatten kraus_family_trace\<close>
  by (auto simp: kraus_equivalent_def) *)

lemma trace_kraus_map_is_trace': \<open>trace_tc t = one_dim_iso (kraus_map_apply trace_kraus_map t)\<close>
  apply (transfer fixing: t)
  by (simp add: kraus_family_flatten_same_map trace_kraus_family_is_kraus_family trace_kraus_family_is_trace)

lemma partial_trace_scaleC: \<open>partial_trace (c *\<^sub>C t) = c *\<^sub>C partial_trace t\<close>
  by (simp add: partial_trace_def infsum_scaleC_right compose_tcr.scaleC_right compose_tcl.scaleC_left)

lemma partial_trace_tensor: \<open>partial_trace (tc_tensor t u) = trace_tc u *\<^sub>C t\<close>
proof -
  define t' u' where \<open>t' = from_trace_class t\<close> and \<open>u' = from_trace_class u\<close>
  have 1: \<open>(\<lambda>j. ket j \<bullet>\<^sub>C (from_trace_class u *\<^sub>V ket j)) summable_on UNIV\<close>
    using  trace_exists[where B=\<open>range ket\<close> and A=\<open>from_trace_class u\<close>]
    by (simp add: summable_on_reindex o_def)
  have \<open>partial_trace (tc_tensor t u) =
      (\<Sum>\<^sub>\<infinity>j. compose_tcl (compose_tcr (tensor_ell2_right (ket j)*) (tc_tensor t u)) (tensor_ell2_right (ket j)))\<close>
    by (simp add: partial_trace_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>j. (ket j \<bullet>\<^sub>C (from_trace_class u *\<^sub>V ket j)) *\<^sub>C t)\<close>
  proof -
    have *: \<open>tensor_ell2_right (ket j)* o\<^sub>C\<^sub>L t' \<otimes>\<^sub>o u' o\<^sub>C\<^sub>L tensor_ell2_right (ket j) =
         (ket j \<bullet>\<^sub>C (u' *\<^sub>V ket j)) *\<^sub>C t'\<close> for j
      by (auto intro!: cblinfun_eqI simp: tensor_op_ell2)
    show ?thesis
    apply (rule infsum_cong)
      by (auto intro!: from_trace_class_inject[THEN iffD1] simp flip: t'_def u'_def
        simp: * compose_tcl.rep_eq compose_tcr.rep_eq tc_tensor.rep_eq scaleC_trace_class.rep_eq)
  qed
  also have \<open>\<dots> = trace_tc u *\<^sub>C t\<close>
    by (auto intro!: infsum_scaleC_left simp: trace_tc_def trace_alt_def[OF is_onb_ket] infsum_reindex o_def 1)
  finally show ?thesis
    by -
qed


lemma bounded_clinear_partial_trace[bounded_clinear, iff]: \<open>bounded_clinear partial_trace\<close>
  apply (rule bounded_clinearI[where K=1])
  by (auto simp add: partial_trace_plus partial_trace_scaleC partial_trace_norm_reducing)


lemma partial_trace_as_kraus_map: \<open>partial_trace t = 
  kraus_map_apply (kraus_map_of_op (tensor_ell2_right 1*))
  (kraus_map_apply (kraus_map_tensor kraus_map_id trace_kraus_map) t)\<close>
(* TODO: also "kraus_map_apply (kraus_map_tensor kraus_map_id kraus_map_trace) t = ... partial_trace ... *)
proof (rule fun_cong[where x=t], rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
  show \<open>bounded_clinear partial_trace\<close>
    by simp
  show \<open>bounded_clinear
     (\<lambda>a. kraus_map_apply (kraus_map_of_op (tensor_ell2_right 1*))
           (kraus_map_apply (kraus_map_tensor kraus_map_id trace_kraus_map) a))\<close>
    by (intro bounded_linear_intros)
  fix \<rho> :: \<open>('a ell2, 'a ell2) trace_class\<close> and \<sigma> :: \<open>('b ell2, 'b ell2) trace_class\<close>
  show \<open>partial_trace (tc_tensor \<rho> \<sigma>) =
           kraus_map_apply (kraus_map_of_op (tensor_ell2_right 1*))
           (kraus_map_apply (kraus_map_tensor kraus_map_id trace_kraus_map) (tc_tensor \<rho> \<sigma>))\<close>
    apply (auto intro!: from_trace_class_inject[THEN iffD1]
        simp: partial_trace_tensor kraus_map_tensor trace_kraus_map_is_trace kraus_map_of_op_apply
        from_trace_class_sandwich_tc sandwich_apply trace_tc.rep_eq tc_tensor.rep_eq scaleC_trace_class.rep_eq)
    by (auto intro!: cblinfun_eqI simp: tensor_op_ell2)
qed

lemma partial_trace_ignore_trace_preserving_map:
  assumes \<open>trace_preserving \<EE>\<close>
  shows \<open>partial_trace (kraus_map_apply (kraus_map_tensor kraus_map_id \<EE>) \<rho>) = partial_trace \<rho>\<close>
proof (rule fun_cong[where x=\<rho>], rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
  show \<open>bounded_clinear (\<lambda>a. partial_trace (kraus_map_apply (kraus_map_tensor kraus_map_id \<EE>) a))\<close>
    by (intro bounded_linear_intros)
  show \<open>bounded_clinear partial_trace\<close>
    by (intro bounded_linear_intros)
  fix \<rho> :: \<open>('c ell2, 'c ell2) trace_class\<close> and \<sigma> :: \<open>('a ell2, 'a ell2) trace_class\<close>
  from assms
  show \<open>partial_trace (kraus_map_apply (kraus_map_tensor kraus_map_id \<EE>) (tc_tensor \<rho> \<sigma>)) = partial_trace (tc_tensor \<rho> \<sigma>)\<close>
    by (auto intro!: simp: kraus_map_tensor partial_trace_tensor trace_preserving_def)
qed

lemma kraus_map_comp_id_left[simp]: \<open>kraus_map_comp kraus_map_id \<EE> = \<EE>\<close>
  by (auto intro!: kraus_map_apply_inj cblinfun_eqI simp: kraus_map_apply_comp kraus_map_id_apply)

lemma kraus_map_comp_id_right[simp]: \<open>kraus_map_comp \<EE> kraus_map_id = \<EE>\<close>
  by (auto intro!: kraus_map_apply_inj cblinfun_eqI simp: kraus_map_apply_comp kraus_map_id_apply)

end
