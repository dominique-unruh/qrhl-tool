theory Kraus_Maps
  imports Tensor_Product.Trace_Class Registers2.Missing_Bounded_Operators Wlog.Wlog "HOL-Library.Rewrite"
begin

unbundle cblinfun_notation

definition \<open>kraus_family \<EE> \<longleftrightarrow> bdd_above ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
  for \<EE> :: \<open>((_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space) \<times> _) set\<close>

typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family = 
  \<open>Collect kraus_family :: (('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<times> 'x) set set\<close>
  by (rule exI[of _ \<open>{}\<close>], auto simp: kraus_family_def)
setup_lifting type_definition_kraus_family

lift_definition kraus_family_bound :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close> is
  \<open>\<lambda>\<EE>. infsum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>)\<close> .
definition \<open>kraus_family_norm \<EE> = norm (kraus_family_bound \<EE>)\<close>
(* definition \<open>kraus_family_norm \<EE> = (if kraus_family \<EE> \<and> \<EE> \<noteq> {} then
          SUP F\<in>{M. M \<subseteq> \<EE> \<and> finite M}. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) else 0)\<close>
  for \<EE> :: \<open>(_::chilbert_space, _::chilbert_space, _) kraus_family\<close> *)

lemma kraus_familyI:
  assumes \<open>bdd_above ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
  (* assumes \<open>0 \<notin> fst ` \<EE>\<close> *)
  shows \<open>kraus_family \<EE>\<close>
  by (meson assms kraus_family_def)


lemma kraus_family_norm_bdd: \<open>bdd_above ((\<lambda>F. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)) ` {F. F \<subseteq> Rep_kraus_family \<EE> \<and> finite F})\<close>
proof -
  from Rep_kraus_family[of \<EE>]
  obtain B where B_bound: \<open>(\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>F \<subseteq> Rep_kraus_family \<EE>\<close> and \<open>finite F\<close> for F
    by (metis (mono_tags, lifting) bdd_above.unfold imageI kraus_family_def mem_Collect_eq)
  have \<open>norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> norm B\<close> if \<open>F \<subseteq> Rep_kraus_family \<EE>\<close> and \<open>finite F\<close> for F
    by (metis (no_types, lifting) B_bound norm_cblinfun_mono positive_cblinfun_squareI split_def sum_nonneg that(1) that(2))
  then show \<open>bdd_above ((\<lambda>F. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)) ` {F. F \<subseteq> Rep_kraus_family \<EE> \<and> finite F})\<close>
    by (metis (mono_tags, lifting) bdd_aboveI2 mem_Collect_eq)
qed

lemma kraus_family_norm_geq0:
  shows \<open>kraus_family_norm \<EE> \<ge> 0\<close>
proof (cases \<open>Rep_kraus_family \<EE> \<noteq> {}\<close>)
  case True
  then obtain E where \<open>E \<in> Rep_kraus_family \<EE>\<close> by auto
  have \<open>0 \<le> (\<Squnion>F\<in>{F. F \<subseteq> Rep_kraus_family \<EE> \<and> finite F}. norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E))\<close>
    apply (rule cSUP_upper2[where x=\<open>{E}\<close>])
    using True by (simp_all add: \<open>E \<in> Rep_kraus_family \<EE>\<close> kraus_family_norm_bdd)
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
  shows \<open>has_sum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>) (kraus_family_bound \<EE>)\<close>
proof -
  obtain B where B: \<open>finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> for F
    using Rep_kraus_family[of \<EE>]
    by (auto simp: kraus_family_def case_prod_unfold bdd_above_def)
  have \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>)\<close>
    apply (auto intro!: summable_wot_boundedI positive_cblinfun_squareI simp: kraus_family_def)
    using B by blast
  then show ?thesis
    by (auto intro!: has_sum_in_infsum_in simp: kraus_family_bound_def)
qed

lemma kraus_family_Sup:
  shows \<open>is_Sup ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> Rep_kraus_family \<EE>}) (kraus_family_bound \<EE>)\<close>
proof -
  from Rep_kraus_family[of \<EE>]
  obtain B where \<open>finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> for F
    by (metis (mono_tags, lifting) bdd_above.unfold imageI kraus_family_def mem_Collect_eq)
  then have \<open>is_Sup ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> Rep_kraus_family \<EE>})
     (infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>))\<close>
    apply (rule infsum_wot_is_Sup[OF summable_wot_boundedI[where B=B]])
    by (auto intro!: summable_wot_boundedI positive_cblinfun_squareI simp: case_prod_beta)
  then show ?thesis
    by (auto intro!: simp: kraus_family_bound_def)
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


definition kraus_family_related_ops :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> _\<close> where
  \<open>kraus_family_related_ops \<EE> E = {(F,x) \<in> Rep_kraus_family \<EE>. (\<exists>r>0. E = r *\<^sub>R F)}\<close>

definition kraus_family_op_weight where
  \<open>kraus_family_op_weight \<EE> E = (\<Sum>\<^sub>\<infinity>(F,_)\<in>kraus_family_related_ops \<EE> E. norm (F* o\<^sub>C\<^sub>L F))\<close>

lemma kraus_family_op_weight_geq0[simp]: \<open>kraus_family_op_weight \<EE> E \<ge> 0\<close>
  by (auto intro!: infsum_nonneg simp: kraus_family_op_weight_def)

lemma kraus_family_related_ops_abs_summable:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
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

  from Rep_kraus_family[of \<EE>]
  have \<open>bdd_above ((\<lambda>M. \<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) ` {M. finite M \<and> M \<subseteq> Rep_kraus_family \<EE>})\<close>
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
  if \<open>(E,x) \<in> Rep_kraus_family \<EE>\<close> and \<open>E \<noteq> 0\<close>
proof -
  have 1: \<open>(E, x) \<in> kraus_family_related_ops \<EE> E\<close>
    by (auto intro!: exI[where x=1] simp: kraus_family_related_ops_def that)

  have \<open>kraus_family_op_weight \<EE> E = (\<Sum>\<^sub>\<infinity>(F, x)\<in>kraus_family_related_ops \<EE> E. (norm F)\<^sup>2)\<close>
    by (simp add: kraus_family_op_weight_def)
  moreover have \<open>\<dots> \<ge> (\<Sum>\<^sub>\<infinity>(F, x)\<in>{(E,x)}. (norm F)\<^sup>2)\<close> (is \<open>_ \<ge> \<dots>\<close>)
    apply (rule infsum_mono_neutral)
    using kraus_family_related_ops_abs_summable
    by (auto intro!: 1 simp: that case_prod_unfold)
  moreover have \<open>\<dots> > 0\<close>
    using that by simp
  ultimately show ?thesis
    by auto
qed

lemma kraus_family_bound_pos[simp]: \<open>kraus_family_bound \<EE> \<ge> 0\<close>
  using kraus_family_Sup[of \<EE>]
  by (metis (no_types, lifting) empty_subsetI finite.emptyI image_iff is_Sup_def mem_Collect_eq sum.empty)

lemma kraus_family_sums_bounded_by_bound:
  assumes \<open>M \<subseteq> Rep_kraus_family \<EE>\<close>
  shows \<open>(\<Sum>(E,_)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> kraus_family_bound \<EE>\<close>
proof (cases \<open>finite M\<close>)
  case True
  then show ?thesis
  using kraus_family_Sup[of \<EE>]
  apply (simp add: is_Sup_def case_prod_beta)
  using assms by blast
next
  case False
  then show ?thesis
    by simp
qed

lemma kraus_family_sums_bounded_by_norm:
  assumes \<open>M \<subseteq> Rep_kraus_family \<EE>\<close>
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


lift_definition kraus_family_map :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a,'a) trace_class \<Rightarrow> ('b,'b) trace_class\<close> is
  \<open>\<lambda>\<EE> \<rho>. (\<Sum>\<^sub>\<infinity>E\<in>\<EE>. sandwich_tc (fst E) \<rho>)\<close> .

lemma kraus_family_emptyset[iff]: \<open>kraus_family {}\<close>
  by (auto simp: kraus_family_def)


instantiation kraus_family :: (chilbert_space, chilbert_space, type) \<open>zero\<close> begin
lift_definition zero_kraus_family :: \<open>('a,'b,'x) kraus_family\<close> is \<open>{}\<close>
  by simp
instance..
end

lemma kraus_family_map_0[simp]: \<open>kraus_family_map 0 = 0\<close>
  by (auto simp: kraus_family_map_def zero_kraus_family.rep_eq)

definition \<open>kraus_equivalent \<EE> \<FF> \<longleftrightarrow> kraus_family_map \<EE> = kraus_family_map \<FF>\<close>

lemma kraus_equivalent_reflI: \<open>kraus_equivalent x x\<close>
  by (simp add: kraus_equivalent_def)

(* lemma kraus_family_zero[simp]: \<open>kraus_family {}\<close>
  by (auto simp: kraus_family_def) *)

(* TODO define map function? *)
quotient_type (overloaded) ('a,'b) kraus_map = \<open>('a::chilbert_space, 'b::chilbert_space, unit) kraus_family\<close> / kraus_equivalent
  by (auto intro!: equivpI exI[of _ \<open>{}\<close>] reflpI sympI transpI simp: kraus_equivalent_def)

lift_definition kraus_family_comp_dependent :: \<open>('x \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'y) kraus_family) \<Rightarrow> ('a::chilbert_space,'b,'x) kraus_family
                    \<Rightarrow> ('a,'c,'b \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'y \<times> 'x) kraus_family\<close> is
  \<open>\<lambda>\<EE> \<FF>. if bdd_above ((kraus_family_norm o \<EE>) ` UNIV) then
    (\<lambda>((F,y), (E::'b\<Rightarrow>\<^sub>C\<^sub>L'c,x::'y)). (E o\<^sub>C\<^sub>L F, (E,F,x,y))) ` (SIGMA (F::'a\<Rightarrow>\<^sub>C\<^sub>L'b,y::'x):Rep_kraus_family \<FF>. (Rep_kraus_family (\<EE> y)))
    else {}\<close>
(* lemma kraus_family_kraus_family_comp_dependent:
  fixes \<EE> :: \<open>'y \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('c::chilbert_space, 'a, 'y) kraus_family\<close>
  assumes \<EE>_family: \<open>\<And>y. kraus_family (\<EE> y)\<close> and \<FF>_family: \<open>kraus_family \<FF>\<close>
  assumes \<EE>_uniform: \<open>\<And>y. kraus_family_norm (\<EE> y) \<le> B\<close>
  shows \<open>kraus_family (kraus_family_comp_dependent \<EE> \<FF>)\<close> *)
proof (rename_tac \<EE> \<FF>)
  fix \<EE> :: \<open>'x \<Rightarrow> ('b, 'c, 'y) kraus_family\<close> and \<FF> :: \<open>('a, 'b, 'x) kraus_family\<close>
  show \<open>(if bdd_above ((kraus_family_norm o \<EE>) ` UNIV)
        then (\<lambda>((F, y), E, x). (E o\<^sub>C\<^sub>L F, E, F, x, y)) ` (SIGMA (F, y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))
        else {})
       \<in> Collect kraus_family\<close>
  proof (cases \<open>bdd_above ((kraus_family_norm o \<EE>) ` UNIV)\<close>)
    case True
    obtain BF where BF: \<open>(\<Sum>(F, y)\<in>M. (F* o\<^sub>C\<^sub>L F)) \<le> BF\<close> if \<open>M \<subseteq> Rep_kraus_family \<FF>\<close> and \<open>finite M\<close> for M
      using Rep_kraus_family[of \<FF>]
      by (metis (mono_tags, lifting) bdd_above.unfold imageI kraus_family_def mem_Collect_eq)
    from True obtain B where \<EE>_uniform: \<open>kraus_family_norm (\<EE> y) \<le> B\<close> for y
      by (auto simp: bdd_above_def)
    define BE :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>BE = B *\<^sub>R id_cblinfun\<close>
    define \<FF>x\<EE> where \<open>\<FF>x\<EE> = (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
    from \<EE>_uniform
    have BE: \<open>(\<Sum>(E, x)\<in>M. (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> if \<open>M \<subseteq> Rep_kraus_family (\<EE> y)\<close> and \<open>finite M\<close> for M y
      using that
      using kraus_family_sums_bounded_by_norm[of _ \<open>\<EE> _\<close>]
      apply (auto intro!: simp: BE_def case_prod_beta)
      by (smt (verit) adj_0 comparable_hermitean less_eq_scaled_id_norm positive_cblinfun_squareI scaleR_scaleC sum_nonneg)
    have [simp]: \<open>B \<ge> 0\<close>
      using kraus_family_norm_geq0[of \<open>\<EE> undefined\<close>] \<EE>_uniform[of undefined] by auto

    have \<open>bdd_above ((\<lambda>M. \<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) `
            {M. M \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (E,F,x,y))) ` \<FF>x\<EE> \<and> finite M})\<close>
    proof (rule bdd_aboveI, rename_tac A)
      fix A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
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

      have CE_sub_\<EE>: \<open>CE y \<subseteq> Rep_kraus_family (\<EE> y)\<close> and \<open>CF \<subseteq> Rep_kraus_family \<FF>\<close> for y
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
        using BF by (simp add: \<open>CF \<subseteq> Rep_kraus_family \<FF>\<close> scaleR_left_mono case_prod_unfold)
      finally show \<open>A \<le> B *\<^sub>R BF\<close>
        by -
    qed
    then have \<open>kraus_family ((\<lambda>((F, y), E, x). (E o\<^sub>C\<^sub>L F, E, F, x, y)) ` (SIGMA (F, y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y)))\<close>
      by (auto intro!: kraus_familyI simp: conj_commute \<FF>x\<EE>_def)
    then show ?thesis
      using True by simp
  next
    case False
    then show ?thesis
      by (auto simp: kraus_family_def)
  qed
qed





definition \<open>kraus_family_comp \<EE> \<FF> = kraus_family_comp_dependent (\<lambda>_. \<EE>) \<FF>\<close>

(* definition \<open>kraus_family_comp \<EE> \<FF> = (\<lambda>((E,x), (F,y)). (E o\<^sub>C\<^sub>L F, (E,F,x,y))) ` (\<EE>\<times>\<FF>)\<close> 
  for \<EE> \<FF> :: \<open>(_::chilbert_space, _::chilbert_space, _) kraus_family\<close> *)

lemma kraus_family_finite: \<open>kraus_family \<EE>\<close> if \<open>finite \<EE>\<close>
proof -
  define B where \<open>B = (\<Sum>(E,x)\<in>\<EE>. E* o\<^sub>C\<^sub>L E)\<close>
  have \<open>(\<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>finite M\<close> and \<open>M \<subseteq> \<EE>\<close> for M
    unfolding B_def
    using \<open>finite \<EE>\<close> \<open>M \<subseteq> \<EE>\<close> apply (rule sum_mono2)
    by (auto intro!: positive_cblinfun_squareI)
  with that show ?thesis
    by (auto intro!: bdd_aboveI[of _ B] simp: kraus_family_def)
qed

lift_definition kraus_family_of_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> ('a, 'b, unit) kraus_family\<close> is
  \<open>\<lambda>E::'a\<Rightarrow>\<^sub>C\<^sub>L'b. {(E, ())}\<close>
  by (auto intro: kraus_family_finite)

lemma kraus_family_bound_finite: \<open>kraus_family_bound \<EE> = (\<Sum>(E,x)\<in>Rep_kraus_family \<EE>. E* o\<^sub>C\<^sub>L E)\<close> if \<open>finite (Rep_kraus_family \<EE>)\<close>
  by (auto intro!: kraus_family_finite simp: kraus_family_bound_def that infsum_in_finite)

lemma kraus_family_norm_finite: \<open>kraus_family_norm \<EE> = norm (\<Sum>(E,x)\<in>Rep_kraus_family \<EE>. E* o\<^sub>C\<^sub>L E)\<close>
  if \<open>finite (Rep_kraus_family \<EE>)\<close>
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

(* lemma kraus_family_kraus_family_of_op[simp]: \<open>kraus_family (kraus_family_of_op E)\<close>
  by (auto intro!: kraus_family_finite simp: kraus_family_of_op_def) *)

lemma kraus_family_norm_0[simp]: \<open>kraus_family_norm 0 = 0\<close>
  apply (simp add: kraus_family_norm_def kraus_family_bound.rep_eq zero_kraus_family.rep_eq)
  by (metis (mono_tags, lifting) finite.intros(1) kraus_family_bound.abs_eq kraus_family_bound_finite sum.empty zero_kraus_family.rep_eq)

lemma kraus_family_of_op_norm[simp]: \<open>kraus_family_norm (kraus_family_of_op E) = (norm E)\<^sup>2\<close>
  by (simp add: kraus_family_of_op.rep_eq kraus_family_norm_finite)
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
  is kraus_family_of_op.

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
  (* assumes \<open>kraus_family \<EE>\<close> *)
  shows \<open>(\<lambda>(E,x). sandwich_tc E \<rho>) summable_on (Rep_kraus_family \<EE>)\<close>
  apply (rule abs_summable_summable)
  apply (rule kraus_family_map_abs_summable)
  using Rep_kraus_family by blast

lemma kraus_family_map_has_sum:
  shows \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum kraus_family_map \<EE> \<rho>) (Rep_kraus_family \<EE>)\<close>
  using kraus_family_map_summable Rep_kraus_family[of \<EE>]
  by (auto intro!: has_sum_infsum simp add: kraus_family_map_def kraus_family_map_summable case_prod_unfold)

lemma kraus_family_map_plus_right:
  shows \<open>kraus_family_map \<EE> (x + y) = kraus_family_map \<EE> x + kraus_family_map \<EE> y\<close>
  using kraus_family_map_summable Rep_kraus_family[of \<EE>]
  by (auto intro!: infsum_add
      simp add: kraus_family_map_def sandwich_tc_plus scaleC_add_right case_prod_unfold)

lemma sandwich_tc_uminus_right: \<open>sandwich_tc e (- t) = - sandwich_tc e t\<close>
  by (metis (no_types, lifting) add.right_inverse arith_simps(50) diff_0 group_cancel.sub1 sandwich_tc_minus)

lemma kraus_family_map_uminus_right:
  shows \<open>kraus_family_map \<EE> (- x) = - kraus_family_map \<EE> x\<close>
  using kraus_family_map_summable  Rep_kraus_family[of \<EE>]
  by (auto intro!: infsum_uminus 
      simp add: kraus_family_map_def sandwich_tc_uminus_right scaleC_minus_right case_prod_unfold)


lemma kraus_family_map_minus_right:
  shows \<open>kraus_family_map \<EE> (x - y) = kraus_family_map \<EE> x - kraus_family_map \<EE> y\<close>
  by (simp only: diff_conv_add_uminus kraus_family_map_plus_right kraus_family_map_uminus_right)

lemma kraus_family_map_pos:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kraus_family_map \<EE> \<rho> \<ge> 0\<close>
  by (auto intro!: infsum_nonneg_traceclass scaleC_nonneg_nonneg of_nat_0_le_iff
      sandwich_tc_pos assms simp: kraus_family_map_def)

lemma kraus_family_map_bounded_pos:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>norm (kraus_family_map \<EE> \<rho>) \<le> kraus_family_norm \<EE> * norm \<rho>\<close>
proof -
  have \<open>norm (kraus_family_map \<EE> \<rho>) = Re (trace_tc (\<Sum>\<^sub>\<infinity>(E,_)\<in>Rep_kraus_family \<EE>. sandwich_tc E \<rho>))\<close>
    apply (subst Re_complex_of_real[symmetric])
    apply (subst norm_tc_pos)
    using \<open>\<rho> \<ge> 0\<close> apply (rule kraus_family_map_pos)
    by (simp add: kraus_family_map_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,_)\<in>Rep_kraus_family \<EE>. Re (trace_tc (sandwich_tc E \<rho>)))\<close>
    using kraus_family_map_summable[of _ \<EE>]
    by (simp_all flip: infsum_bounded_linear[of \<open>\<lambda>x. Re (trace_tc x)\<close>] 
        add: case_prod_unfold bounded_linear_compose[of Re trace_tc] bounded_linear_Re
        o_def bounded_clinear.bounded_linear)
  also have \<open>\<dots> \<le> kraus_family_norm \<EE> * norm \<rho>\<close>
  proof (rule infsum_le_finite_sums)
    show \<open>(\<lambda>(E,_). Re (trace_tc (sandwich_tc E \<rho>))) summable_on (Rep_kraus_family \<EE>)\<close>
      unfolding case_prod_beta
      apply (rule summable_on_bounded_linear[unfolded o_def, where h=\<open>\<lambda>x. Re (trace_tc x)\<close>])
      using kraus_family_map_summable[of _ \<EE>]
      by (simp_all flip: infsum_bounded_linear[of \<open>\<lambda>x. Re (trace_tc x)\<close>] 
        add: bounded_linear_compose[of Re trace_tc] bounded_linear_Re bounded_clinear.bounded_linear 
        o_def trace_tc_scaleC assms kraus_family_map_def case_prod_unfold)
    fix M :: \<open>(('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<times> 'c) set\<close> assume \<open>finite M\<close> and \<open>M \<subseteq> Rep_kraus_family \<EE>\<close>
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
      using assms \<open>M \<subseteq> Rep_kraus_family \<EE>\<close> by auto
    finally show \<open>(\<Sum>(E,_)\<in>M. Re (trace_tc (sandwich_tc E \<rho>))) \<le> kraus_family_norm \<EE> * norm \<rho>\<close>
      by -
  qed
  finally show ?thesis 
    by -
qed

lemma kraus_family_map_bounded:
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
    by (auto intro!: mult_left_mono add_mono kraus_family_norm_geq0 
        simp only: aux norm)
  also have \<open>\<dots> = 4 * kraus_family_norm \<EE> * norm \<rho>\<close>
    by argo
  finally show ?thesis
    by -
qed

lemma kraus_family_map_bounded_clinear:
  shows \<open>bounded_clinear (kraus_family_map \<EE>)\<close>
  apply (rule bounded_clinearI[where K=\<open>4 * kraus_family_norm \<EE>\<close>])
    apply (auto intro!: kraus_family_map_plus_right kraus_family_map_scaleC
      mult.commute)
  using kraus_family_map_bounded
  by (simp add: mult.commute)

lemma kraus_family_bound_from_map:
  shows \<open>\<psi> \<bullet>\<^sub>C kraus_family_bound \<EE> \<phi> = trace_tc (kraus_family_map \<EE> (tc_butterfly \<phi> \<psi>))\<close>
proof -
  have \<open>has_sum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>) (kraus_family_bound \<EE>)\<close>
    by (simp add: kraus_family_bound_has_sum)
  then have \<open>((\<lambda>(E, x). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum \<psi> \<bullet>\<^sub>C kraus_family_bound \<EE> \<phi>) (Rep_kraus_family \<EE>)\<close>
    by (auto intro!: simp: has_sum_in_cweak_operator_topology_pointwise case_prod_unfold)
  moreover have \<open>((\<lambda>(E, x). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum trace_tc (kraus_family_map \<EE> (tc_butterfly \<phi> \<psi>))) (Rep_kraus_family \<EE>)\<close>
  proof -
    have *: \<open>trace_tc (sandwich_tc E (tc_butterfly \<phi> \<psi>)) = \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>\<close> for E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      by (auto intro!: simp: trace_tc.rep_eq from_trace_class_sandwich_tc
          sandwich_apply tc_butterfly.rep_eq circularity_of_trace[symmetric, of _ E]
          trace_class_comp_left cblinfun_compose_assoc trace_butterfly_comp)
    from kraus_family_map_has_sum Rep_kraus_family[of \<EE>]
    have \<open>((\<lambda>(E,x). sandwich_tc E (tc_butterfly \<phi> \<psi>)) has_sum kraus_family_map \<EE> (tc_butterfly \<phi> \<psi>)) (Rep_kraus_family \<EE>)\<close>
      by blast
    then have \<open>((\<lambda>(E,x). trace_tc (sandwich_tc E (tc_butterfly \<phi> \<psi>))) has_sum trace_tc (kraus_family_map \<EE> (tc_butterfly \<phi> \<psi>))) (Rep_kraus_family \<EE>)\<close>
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

(* lemma kraus_family_kraus_family_comp[intro]:
  fixes \<EE> :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('c::chilbert_space, 'a, 'y) kraus_family\<close>
  (* assumes \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close> *)
  shows \<open>kraus_family (kraus_family_comp \<EE> \<FF>)\<close>
  using assms by (auto intro!: kraus_family_kraus_family_comp_dependent simp: kraus_family_comp_def) *)


lemma kraus_family_map_mono:
  assumes (* \<open>kraus_family \<EE>\<close> and *) \<open>\<rho> \<ge> \<tau>\<close>
  shows \<open>kraus_family_map \<EE> \<rho> \<ge> kraus_family_map \<EE> \<tau>\<close>
  apply (subst diff_ge_0_iff_ge[symmetric])
  apply (subst kraus_family_map_minus_right[symmetric])
  apply (rule kraus_family_map_pos)
  using assms by (subst diff_ge_0_iff_ge)

lemma kraus_family_map_geq_sum:
  assumes (* \<open>kraus_family \<EE>\<close> and *) \<open>\<rho> \<ge> 0\<close> and \<open>M \<subseteq> Rep_kraus_family \<EE>\<close>
  shows \<open>kraus_family_map \<EE> \<rho> \<ge> (\<Sum>(E,_)\<in>M. sandwich_tc E \<rho>)\<close>
proof (cases \<open>finite M\<close>)
  case True
  have *: \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on X\<close> if \<open>X \<subseteq> Rep_kraus_family \<EE>\<close> for X
    apply (rule summable_on_subset_banach[where A=\<open>Rep_kraus_family \<EE>\<close>])
     apply (rule kraus_family_map_summable[unfolded case_prod_unfold])
    using assms that by blast
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
  fixes \<EE> :: \<open>'y \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('c::chilbert_space, 'a, 'y) kraus_family\<close>
  (* assumes kraus\<EE>: \<open>\<And>x. kraus_family (\<EE> x)\<close> and kraus\<FF>: \<open>kraus_family \<FF>\<close> *)
  assumes \<open>bdd_above (range (kraus_family_norm o \<EE>))\<close>
  shows \<open>kraus_family_map (kraus_family_comp_dependent \<EE> \<FF>) \<rho>
      = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. kraus_family_map (\<EE> y) (sandwich_tc F \<rho>))\<close>
proof -
(*   have family: \<open>kraus_family (kraus_family_comp_dependent \<EE> \<FF>)\<close>
    by (auto intro!: kraus_family_kraus_family_comp_dependent assms) *)

  have sum2: \<open>(\<lambda>(F, x). sandwich_tc F \<rho>) summable_on (Rep_kraus_family \<FF>)\<close>
    using kraus_family_map_summable[of \<rho> \<FF>] (* kraus\<FF> *) by (simp add: case_prod_unfold)
  have \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on 
          (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, E, F, x, y)) ` (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
    using kraus_family_map_summable[of _ \<open>kraus_family_comp_dependent \<EE> \<FF>\<close>] assms
    by (simp add: kraus_family_comp_dependent.rep_eq case_prod_unfold)
  then have sum1: \<open>(\<lambda>((F,y), (E,x)). sandwich_tc (E o\<^sub>C\<^sub>L F) \<rho>) summable_on (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
    apply (subst (asm) summable_on_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)

  have \<open>kraus_family_map (kraus_family_comp_dependent \<EE> \<FF>) \<rho>
          = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, E, F, x, y)) ` (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y)). sandwich_tc (fst E) \<rho>)\<close>
    using assms by (simp add: kraus_family_map_def kraus_family_comp_dependent.rep_eq case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((F,y), (E,x))\<in>(SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y)). sandwich_tc (E o\<^sub>C\<^sub>L F) \<rho>)\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. \<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family (\<EE> y). sandwich_tc (E o\<^sub>C\<^sub>L F) \<rho>)\<close>
    apply (subst infsum_Sigma'_banach[symmetric])
    using sum1 by (auto simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. \<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family (\<EE> y). sandwich_tc E (sandwich_tc F \<rho>))\<close>
    by (simp add: sandwich_tc_compose)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. kraus_family_map (\<EE> y) (sandwich_tc F \<rho>))\<close>
    by (simp add: kraus_family_map_def case_prod_unfold)
  finally show ?thesis
    by -
qed

lemma kraus_family_comp_apply:
(*   fixes \<EE> :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space \<times> 'x) set\<close>
    and \<FF> :: \<open>('c::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a \<times> 'y) set\<close>
  assumes \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close> *)
  shows \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) = kraus_family_map \<EE> \<circ> kraus_family_map \<FF>\<close>
proof (rule ext, rename_tac \<rho>)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>

  have sumF: \<open>(\<lambda>(F, y). sandwich_tc F \<rho>) summable_on Rep_kraus_family \<FF>\<close>
    by (rule kraus_family_map_summable)
  have \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) \<rho> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. kraus_family_map \<EE> (sandwich_tc F \<rho>))\<close>
    by (auto intro!: kraus_family_comp_dependent_apply simp: kraus_family_comp_def)
  also have \<open>\<dots> = kraus_family_map \<EE> (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. sandwich_tc F \<rho>)\<close>
    apply (subst infsum_bounded_linear[symmetric, where f=\<open>kraus_family_map \<EE>\<close>])
    using sumF by (auto intro!: bounded_clinear.bounded_linear kraus_family_map_bounded_clinear
        simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (kraus_family_map \<EE> \<circ> kraus_family_map \<FF>) \<rho>\<close>
    by (simp add: o_def kraus_family_map_def case_prod_unfold)
  finally show \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) \<rho> = (kraus_family_map \<EE> \<circ> kraus_family_map \<FF>) \<rho>\<close>
    by -
qed

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

lemma kraus_family_def2:
  \<open>kraus_family \<EE> \<longleftrightarrow> summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE>\<close>
proof (rule iffI)
  assume \<open>kraus_family \<EE>\<close>
  have \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family (Abs_kraus_family \<EE>))\<close>
    using \<open>kraus_family \<EE>\<close> kraus_family_bound_has_sum summable_on_in_def by blast
  with \<open>kraus_family \<EE>\<close> show \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE>\<close>
    by (simp add: Abs_kraus_family_inverse)
next
  assume \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE>\<close>
  then show \<open>kraus_family \<EE>\<close>
    by (auto intro!: summable_wot_bdd_above[where X=\<EE>] positive_cblinfun_squareI simp: kraus_family_def)
qed

lemma kraus_family_def2':
  \<open>kraus_family \<EE> \<longleftrightarrow> (\<lambda>(E,x). Abs_cblinfun_wot (E* o\<^sub>C\<^sub>L E)) summable_on \<EE>\<close>
  apply (transfer' fixing: \<EE>)
  by (simp add: kraus_family_def2)


lift_definition kraus_family_filter :: \<open>('x \<Rightarrow> bool) \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close> is
  \<open>\<lambda>P \<EE>. {(E,x)\<in>\<EE>. P x}\<close>
proof (rename_tac P \<EE>, rule CollectI)
  fix P \<EE>
  assume \<open>\<EE> \<in> Collect kraus_family\<close>
  then have \<open>kraus_family \<EE>\<close>
    by simp
  then show \<open>kraus_family {(E, x). (E, x) \<in> \<EE> \<and> P x}\<close>
    unfolding kraus_family_def
    apply (rule bdd_above_mono2)
    by auto
qed

(*   have snd_sigma: \<open>snd ` (SIGMA (E, y):Collect good. kraus_family_related_ops (filtered y) E)
      = {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> F \<noteq> 0}\<close>
    and inj_snd: \<open>inj_on snd (SIGMA p:Collect good. kraus_family_related_ops (filtered (snd p)) (fst p))\<close>
    and bound_has_sum: \<open>has_sum_in cweak_operator_topology (\<lambda>(E,_). E* o\<^sub>C\<^sub>L E) flattened B\<close>

      and \<open>flattened = {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kraus_family_op_weight (filtered y) E \<and> E \<noteq> 0}\<close>
      and \<open>B = kraus_family_bound \<EE>\<close> 
    where \<open>filtered y = kraus_family_filter (\<lambda>x. f x = y) \<EE>\<close>

 *)
lemma kraus_family_map_outcome_aux:
  fixes f :: \<open>'x \<Rightarrow> 'y\<close> and \<EE> :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
  defines \<open>B \<equiv> kraus_family_bound \<EE>\<close>
  defines \<open>filtered y \<equiv> kraus_family_filter (\<lambda>x. f x = y) \<EE>\<close>
  defines \<open>flattened \<equiv> {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kraus_family_op_weight (filtered y) E \<and> E \<noteq> 0}\<close>
  defines \<open>good \<equiv> (\<lambda>(E,y). (norm E)\<^sup>2 = kraus_family_op_weight (filtered y) E \<and> E \<noteq> 0)\<close>
  shows \<open>has_sum_in cweak_operator_topology (\<lambda>(E,_). E* o\<^sub>C\<^sub>L E) flattened B\<close> (is ?has_sum)
    and \<open>snd ` (SIGMA (E, y):Collect good. kraus_family_related_ops (filtered y) E)
      = {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> F \<noteq> 0}\<close> (is ?snd_sigma)
    and \<open>inj_on snd (SIGMA p:Collect good. kraus_family_related_ops (filtered (snd p)) (fst p))\<close> (is ?inj_snd)
proof -
  have E_inv: \<open>kraus_family_op_weight (filtered y) E \<noteq> 0\<close> if \<open>good (E,y)\<close> for E y
    using that by (auto simp:  good_def)
(*   have E_inv': \<open>kraus_family_op_weight \<EE> E \<noteq> 0\<close> if \<open>good (E,y)\<close> for E y
    using that by (auto simp:  good_def) *)

  show snd_sigma: ?snd_sigma
  proof (intro Set.set_eqI iffI)
    fix Fx
    assume asm: \<open>Fx \<in> snd ` (SIGMA (E, y):Collect good. kraus_family_related_ops (filtered y) E)\<close>
    obtain F x where Fx_def: \<open>Fx = (F,x)\<close> by fastforce
    with asm obtain E y where Fx_rel_E: \<open>(F, x) \<in> kraus_family_related_ops (filtered y) E\<close> and \<open>good (E,y)\<close>
      by auto
    then have \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close>
      by (simp add: kraus_family_related_ops_def filtered_def kraus_family_filter.rep_eq)
    from Fx_rel_E obtain r where \<open>E = r *\<^sub>R F\<close>
      by (smt (verit) kraus_family_related_ops_def mem_Collect_eq prod.sel(1) split_def)
    with \<open>good (E,y)\<close> have \<open>F \<noteq> 0\<close>
      by (simp add: good_def)
    with \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close> show \<open>Fx \<in> {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> F \<noteq> 0}\<close>
      by (simp add: Fx_def)
  next
    fix Fx
    assume asm: \<open>Fx \<in> {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> F \<noteq> 0}\<close>
    obtain F x where Fx_def: \<open>Fx = (F,x)\<close> by fastforce
    from asm have \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close> and \<open>F \<noteq> 0\<close>
      by (auto simp: Fx_def)
    then have [simp]: \<open>kraus_family_op_weight \<EE> F \<noteq> 0\<close>
      by (simp add: kraus_family_op_weight_neq0)
    then have [simp]: \<open>kraus_family_op_weight \<EE> F > 0\<close>
      using kraus_family_op_weight_geq0 
      by (metis less_eq_real_def)
    define E where \<open>E = (sqrt (kraus_family_op_weight (filtered (f x)) F) / norm F) *\<^sub>R F\<close>
    have \<open>good (E,f x)\<close>
      thm  good_def E_def \<open>F \<noteq> 0\<close> kraus_family_op_weight_scale filtered_def
      apply (auto intro!: simp: good_def E_def \<open>F \<noteq> 0\<close> kraus_family_op_weight_scale filtered_def)
       apply (smt (verit, ccfv_threshold) Fx_def Pair_inject asm case_prodD kraus_family_filter.rep_eq kraus_family_op_weight_geq0 kraus_family_op_weight_neq0 kraus_family_op_weight_scale linordered_field_class.divide_pos_pos mem_Collect_eq real_sqrt_gt_zero split_cong zero_less_norm_iff)
      by (smt (verit) Fx_def Pair_inject asm case_prodD kraus_family_filter.rep_eq kraus_family_op_weight_neq0 mem_Collect_eq split_cong)
    have \<open>(F, x) \<in> kraus_family_related_ops (filtered (f x)) E\<close>
      apply (auto intro!: \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close> simp: kraus_family_related_ops_def E_def \<open>F \<noteq> 0\<close>
          filtered_def kraus_family_filter.rep_eq)
      by (smt (verit) Fx_def Pair_inject asm case_prodD kraus_family_filter.rep_eq kraus_family_op_weight_geq0 kraus_family_op_weight_neq0 mem_Collect_eq nice_ordered_field_class.divide_pos_pos real_sqrt_gt_zero split_cong zero_less_norm_iff)

    with \<open>good (E,f x)\<close>
    show \<open>Fx \<in> snd ` (SIGMA (E, y):Collect good. kraus_family_related_ops (filtered y) E)\<close>
      apply (auto intro!: image_eqI[where x=\<open>((E,()),F,x)\<close>] simp: Fx_def filtered_def)
      by force
  qed

  show inj_snd: ?inj_snd
  proof (rule inj_onI)
    fix EFx EFx' :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'y) \<times> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x\<close>
    assume EFx_in: \<open>EFx \<in> (SIGMA p:Collect good. kraus_family_related_ops (filtered (snd p)) (fst p))\<close>
      and EFx'_in: \<open>EFx' \<in> (SIGMA p:Collect good. kraus_family_related_ops (filtered (snd p)) (fst p))\<close>
    assume snd_eq: \<open>snd EFx = snd EFx'\<close>
    obtain E F x y where [simp]: \<open>EFx = ((E,y),F,x)\<close>
      by (metis (full_types) old.unit.exhaust surj_pair)
    obtain E' F' x' y' where [simp]: \<open>EFx' = ((E',y'),(F',x'))\<close> 
      by (metis (full_types) old.unit.exhaust surj_pair)
    from snd_eq have [simp]: \<open>F' = F\<close> and [simp]: \<open>x' = x\<close>
      by auto
    from EFx_in have \<open>good (E,y)\<close> and F_rel_E: \<open>(F, x) \<in> kraus_family_related_ops (filtered y) E\<close>
      by auto
    from EFx'_in have \<open>good (E',y')\<close> and F_rel_E': \<open>(F, x) \<in> kraus_family_related_ops (filtered y') E'\<close>
      by auto
    from \<open>good (E,y)\<close> have \<open>E \<noteq> 0\<close>
      by (simp add: good_def)
    from \<open>good (E',y')\<close> have \<open>E' \<noteq> 0\<close>
      by (simp add: good_def)
    from F_rel_E obtain r where ErF: \<open>E = r *\<^sub>R F\<close> and \<open>r > 0\<close>
      by (auto intro!: simp: kraus_family_related_ops_def)
    from F_rel_E' obtain r' where E'rF: \<open>E' = r' *\<^sub>R F\<close> and \<open>r' > 0\<close>
      by (auto intro!: simp: kraus_family_related_ops_def)

    from EFx_in have \<open>y = f x\<close>
      by (auto intro!: simp: filtered_def kraus_family_related_ops_def kraus_family_filter.rep_eq)
    moreover from EFx'_in have \<open>y' = f x'\<close>
      by (auto intro!: simp: filtered_def kraus_family_related_ops_def kraus_family_filter.rep_eq)
    ultimately have [simp]: \<open>y = y'\<close>
      by simp

    define r'' where \<open>r'' = r' / r\<close>
    with E'rF ErF \<open>E \<noteq> 0\<close>
    have E'_E: \<open>E' = r'' *\<^sub>R E\<close>
      by auto
    with \<open>r' > 0\<close> \<open>r > 0\<close> \<open>E' \<noteq> 0\<close>
    have [simp]: \<open>r'' > 0\<close>
      by (fastforce simp: r''_def)
    from E'_E have \<open>kraus_family_op_weight (filtered y') E' = kraus_family_op_weight (filtered y) E\<close>
      by (simp add: kraus_family_op_weight_scale)
    with \<open>good (E,y)\<close> \<open>good (E',y')\<close> have \<open>(norm E')\<^sup>2 = (norm E)\<^sup>2\<close>
      by (auto intro!: simp: good_def)
    with \<open>E' = r'' *\<^sub>R E\<close>
    have \<open>E' = E\<close>
      using \<open>0 < r''\<close> by force
    then show \<open>EFx = EFx'\<close>
      by simp
  qed

  show ?has_sum
  proof (unfold has_sum_in_cweak_operator_topology_pointwise, intro allI)
    fix \<psi> \<phi> :: 'a
    define B' where \<open>B' = \<psi> \<bullet>\<^sub>C B \<phi>\<close>
    define normal where \<open>normal E y = E /\<^sub>R sqrt (kraus_family_op_weight (filtered y) E)\<close> for E y
    have \<open>has_sum_in cweak_operator_topology (\<lambda>(F,x). F* o\<^sub>C\<^sub>L F) (Rep_kraus_family \<EE>) B\<close>
      using B_def kraus_family_bound_has_sum by blast
    then have \<open>((\<lambda>(F,x). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B') (Rep_kraus_family \<EE>)\<close>
      by (simp add: B'_def has_sum_in_cweak_operator_topology_pointwise case_prod_unfold)
    then have \<open>((\<lambda>(F,x). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B') {(F,x)\<in>Rep_kraus_family \<EE>. F \<noteq> 0}\<close>
      apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
      by (auto simp: zero_cblinfun_wot_def)
    then have \<open>((\<lambda>(F,x). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B')
           (snd ` (SIGMA (E,y):Collect good. kraus_family_related_ops (filtered y) E))\<close>
      by (simp add: snd_sigma)
    then have \<open>((\<lambda>((E,x), (F,y)). \<psi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>) has_sum B')
       (SIGMA (E,y):Collect good. kraus_family_related_ops (filtered y) E)\<close>
      apply (subst (asm) has_sum_reindex)
      by (auto intro!: inj_on_def inj_snd simp: o_def case_prod_unfold)
    then have sum1: \<open>((\<lambda>((E,y), (F,x)). (norm F)\<^sup>2 *\<^sub>R (\<psi> \<bullet>\<^sub>C (normal E y* o\<^sub>C\<^sub>L normal E y) \<phi>)) has_sum B')
        (SIGMA (E,y):Collect good. kraus_family_related_ops (filtered y) E)\<close>
      apply (rule has_sum_cong[THEN iffD2, rotated])
      apply (auto intro!: simp: good_def normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv
          kraus_family_related_ops_def kraus_family_op_weight_scale 
          cblinfun.scaleC_left cblinfun.scaleC_right cinner_scaleC_right scaleR_scaleC) 
      by (smt (verit) Extra_Ordered_Fields.mult_sign_intros(5) Extra_Ordered_Fields.sign_simps(5) inverse_eq_iff_eq left_inverse more_arith_simps(11) of_real_eq_0_iff of_real_mult power2_eq_square power_inverse real_inv_sqrt_pow2 zero_less_norm_iff)
    then have \<open>((\<lambda>(E,y). \<Sum>\<^sub>\<infinity>(F, x)\<in>kraus_family_related_ops (filtered y) E.
                (norm F)\<^sup>2 *\<^sub>R (\<psi> \<bullet>\<^sub>C (normal E y* o\<^sub>C\<^sub>L normal E y) \<phi>)) has_sum B') (Collect good)\<close>
      by (auto intro!: has_sum_Sigma'_banach simp add: case_prod_unfold)
    then have \<open>((\<lambda>(E,y). (\<Sum>\<^sub>\<infinity>(F, x)\<in>kraus_family_related_ops (filtered y) E.
                              (norm F)\<^sup>2) *\<^sub>R (\<psi> \<bullet>\<^sub>C (normal E y* o\<^sub>C\<^sub>L normal E y) \<phi>))
                        has_sum B') (Collect good)\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      apply auto
      by (smt (verit) Complex_Vector_Spaces.infsum_scaleR_left cblinfun.scaleR_left infsum_cong split_def)
    then have \<open>((\<lambda>(E,y). kraus_family_op_weight (filtered y) E *\<^sub>R 
                              (\<psi> \<bullet>\<^sub>C (normal E y* o\<^sub>C\<^sub>L normal E y) \<phi>)) has_sum B') (Collect good)\<close>
      by (simp add: kraus_family_op_weight_def)
    then have \<open>((\<lambda>(E,_). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum B') (Collect good)\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      apply (auto intro!: simp: normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv 
          cblinfun.scaleR_left scaleR_scaleC
          simp flip: inverse_mult_distrib semigroup_mult.mult_assoc)
      by (metis E_inv field_class.field_inverse kraus_family_op_weight_geq0 mult.commute of_real_eq_0_iff of_real_hom.hom_mult power2_eq_square real_sqrt_pow2)
    then have \<open>((\<lambda>(E,_). \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<phi>) has_sum B') flattened\<close>
      by (simp add: flattened_def good_def)
    then show \<open>((\<lambda>x. \<psi> \<bullet>\<^sub>C ((case x of (E, uu_) \<Rightarrow> E* o\<^sub>C\<^sub>L E) *\<^sub>V \<phi>)) has_sum B') flattened\<close>
      by (simp add: case_prod_unfold)
  qed
qed

lift_definition kraus_family_map_outcome :: \<open>('x \<Rightarrow> 'y) \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a, 'b, 'y) kraus_family\<close> is
  \<open>\<lambda>f \<EE>. {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kraus_family_op_weight (kraus_family_filter (\<lambda>x. f x = y) \<EE>) E \<and> E \<noteq> 0}\<close>
proof (rename_tac f \<EE>)
  fix f :: \<open>'x \<Rightarrow> 'y\<close> and \<EE> :: \<open>('a, 'b, 'x) kraus_family\<close>
  define filtered flattened B 
    where \<open>filtered y = kraus_family_filter (\<lambda>x. f x = y) \<EE>\<close>
      (* and \<open>good = (\<lambda>(E,y). (norm E)\<^sup>2 = kraus_family_op_weight (filtered y) E \<and> E \<noteq> 0)\<close> *)
      (* and \<open>good y E \<longleftrightarrow> (norm E)\<^sup>2 = kraus_family_op_weight (filtered y) E \<and> E \<noteq> 0\<close> *)
      and \<open>flattened = {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kraus_family_op_weight (filtered y) E \<and> E \<noteq> 0}\<close>
      and \<open>B = kraus_family_bound \<EE>\<close> 
    for E y

  from kraus_family_map_outcome_aux[of f \<EE>]
  have bound_has_sum: \<open>has_sum_in cweak_operator_topology (\<lambda>(E,_). E* o\<^sub>C\<^sub>L E) flattened B\<close>
    by (simp_all add: filtered_def flattened_def B_def)

  from bound_has_sum show \<open>flattened \<in> Collect kraus_family\<close>
    by (auto simp: kraus_family_def2 summable_on_in_def)
qed

lemma 
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  shows kraus_family_map_outcome_same_map: \<open>kraus_family_map (kraus_family_map_outcome f \<EE>) = kraus_family_map \<EE>\<close>
    and kraus_family_map_outcome_bound: \<open>kraus_family_bound (kraus_family_map_outcome f \<EE>) = kraus_family_bound \<EE>\<close>
    and kraus_family_map_outcome_norm: \<open>kraus_family_norm (kraus_family_map_outcome f \<EE>) = kraus_family_norm \<EE>\<close>
proof (rule ext)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  define filtered good flattened B normal \<sigma>
    where \<open>filtered y = kraus_family_filter (\<lambda>x. f x = y) \<EE>\<close>
      and \<open>good = (\<lambda>(E,y). (norm E)\<^sup>2 = kraus_family_op_weight (filtered y) E \<and> E \<noteq> 0)\<close>
      and \<open>flattened = {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kraus_family_op_weight (filtered y) E \<and> E \<noteq> 0}\<close>
      and \<open>B = kraus_family_bound \<EE>\<close> 
      and \<open>normal E y = E /\<^sub>R sqrt (kraus_family_op_weight (filtered y) E)\<close>
      and \<open>\<sigma> = kraus_family_map \<EE> \<rho>\<close>
    for E y
(*   define good normal \<sigma> B flattened where \<open>good E \<longleftrightarrow> (norm E)\<^sup>2 = kraus_family_op_weight \<EE> E \<and> E \<noteq> 0\<close>
    and \<open>normal E = E /\<^sub>R sqrt (kraus_family_op_weight \<EE> E)\<close>
    and \<open>\<sigma> = kraus_family_map \<EE> \<rho>\<close>
    and \<open>B = kraus_family_bound \<EE>\<close>
    and \<open>flattened = {(E, x::unit). norm (E* o\<^sub>C\<^sub>L E) = kraus_family_op_weight \<EE> E \<and> E \<noteq> 0}\<close>
  for E *)
  have E_inv: \<open>kraus_family_op_weight (filtered y) E \<noteq> 0\<close> if \<open>good (E,y)\<close> for E y
    using that by (auto simp:  good_def)

  from kraus_family_map_outcome_aux[of f \<EE>]
  have snd_sigma: \<open>snd ` (SIGMA (E, y):Collect good. kraus_family_related_ops (filtered y) E)
      = {(F, x). (F, x) \<in> Rep_kraus_family \<EE> \<and> F \<noteq> 0}\<close>
    and inj_snd: \<open>inj_on snd (SIGMA p:Collect good. kraus_family_related_ops (filtered (snd p)) (fst p))\<close>
    and bound_has_sum: \<open>has_sum_in cweak_operator_topology (\<lambda>(E,_). E* o\<^sub>C\<^sub>L E) flattened B\<close>
    by (simp_all add: good_def filtered_def flattened_def B_def)

  show \<open>kraus_family_map (kraus_family_map_outcome f \<EE>) \<rho> = \<sigma>\<close>
  proof -
    have \<open>(\<lambda>(F,x). sandwich_tc F \<rho>) summable_on Rep_kraus_family \<EE>\<close>
      using kraus_family_map_summable by (simp add: case_prod_unfold)
    then have \<open>((\<lambda>(F,x). sandwich_tc F \<rho>) has_sum \<sigma>) (Rep_kraus_family \<EE>)\<close>
      by (simp add: \<sigma>_def kraus_family_map_def split_def)
    then have \<open>((\<lambda>(F,x). sandwich_tc F \<rho>) has_sum \<sigma>) {(F,x)\<in>Rep_kraus_family \<EE>. F \<noteq> 0}\<close>
      apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
      by auto
    then have \<open>((\<lambda>(F,x). sandwich_tc F \<rho>) has_sum \<sigma>)
           (snd ` (SIGMA (E,y):Collect good. kraus_family_related_ops (filtered y) E))\<close>
      by (simp add: snd_sigma)
    then have \<open>((\<lambda>((E,x), (F,y)). sandwich_tc F \<rho>) has_sum \<sigma>)
       (SIGMA (E,y):Collect good. kraus_family_related_ops (filtered y) E)\<close>
      apply (subst (asm) has_sum_reindex)
      by (auto intro!: inj_on_def inj_snd simp: o_def case_prod_unfold)
    then have sum1: \<open>((\<lambda>((E,y), (F,_)). (norm F)\<^sup>2 *\<^sub>R sandwich_tc (normal E y) \<rho>) has_sum \<sigma>)
                (SIGMA (E,y):Collect good. kraus_family_related_ops (filtered y) E)\<close>
      apply (rule has_sum_cong[THEN iffD2, rotated])
      apply (auto intro!: simp: good_def normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv
          kraus_family_related_ops_def kraus_family_op_weight_scale)
      by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(5) linorder_not_less more_arith_simps(11) mult_eq_0_iff norm_le_zero_iff order.refl power2_eq_square right_inverse scale_one)
    then have \<open>((\<lambda>(E,y). \<Sum>\<^sub>\<infinity>(F, x)\<in>kraus_family_related_ops (filtered y) E.
                (norm F)\<^sup>2 *\<^sub>R sandwich_tc (normal E y) \<rho>) has_sum \<sigma>) (Collect good)\<close>
      by (auto intro!: has_sum_Sigma'_banach simp add: case_prod_unfold)
    then have \<open>((\<lambda>(E,y). (\<Sum>\<^sub>\<infinity>(F, x)\<in>kraus_family_related_ops (filtered y) E. (norm F)\<^sup>2) *\<^sub>R sandwich_tc (normal E y) \<rho>)
                        has_sum \<sigma>) (Collect good)\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      apply auto
      by (smt (verit) Complex_Vector_Spaces.infsum_scaleR_left cblinfun.scaleR_left infsum_cong split_def)
    then have \<open>((\<lambda>(E,y). kraus_family_op_weight (filtered y) E *\<^sub>R sandwich_tc (normal E y) \<rho>) has_sum \<sigma>) (Collect good)\<close>
      by (simp add: kraus_family_op_weight_def)
    then have \<open>((\<lambda>(E,_). sandwich_tc E \<rho>) has_sum \<sigma>) (Collect good)\<close>
      apply (rule has_sum_cong[THEN iffD1, rotated])
      by (auto intro!: simp: normal_def sandwich_tc_scaleR_left power_inverse real_sqrt_pow2 E_inv)
    then have \<open>((\<lambda>(E,_). sandwich_tc E \<rho>) has_sum \<sigma>) flattened\<close>
      by (simp add: flattened_def good_def)
    then show \<open>kraus_family_map (kraus_family_map_outcome f \<EE>) \<rho> = \<sigma>\<close>
      by (simp add: kraus_family_map.rep_eq kraus_family_map_outcome.rep_eq flattened_def case_prod_unfold infsumI
          flip: filtered_def)
  qed

  from bound_has_sum show bound: \<open>kraus_family_bound (kraus_family_map_outcome f \<EE>) = B\<close>
    apply (simp add: kraus_family_bound_def flattened_def kraus_family_map_outcome.rep_eq B_def filtered_def)
    using has_sum_in_infsum_in has_sum_in_unique hausdorff_cweak_operator_topology summable_on_in_def
    by blast

  from bound show \<open>kraus_family_norm (kraus_family_map_outcome f \<EE>) = kraus_family_norm \<EE>\<close>
    by (simp add: kraus_family_norm_def B_def)
qed

abbreviation \<open>kraus_family_flatten \<equiv> kraus_family_map_outcome (\<lambda>_. ())\<close>

lift_definition kraus_map_comp :: \<open>('a::chilbert_space,'b::chilbert_space) kraus_map
                                \<Rightarrow> ('c::chilbert_space,'a) kraus_map \<Rightarrow> ('c,'b) kraus_map\<close>
  is \<open>\<lambda>\<EE> \<FF>. kraus_family_flatten (kraus_family_comp \<EE> \<FF>)\<close>
  by (auto intro!: 
      simp add: kraus_equivalent_def kraus_family_comp_apply kraus_family_map_outcome_same_map)

definition \<open>kraus_map_id = kraus_map_of_op id_cblinfun\<close>

lemma kraus_map_norm_id_le: \<open>kraus_map_norm kraus_map_id \<le> 1\<close>
  apply (simp add: kraus_map_id_def)
  apply transfer
  by (auto intro!: power_le_one onorm_pos_le onorm_id_le)

lemma kraus_map_norm_id[simp]: \<open>kraus_map_norm (kraus_map_id :: ('a :: {chilbert_space, not_singleton},'a) kraus_map) = 1\<close>
  by (auto intro!: antisym kraus_map_norm_id_le simp: kraus_map_id_def)

lift_definition kraus_family_plus :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a,'b,'y) kraus_family \<Rightarrow> ('a,'b,'x+'y) kraus_family\<close> is
  \<open>\<lambda>\<EE> \<FF>. (\<lambda>(E,x). (E, Inl x)) ` \<EE> \<union> (\<lambda>(F,y). (F, Inr y)) ` \<FF>\<close>
proof (rename_tac \<EE> \<FF>)
  fix \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x) set\<close> and \<FF> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'y) set\<close>
  assume \<open>\<EE> \<in> Collect kraus_family\<close> and \<open>\<FF> \<in> Collect kraus_family\<close>
  then have \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
    by auto
  then have \<open>kraus_family ((\<lambda>(E, x). (E, Inl x)) ` \<EE> \<union> (\<lambda>(F, y). (F, Inr y)) ` \<FF>)\<close>
    by (auto intro!: summable_on_Un_disjoint 
      summable_on_reindex[THEN iffD2] inj_onI
      simp: kraus_family_def2' o_def case_prod_unfold conj_commute)
  then show \<open>(\<lambda>(E, x). (E, Inl x)) ` \<EE> \<union> (\<lambda>(F, y). (F, Inr y)) ` \<FF> \<in> Collect kraus_family\<close>
    by simp
qed

lemma kraus_family_map_plus:
  fixes \<EE> :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('a, 'b, 'y) kraus_family\<close>
  shows \<open>kraus_family_map (kraus_family_plus \<EE> \<FF>) \<rho> = kraus_family_map \<EE> \<rho> + kraus_family_map \<FF> \<rho>\<close>
proof -
  have \<open>kraus_family_map (kraus_family_plus \<EE> \<FF>) \<rho> = 
    (\<Sum>\<^sub>\<infinity>EF\<in>(\<lambda>(E,x). (E, Inl x)) ` Rep_kraus_family \<EE> \<union> (\<lambda>(F,y). (F, Inr y)) ` Rep_kraus_family \<FF>. sandwich_tc (fst EF) \<rho>)\<close>
    by (simp add: kraus_family_plus.rep_eq kraus_family_map_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>EF\<in>(\<lambda>(E,x). (E, Inl x :: 'x+'y)) ` Rep_kraus_family \<EE>. sandwich_tc (fst EF) \<rho>)
                + (\<Sum>\<^sub>\<infinity>EF\<in>(\<lambda>(F,y). (F, Inr y :: 'x+'y)) ` Rep_kraus_family \<FF>. sandwich_tc (fst EF) \<rho>)\<close>
    apply (subst infsum_Un_disjoint)
    using kraus_family_map_summable
    by (auto intro!: summable_on_reindex[THEN iffD2] inj_onI
        simp: o_def case_prod_unfold kraus_family_map_summable)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>Rep_kraus_family \<EE>. sandwich_tc (fst E) \<rho>) + (\<Sum>\<^sub>\<infinity>F\<in>Rep_kraus_family \<FF>. sandwich_tc (fst F) \<rho>)\<close>
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

lift_definition kraus_family_scale :: \<open>real \<Rightarrow> ('a::chilbert_space,'b::chilbert_space,'x) kraus_family \<Rightarrow> ('a,'b,'x) kraus_family\<close> is
  \<open>\<lambda>r \<EE>. if r \<le> 0 then {} else (\<lambda>(E,x). (sqrt r *\<^sub>R E, x)) ` \<EE>\<close>
proof (rename_tac r \<EE>)
  fix r and \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x) set\<close>
  assume asm: \<open>\<EE> \<in> Collect kraus_family\<close>
  define scaled where \<open>scaled = (\<lambda>(E, y). (sqrt r *\<^sub>R E, y)) ` \<EE>\<close>
  show \<open>(if r \<le> 0 then {} else scaled) \<in> Collect kraus_family\<close>
  proof (cases \<open>r > 0\<close>)
    case True
    obtain B where B: \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>M \<subseteq> \<EE>\<close> and \<open>finite M\<close> for M
      using asm
      by (auto intro!: simp: kraus_family_def bdd_above_def)
    have \<open>(\<Sum>\<^sub>\<infinity>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) \<le> r *\<^sub>R B\<close> if Mr\<EE>: \<open>M \<subseteq> scaled\<close> and \<open>finite M\<close> for M
    proof -
      define M' where \<open>M' = (\<lambda>(E,x). (E /\<^sub>R sqrt r, x)) ` M\<close>
      then have \<open>finite M'\<close>
        using that(2) by blast
      moreover have \<open>M' \<subseteq> \<EE>\<close>
        using Mr\<EE> True by (auto intro!: simp: M'_def scaled_def)
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
      by (simp add: scaled_def)
  qed
qed


lemma kraus_family_scale_map:
  assumes \<open>r \<ge> 0\<close>
  shows \<open>kraus_family_map (kraus_family_scale r \<EE>) \<rho> = r *\<^sub>R kraus_family_map \<EE> \<rho>\<close>
proof (cases \<open>r > 0\<close>)
  case True
  then show ?thesis
    apply (simp add: kraus_family_scale.rep_eq kraus_family_map_def)
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI
        simp: kraus_family_scale_def kraus_family_map_def case_prod_unfold
        o_def sandwich_tc_scaleR_left cblinfun.scaleR_left infsum_scaleR_right)
next
  case False
  with assms show ?thesis
    by (simp add: kraus_family_map.rep_eq kraus_family_scale.rep_eq)
qed

instantiation kraus_map :: (chilbert_space, chilbert_space) \<open>{zero,plus,scaleR}\<close> begin
lift_definition zero_kraus_map :: \<open>('a,'b) kraus_map\<close> is 0.
lift_definition plus_kraus_map :: \<open>('a,'b) kraus_map \<Rightarrow> ('a,'b) kraus_map \<Rightarrow> ('a,'b) kraus_map\<close> is
  \<open>\<lambda>\<EE> \<FF>. kraus_family_flatten (kraus_family_plus \<EE> \<FF>)\<close>
  by (auto simp: kraus_family_map_plus  kraus_equivalent_def kraus_family_comp_apply kraus_family_map_outcome_same_map)
lift_definition scaleR_kraus_map :: \<open>real \<Rightarrow> ('a,'b) kraus_map \<Rightarrow> ('a,'b) kraus_map\<close> is
  kraus_family_scale
proof (unfold kraus_equivalent_def)
  fix r :: real and \<EE> \<FF> :: \<open>('a, 'b, unit) kraus_family\<close>
  assume \<open>kraus_family_map \<EE> = kraus_family_map \<FF>\<close>
  then show \<open>kraus_family_map (kraus_family_scale r \<EE>) = kraus_family_map (kraus_family_scale r \<FF>)\<close>
    apply (cases \<open>r < 0\<close>)
     apply (simp add: kraus_family_scale_def)
    by (auto intro!: ext simp: kraus_family_scale_map)
qed
instance..
end


instantiation kraus_map :: (chilbert_space, chilbert_space) comm_monoid_add begin
instance
proof intro_classes
  fix a b c :: \<open>('a, 'b) kraus_map\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer
    by (auto intro!: ext
        simp add: kraus_equivalent_def kraus_family_map_outcome_same_map kraus_family_map_plus)
  show \<open>a + b = b + a\<close>
    apply transfer
    by (auto intro!: ext
        simp add: kraus_equivalent_def kraus_family_map_outcome_same_map kraus_family_map_plus)
  show \<open>0 + a = a\<close>
    apply transfer
    by (auto intro!: ext
        simp add: kraus_equivalent_def kraus_family_map_outcome_same_map kraus_family_map_plus)
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
  by (simp add: kraus_family_map_def kraus_family_of_op.rep_eq)


lemma kraus_map_of_op_apply: \<open>kraus_map_apply (kraus_map_of_op E) \<rho> = sandwich_tc E \<rho>\<close>
  apply (transfer' fixing: \<rho>)
  by (simp add: kraus_family_of_op_apply)

lemma kraus_map_id_apply[simp]: \<open>kraus_map_apply kraus_map_id \<rho> = \<rho>\<close>
  by (simp add: kraus_map_id_def kraus_map_of_op_apply)

(* lemma kraus_family_rep_kraus_map[simp]: \<open>kraus_family (rep_kraus_map \<EE>)\<close>
  using Quotient_rep_reflp[OF Quotient_kraus_map]
  by (auto simp add: kraus_equivalent_def) *)

lemma kraus_map_scaleR:
  assumes \<open>r \<ge> 0\<close>
  shows \<open>kraus_map_apply (r *\<^sub>R \<EE>) \<rho> = r *\<^sub>R kraus_map_apply \<EE> \<rho>\<close>
proof -
  have \<open>kraus_map_apply (r *\<^sub>R \<EE>) \<rho> = kraus_family_map (kraus_family_scale r (rep_kraus_map \<EE>)) \<rho>\<close>
    by (simp add: scaleR_kraus_map_def kraus_map_apply.abs_eq kraus_equivalent_reflI)
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
  by (auto intro!: ext simp: kraus_family_scale.rep_eq kraus_family_map.rep_eq)

lemma kraus_map_norm_0[simp]: \<open>kraus_map_norm 0 = 0\<close>
  apply transfer by simp



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
  by (simp add: kraus_equivalent_def kraus_family_map_outcome_same_map kraus_family_comp_apply)

lemma kraus_map_comp_assoc: \<open>kraus_map_comp (kraus_map_comp E F) G = kraus_map_comp E (kraus_map_comp F G)\<close>
  apply (rule kraus_map_apply_inj)
  by (simp add: kraus_map_apply_comp o_def)

(* Could be renamed complete measurement *)
lift_definition trace_kraus_family :: \<open>'a set \<Rightarrow> ('a::chilbert_space, 'b::one_dim, 'a) kraus_family\<close> is
  \<open>\<lambda>B. if is_onb B then (\<lambda>x. (vector_to_cblinfun x*, x)) ` B else {}\<close>
proof (rename_tac B)
  fix B :: \<open>'a set\<close>
  define family :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'a) set\<close> where \<open>family = (\<lambda>x. (vector_to_cblinfun x*, x)) ` B\<close>
  have \<open>kraus_family family\<close> if \<open>is_onb B\<close>
  proof -
    have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> id_cblinfun\<close> if \<open>finite F\<close> and FB: \<open>F \<subseteq> family\<close> for F :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'a) set\<close>
    proof -
      obtain G where \<open>finite G\<close> and \<open>G \<subseteq> B\<close> and FG: \<open>F = (\<lambda>x. (vector_to_cblinfun x*, x)) ` G\<close>
        apply atomize_elim
        using \<open>finite F\<close> and FB
        apply (simp add: family_def)
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
  then
  show \<open>(if is_onb B then family else {}) \<in> Collect kraus_family\<close>
    by auto
qed


lemma trace_kraus_family_is_trace: 
  assumes \<open>is_onb B\<close>
  shows \<open>kraus_family_map (trace_kraus_family B) \<rho> = one_dim_iso (trace_tc \<rho>)\<close>
proof -
  define \<rho>' where \<open>\<rho>' = from_trace_class \<rho>\<close>
  have \<open>kraus_family_map (trace_kraus_family B) \<rho> = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (vector_to_cblinfun x*) \<rho>)\<close>
    apply (simp add: kraus_family_map.rep_eq trace_kraus_family.rep_eq assms)
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
  by (auto simp: kraus_equivalent_def trace_kraus_family_is_trace assms)

lift_definition trace_kraus_map :: \<open>('a::chilbert_space, 'b::one_dim) kraus_map\<close> is
  \<open>kraus_family_flatten (trace_kraus_family some_chilbert_basis)\<close>.

lemma trace_kraus_map_is_trace: \<open>kraus_map_apply trace_kraus_map \<rho> = one_dim_iso (trace_tc \<rho>)\<close>
  apply (transfer' fixing: \<rho>)
  by (simp add: kraus_family_map_outcome_same_map trace_kraus_family_is_trace)

definition \<open>trace_preserving \<EE> \<longleftrightarrow> (\<forall>\<rho>. trace_tc (kraus_map_apply \<EE> \<rho>) = trace_tc \<rho>)\<close>

lemma trace_preserving_id[iff]: \<open>trace_preserving kraus_map_id\<close>
  by (simp add: trace_preserving_def trace_kraus_map_is_trace)

lemma trace_preserving_trace_kraus_map[iff]: \<open>trace_preserving trace_kraus_map\<close>
  by (simp add: trace_preserving_def trace_kraus_map_is_trace)

lemma kraus_equivalent_kraus_family_map_outcome_left: \<open>kraus_equivalent (kraus_family_flatten F) G\<close> if \<open>kraus_equivalent F G\<close>
  using that by (simp add: kraus_equivalent_def kraus_family_map_outcome_same_map)
lemma kraus_equivalent_kraus_family_map_outcome_right: \<open>kraus_equivalent F (kraus_family_flatten G)\<close> if \<open>kraus_equivalent F G\<close>
  using that by (simp add: kraus_equivalent_def kraus_family_map_outcome_same_map)

lemma kraus_family_comp_cong: \<open>kraus_equivalent (kraus_family_comp F G) (kraus_family_comp F' G')\<close>
  if \<open>kraus_equivalent F F'\<close> and \<open>kraus_equivalent G G'\<close>
  by (metis kraus_equivalent_def kraus_family_comp_apply that(1) that(2))

lemma kraus_equivalent_trans[trans]:
  \<open>kraus_equivalent F G \<Longrightarrow> kraus_equivalent G H \<Longrightarrow> kraus_equivalent F H\<close>
  by (simp add: kraus_equivalent_def)

lift_definition kraus_family_tensor :: \<open>('a ell2, 'b ell2, 'x) kraus_family \<Rightarrow> ('c ell2, 'd ell2, 'y) kraus_family \<Rightarrow> 
          (('a\<times>'c) ell2, ('b\<times>'d) ell2, (('a ell2\<Rightarrow>\<^sub>C\<^sub>L'b ell2)\<times>('c ell2\<Rightarrow>\<^sub>C\<^sub>L'd ell2)\<times>'x\<times>'y)) kraus_family\<close> is
  \<open>\<lambda>\<EE> \<FF>. (\<lambda>((E,x), (F,y)). (E \<otimes>\<^sub>o F, (E,F,x,y))) ` (\<EE>\<times>\<FF>)\<close>
proof (rename_tac \<EE> \<FF>, intro CollectI)
  fix \<EE> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'x) set\<close> and \<FF> :: \<open>('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2 \<times> 'y) set\<close>
  assume \<open>\<EE> \<in> Collect kraus_family\<close> and \<open>\<FF> \<in> Collect kraus_family\<close>
  then have \<open>kraus_family \<EE>\<close> and \<open>kraus_family \<FF>\<close>
    by auto
  define tensor where \<open>tensor = ((\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)) ` (\<EE> \<times> \<FF>))\<close>
  show \<open>kraus_family tensor\<close>
  proof (intro kraus_familyI)
    from \<open>kraus_family \<EE>\<close>
    obtain B where B: \<open>(\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>finite S\<close> and \<open>S \<subseteq> \<EE>\<close> for S
      apply atomize_elim
      by (auto simp: kraus_family_def bdd_above_def)
    from B[where S=\<open>{}\<close>] have [simp]: \<open>B \<ge> 0\<close>
      by simp
    from \<open>kraus_family \<FF>\<close>
    obtain C where C: \<open>(\<Sum>(F, x)\<in>T. F* o\<^sub>C\<^sub>L F) \<le> C\<close> if \<open>finite T\<close> and \<open>T \<subseteq> \<FF>\<close> for T
      apply atomize_elim
      by (auto simp: kraus_family_def bdd_above_def)
    have \<open>(\<Sum>(G, z)\<in>U. G* o\<^sub>C\<^sub>L G) \<le> B \<otimes>\<^sub>o C\<close> if \<open>finite U\<close> and \<open>U \<subseteq> tensor\<close> for U
    proof -
      define f :: \<open>(('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'x) \<times> ('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2 \<times> 'y)) \<Rightarrow> _\<close>
        where \<open>f = (\<lambda>((E,x), (F,y)). (E \<otimes>\<^sub>o F, (E,F,x,y)))\<close>
      from that
      obtain V where V_subset: \<open>V \<subseteq> \<EE> \<times> \<FF>\<close> and [simp]: \<open>finite V\<close> and \<open>U = f ` V\<close>
        apply (simp only: tensor_def flip: f_def)
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
    then show \<open>bdd_above ((\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> tensor})\<close>
      by fast
  qed
qed

lemma kraus_family_map_tensor:
  shows \<open>kraus_family_map (kraus_family_tensor \<EE> \<FF>) (tc_tensor \<rho> \<sigma>) = tc_tensor (kraus_family_map \<EE> \<rho>) (kraus_family_map \<FF> \<sigma>)\<close>
proof -
  have inj: \<open>inj_on (\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)) (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>)\<close>
    by (auto intro!: inj_onI)
  have [simp]: \<open>bounded_linear (\<lambda>x. tc_tensor x (kraus_family_map \<FF> \<sigma>))\<close>
    by (intro bounded_linear_intros)
  have [simp]: \<open>bounded_linear (tc_tensor (sandwich_tc E \<rho>))\<close> for E
    by (intro bounded_linear_intros)
  have sum2: \<open>(\<lambda>(E, x). sandwich_tc E \<rho>) summable_on Rep_kraus_family \<EE>\<close>
    using kraus_family_map_summable by blast
  have sum3: \<open>(\<lambda>(F, y). sandwich_tc F \<sigma>) summable_on Rep_kraus_family \<FF>\<close>
    using kraus_family_map_summable by blast

  from kraus_family_map_summable[of _ \<open>kraus_family_tensor \<EE> \<FF>\<close>]
  have sum1: \<open>(\<lambda>((E, x), F, y). sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>)) summable_on Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>\<close>
    apply (simp add: kraus_family_map.rep_eq kraus_family_tensor.rep_eq summable_on_reindex inj o_def)
    by (simp add: case_prod_unfold)

  have \<open>kraus_family_map (kraus_family_tensor \<EE> \<FF>) (tc_tensor \<rho> \<sigma>)
      = (\<Sum>\<^sub>\<infinity>((E,x),(F,y))\<in>Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>))\<close>
    apply (simp add: kraus_family_map.rep_eq kraus_family_tensor.rep_eq infsum_reindex inj o_def)
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. \<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>))\<close>
    apply (subst infsum_Sigma_banach[symmetric])
    using sum1 by (auto intro!: simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. \<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. tc_tensor (sandwich_tc E \<rho>) (sandwich_tc F \<sigma>))\<close>
    by (simp add: sandwich_tc_tensor)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. tc_tensor (sandwich_tc E \<rho>) (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. (sandwich_tc F \<sigma>)))\<close>
    apply (subst infsum_bounded_linear[where f=\<open>tc_tensor (sandwich_tc _ \<rho>)\<close>, symmetric])
      apply (auto intro!: sum3)[2]
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. tc_tensor (sandwich_tc E \<rho>) (kraus_family_map \<FF> \<sigma>))\<close>
    by (simp add: kraus_family_map_def case_prod_unfold)
  also have \<open>\<dots> = tc_tensor (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. sandwich_tc E \<rho>) (kraus_family_map \<FF> \<sigma>)\<close>
    apply (subst infsum_bounded_linear[where f=\<open>\<lambda>x. tc_tensor x (kraus_family_map \<FF> \<sigma>)\<close>, symmetric])
      apply (auto intro!: sum2)[2]
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = tc_tensor (kraus_family_map \<EE> \<rho>) (kraus_family_map \<FF> \<sigma>)\<close>
    by (simp add: kraus_family_map_def case_prod_unfold)
  finally show ?thesis
    by -
qed



lemma kraus_tensor_cong:
  assumes \<open>kraus_equivalent \<EE> \<EE>'\<close>
  assumes \<open>kraus_equivalent \<FF> \<FF>'\<close>
  shows \<open>kraus_equivalent (kraus_family_tensor \<EE> \<FF>) (kraus_family_tensor \<EE>' \<FF>')\<close>
proof (intro kraus_equivalent_def[THEN iffD2] conjI)
  show \<open>kraus_family_map (kraus_family_tensor \<EE> \<FF>) = kraus_family_map (kraus_family_tensor \<EE>' \<FF>')\<close>
  proof (rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
    show \<open>bounded_clinear (kraus_family_map (kraus_family_tensor \<EE> \<FF>))\<close>
      by (simp add: kraus_family_map_bounded_clinear)
    show \<open>bounded_clinear (kraus_family_map (kraus_family_tensor \<EE>' \<FF>'))\<close>
      by (simp add: kraus_family_map_bounded_clinear)
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
  by (intro kraus_equivalent_kraus_family_map_outcome_left kraus_equivalent_kraus_family_map_outcome_right kraus_tensor_cong)

lemma kraus_map_tensor:
  shows \<open>kraus_map_apply (kraus_map_tensor \<EE> \<FF>) (tc_tensor \<rho> \<sigma>) = tc_tensor (kraus_map_apply \<EE> \<rho>) (kraus_map_apply \<FF> \<sigma>)\<close>
  apply (transfer fixing: \<rho> \<sigma>)
  by (simp add: kraus_equivalent_def kraus_family_map_outcome_same_map kraus_family_map_tensor)

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
  by (simp add: kraus_family_map_outcome_same_map trace_kraus_family_is_trace)

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
