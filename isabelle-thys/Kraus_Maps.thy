theory Kraus_Maps
  imports Tensor_Product.Trace_Class Registers2.Missing_Bounded_Operators Wlog.Wlog "HOL-Library.Rewrite"
begin

no_notation  Order.top ("\<top>\<index>")
no_notation   eq_closure_of ("closure'_of\<index>")

unbundle cblinfun_notation

definition \<open>kraus_family \<EE> \<longleftrightarrow> bdd_above ((\<lambda>F. \<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> \<EE>})\<close>
  for \<EE> :: \<open>((_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space) \<times> _) set\<close>

typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family = 
  \<open>Collect kraus_family :: (('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<times> 'x) set set\<close>
  by (rule exI[of _ \<open>{}\<close>], auto simp: kraus_family_def)
setup_lifting type_definition_kraus_family

lift_definition kraus_family_bound :: \<open>('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close> is
  \<open>\<lambda>\<EE>. infsum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) \<EE>\<close> .

lemma kraus_family_bound_def':
  \<open>kraus_family_bound \<EE> = Rep_cblinfun_wot (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. cblinfun_compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
  unfolding kraus_family_bound.rep_eq infsum_euclidean_eq[symmetric]
  apply transfer'
  by simp


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

lemma kraus_family_norm_geq0[iff]:
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

lemma kraus_family_bound_summable:
  shows \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>)\<close>
  using kraus_family_bound_has_sum summable_on_in_def by blast

lemma kraus_family_bound_has_sum':
  shows \<open>((\<lambda>(E,x). cblinfun_compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) has_sum Abs_cblinfun_wot (kraus_family_bound \<EE>)) (Rep_kraus_family \<EE>)\<close>
  using kraus_family_bound_has_sum[of \<EE>]
  apply transfer'
  by auto

lemma kraus_family_bound_summable':
  \<open>((\<lambda>(E,x). cblinfun_compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) summable_on Rep_kraus_family \<EE>)\<close>
  using has_sum_imp_summable kraus_family_bound_has_sum' by blast


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

lemma kraus_family_bound_leqI:
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
  shows \<open>kraus_family_bound \<EE> \<le> B\<close>
  using kraus_family_Sup[of \<EE>]
  by (simp add: assms is_Sup_def)

lemma kraus_family_bound_pos[simp]: \<open>kraus_family_bound \<EE> \<ge> 0\<close>
  using kraus_family_Sup[of \<EE>]
  by (metis (no_types, lifting) empty_subsetI finite.emptyI image_iff is_Sup_def mem_Collect_eq sum.empty)


lemma not_not_singleton_kraus_family_norm: 
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  assumes \<open>\<not> class.not_singleton TYPE('a)\<close>
  shows \<open>kraus_family_norm \<EE> = 0\<close>
  by (simp add: not_not_singleton_cblinfun_zero[OF assms] kraus_family_norm_def)


lemma kraus_family_norm_leqI:
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> norm (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
  shows \<open>kraus_family_norm \<EE> \<le> B\<close>
proof -
  have bpos: \<open>B \<ge> 0\<close>
    using assms[of \<open>{}\<close>] by auto
  wlog not_singleton: \<open>class.not_singleton TYPE('a)\<close> keeping bpos
    using not_not_singleton_kraus_family_norm[OF negation, of \<EE>]
    by (simp add: \<open>B \<ge> 0\<close>)
  have [simp]: \<open>norm (id_cblinfun :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a) = 1\<close>
    apply (rule norm_cblinfun_id[internalize_sort' 'a])
     apply (rule complex_normed_vector_axioms)
    by (rule not_singleton)
  have *: \<open>selfadjoint (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close> for F :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'c) set\<close>
    apply (auto intro!: pos_imp_selfadjoint sum_nonneg)
    using positive_cblinfun_squareI by blast
  from assms
  have \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> Rep_kraus_family \<EE> \<Longrightarrow> (\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B *\<^sub>R id_cblinfun\<close>
    apply (rule less_eq_scaled_id_norm)
    by (auto intro!: * )
  then have \<open>kraus_family_bound \<EE> \<le> B *\<^sub>R id_cblinfun\<close>
    using kraus_family_bound_leqI by blast
  then have \<open>norm (kraus_family_bound \<EE>) \<le> norm (B *\<^sub>R (id_cblinfun :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a))\<close>
    apply (rule norm_cblinfun_mono[rotated])
    by simp
  then show ?thesis
    using bpos by (simp add: kraus_family_norm_def)
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

lemma kraus_family_op_weight_0_left[simp]: \<open>kraus_family_op_weight 0 E = 0\<close>
  by (simp add: kraus_family_op_weight_def kraus_family_related_ops_def zero_kraus_family.rep_eq)

lemma kraus_family_op_weight_0_right[simp]: \<open>kraus_family_op_weight E 0 = 0\<close>
  by (auto intro!: infsum_0 simp add: kraus_family_op_weight_def kraus_family_related_ops_def)

lift_definition kraus_family_filter :: \<open>('x \<Rightarrow> bool) \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close> is
  \<open>\<lambda>(P::'x \<Rightarrow> bool) \<EE>. Set.filter (\<lambda>(E,x). P x) \<EE>\<close>
proof (rename_tac P \<EE>, rule CollectI)
  fix P \<EE>
  assume \<open>\<EE> \<in> Collect kraus_family\<close>
  then have \<open>kraus_family \<EE>\<close>
    by simp
  then show \<open>kraus_family (Set.filter P \<EE>)\<close>
    unfolding kraus_family_def
    apply (rule bdd_above_mono2)
    by auto
qed

lemma kraus_family_filter_false[simp]: \<open>kraus_family_filter (\<lambda>_. False) \<EE> = 0\<close>
  apply transfer by auto

lemma kraus_family_filter_true[simp]: \<open>kraus_family_filter (\<lambda>_. True) \<EE> = \<EE>\<close>
  apply transfer by auto

definition \<open>kraus_family_map' S \<EE> = kraus_family_map (kraus_family_filter (\<lambda>x. x \<in> S) \<EE>)\<close>

definition \<open>kraus_equivalent \<EE> \<FF> \<longleftrightarrow> kraus_family_map \<EE> = kraus_family_map \<FF>\<close>
definition \<open>kraus_equivalent' \<EE> \<FF> \<longleftrightarrow> (\<forall>x. kraus_family_map' {x} \<EE> = kraus_family_map' {x} \<FF>)\<close>

lemma kraus_equivalent_reflI: \<open>kraus_equivalent x x\<close>
  by (simp add: kraus_equivalent_def)

lemma kraus_equivalentI: 
  assumes \<open>\<And>\<rho>. kraus_family_map \<EE> \<rho> = kraus_family_map \<FF> \<rho>\<close>
  shows \<open>kraus_equivalent \<EE> \<FF>\<close>
  using assms by (auto simp: kraus_equivalent_def)

lemma kraus_equivalent'I: 
  assumes \<open>\<And>x \<rho>. kraus_family_map' {x} \<EE> \<rho> = kraus_family_map' {x} \<FF> \<rho>\<close>
  shows \<open>kraus_equivalent' \<EE> \<FF>\<close>
  using assms by (auto simp: kraus_equivalent'_def)


(* lemma kraus_family_zero[simp]: \<open>kraus_family {}\<close>
  by (auto simp: kraus_family_def) *)

(* TODO define map function? *)
(* quotient_type (overloaded) ('a,'b) kraus_map = \<open>('a::chilbert_space, 'b::chilbert_space, unit) kraus_family\<close> / kraus_equivalent
  by (auto intro!: equivpI exI[of _ \<open>{}\<close>] reflpI sympI transpI simp: kraus_equivalent_def) *)

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
  apply (simp add: kraus_family_norm_def zero_kraus_family.rep_eq)
  by (metis (mono_tags, lifting) finite.intros(1) kraus_family_bound.rep_eq kraus_family_bound_finite sum_clauses(1) zero_kraus_family.rep_eq)

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

(* lift_definition kraus_map_of_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> ('a,'b) kraus_map\<close>
  is kraus_family_of_op. *)


lemma kraus_family_map_scaleC:
  shows \<open>kraus_family_map \<EE> (c *\<^sub>C x) = c *\<^sub>C kraus_family_map \<EE> x\<close>
  by (simp add: kraus_family_map_def cblinfun.scaleC_right case_prod_unfold sandwich_tc_scaleC_right
      flip: infsum_scaleC_right)

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

lemma kraus_family_map'_pos:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kraus_family_map' X \<EE> \<rho> \<ge> 0\<close>
  by (simp add: kraus_family_map'_def kraus_family_map_pos assms)

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

lemma kraus_family_map_bounded_clinear[bounded_clinear]:
  shows \<open>bounded_clinear (kraus_family_map \<EE>)\<close>
  apply (rule bounded_clinearI[where K=\<open>4 * kraus_family_norm \<EE>\<close>])
    apply (auto intro!: kraus_family_map_plus_right kraus_family_map_scaleC
      mult.commute)
  using kraus_family_map_bounded
  by (simp add: mult.commute)

lemma kraus_family_map'_bounded_clinear[bounded_clinear]:
  shows \<open>bounded_clinear (kraus_family_map' X \<EE>)\<close>
  by (simp add: kraus_family_map'_def kraus_family_map_bounded_clinear)

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

(* lift_definition kraus_map_norm :: \<open>('a::chilbert_space, 'b::chilbert_space) kraus_map \<Rightarrow> real\<close> is
  kraus_family_norm
  by (rule kraus_family_norm_welldefined) *)

(* lemma kraus_map_of_op_norm[simp]:
  \<open>kraus_map_norm (kraus_map_of_op E) = (norm E)\<^sup>2\<close>
  apply (transfer fixing: E)
  by simp *)

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
    from asm have Fx_\<EE>: \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close> and [simp]: \<open>F \<noteq> 0\<close>
      by (auto simp: Fx_def)
    have weight_fx_F_not0: \<open>kraus_family_op_weight (filtered (f x)) F \<noteq> 0\<close>
      using Fx_\<EE> by (simp_all add: filtered_def kraus_family_filter.rep_eq kraus_family_op_weight_neq0)
    then have weight_fx_F_pos: \<open>kraus_family_op_weight (filtered (f x)) F > 0\<close>
      using kraus_family_op_weight_geq0 
      by (metis less_eq_real_def)
    define E where \<open>E = (sqrt (kraus_family_op_weight (filtered (f x)) F) / norm F) *\<^sub>R F\<close>
    have [simp]: \<open>E \<noteq> 0\<close>
      by (auto intro!: weight_fx_F_not0 simp: E_def)
    have E_F_same: \<open>kraus_family_op_weight (filtered (f x)) E = kraus_family_op_weight (filtered (f x)) F\<close>
      by (simp add: E_def kraus_family_op_weight_scale weight_fx_F_pos)
    have \<open>good (E, f x)\<close>
      apply (simp add: good_def E_F_same)
      by (simp add: E_def)
    have 1: \<open>sqrt (kraus_family_op_weight (filtered (f x)) F) / norm F > 0\<close>
      by (auto intro!: divide_pos_pos weight_fx_F_pos)
    then have \<open>(F, x) \<in> kraus_family_related_ops (filtered (f x)) E\<close>
      by (auto intro!: \<open>(F, x) \<in> Rep_kraus_family \<EE>\<close> simp: kraus_family_related_ops_def E_def \<open>F \<noteq> 0\<close>
         filtered_def kraus_family_filter.rep_eq)
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
    for y

  from kraus_family_map_outcome_aux[of f \<EE>]
  have bound_has_sum: \<open>has_sum_in cweak_operator_topology (\<lambda>(E,_). E* o\<^sub>C\<^sub>L E) flattened B\<close>
    by (simp_all add: filtered_def flattened_def B_def)

  from bound_has_sum show \<open>flattened \<in> Collect kraus_family\<close>
    by (auto simp: kraus_family_def2 summable_on_in_def)
qed

lemma 
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  shows kraus_family_map_outcome_same_map[simp]: \<open>kraus_family_map (kraus_family_map_outcome f \<EE>) = kraus_family_map \<EE>\<close>
    and kraus_family_map_outcome_bound: \<open>kraus_family_bound (kraus_family_map_outcome f \<EE>) = kraus_family_bound \<EE>\<close>
    and kraus_family_map_outcome_norm[simp]: \<open>kraus_family_norm (kraus_family_map_outcome f \<EE>) = kraus_family_norm \<EE>\<close>
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
      by (simp add: kraus_family_map.rep_eq kraus_family_map_outcome.rep_eq flattened_def
          case_prod_unfold infsumI filtered_def)
  qed

  from bound_has_sum show bound: \<open>kraus_family_bound (kraus_family_map_outcome f \<EE>) = B\<close>
    apply (simp add: kraus_family_bound_def flattened_def kraus_family_map_outcome.rep_eq B_def filtered_def)
    using has_sum_in_infsum_in has_sum_in_unique hausdorff_cweak_operator_topology summable_on_in_def
    by blast

  from bound show \<open>kraus_family_norm (kraus_family_map_outcome f \<EE>) = kraus_family_norm \<EE>\<close>
    by (simp add: kraus_family_norm_def B_def)
qed

abbreviation \<open>kraus_family_flatten \<equiv> kraus_family_map_outcome (\<lambda>_. ())\<close>

text \<open>Like \<^const>\<open>kraus_family_map_outcome\<close>, but with a much simpler definition.
      However, only makes sense for injective functions.\<close>
lift_definition kraus_family_map_outcome_inj :: \<open>('x \<Rightarrow> 'y) \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family \<Rightarrow> ('a, 'b, 'y) kraus_family\<close> is
  \<open>\<lambda>f \<EE>. (\<lambda>(E,x). (E, f x)) ` \<EE>\<close>
proof (rule CollectI, rule kraus_familyI, rename_tac f \<EE>)
  fix f :: \<open>'x \<Rightarrow> 'y\<close> and \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'x) set\<close>
  assume \<open>\<EE> \<in> Collect kraus_family\<close>
  then obtain B where B: \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>F \<in> {F. finite F \<and> F \<subseteq> \<EE>}\<close> for F
    by (auto simp: kraus_family_def bdd_above_def)
  show \<open>bdd_above ((\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> (\<lambda>(E, x). (E, f x)) ` \<EE>})\<close>
  proof (rule bdd_aboveI2)
    fix F assume \<open>F \<in> {F. finite F \<and> F \<subseteq> (\<lambda>(E, x). (E, f x)) ` \<EE>}\<close>
    then obtain F' where \<open>finite F'\<close> and \<open>F' \<subseteq> \<EE>\<close> and F_F': \<open>F = (\<lambda>(E, x). (E, f x)) ` F'\<close>
      and inj: \<open>inj_on (\<lambda>(E, x). (E, f x)) F'\<close>
      by (metis (no_types, lifting) finite_imageD mem_Collect_eq subset_image_inj)
    have \<open>(\<Sum>(E, x)\<in>F'. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
      by (auto intro!: B \<open>finite F'\<close> \<open>F' \<subseteq> \<EE>\<close>)
    moreover have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> (\<Sum>(E, x)\<in>F'. E* o\<^sub>C\<^sub>L E)\<close>
      apply (simp add: F_F' inj sum.reindex)
      by (simp add: case_prod_beta)
    ultimately show \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
      by simp
  qed
qed                              

lemma selfadjoint_kraus_family_bound[iff]: \<open>selfadjoint (kraus_family_bound \<EE>)\<close>
  by (simp add: positive_hermitianI selfadjoint_def)

lemma kraus_family_bound_leq_norm:
  shows \<open>kraus_family_bound \<EE> \<le> kraus_family_norm \<EE> *\<^sub>R id_cblinfun\<close>
  by (auto intro!: less_eq_scaled_id_norm simp: kraus_family_norm_def)

lemma kraus_family_comp_dependent_raw_norm_aux:
  assumes B: \<open>\<And>x. kraus_family_norm (\<EE> x) \<le> B\<close>
  assumes \<open>finite C\<close>
  assumes C_subset: \<open>C \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
  shows \<open>(\<Sum>(E,x)\<in>C. E* o\<^sub>C\<^sub>L E) \<le> (B * kraus_family_norm \<FF>) *\<^sub>R id_cblinfun\<close>
proof -
  define BF :: \<open>'e \<Rightarrow>\<^sub>C\<^sub>L 'e\<close> where \<open>BF = kraus_family_norm \<FF> *\<^sub>R id_cblinfun\<close>
  then have \<open>kraus_family_bound \<FF> \<le> BF\<close>
    by (simp add: kraus_family_bound_leq_norm)
  then have BF: \<open>(\<Sum>(F, y)\<in>M. (F* o\<^sub>C\<^sub>L F)) \<le> BF\<close> if \<open>M \<subseteq> Rep_kraus_family \<FF>\<close> and \<open>finite M\<close> for M
    using dual_order.trans kraus_family_sums_bounded_by_bound that(1) by blast
  define BE :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>BE = B *\<^sub>R id_cblinfun\<close>
  define \<FF>x\<EE> where \<open>\<FF>x\<EE> = (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
  from B
  have BE: \<open>(\<Sum>(E, x)\<in>M. (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> if \<open>M \<subseteq> Rep_kraus_family (\<EE> y)\<close> and \<open>finite M\<close> for M y
    using that
    using kraus_family_sums_bounded_by_norm[of _ \<open>\<EE> _\<close>]
    apply (auto intro!: simp: BE_def case_prod_beta)
    by (smt (verit) adj_0 comparable_hermitean selfadjoint_def less_eq_scaled_id_norm positive_cblinfun_squareI 
        scaleR_scaleC sum_nonneg)
  have [simp]: \<open>B \<ge> 0\<close>
    using kraus_family_norm_geq0[of \<open>\<EE> undefined\<close>] B[of undefined]
    by (auto simp del: kraus_family_norm_geq0)

  define A where \<open>A = (\<Sum>(E,x)\<in>C. E* o\<^sub>C\<^sub>L E)\<close>
  define CE CF where \<open>CE y = (\<lambda>(_,(F,E,y,x)). (E,x)) ` Set.filter (\<lambda>(_,(F,E,y',x)). y'=y) C\<close> 
    and \<open>CF = (\<lambda>(_,(F,E,y,x)). (F,y)) ` C\<close> for y
  with \<open>finite C\<close> have [simp]: \<open>finite (CE y)\<close> \<open>finite CF\<close> for y
    by auto
  have C_C1C2: \<open>C \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):CF. CE y)\<close>
  proof (rule subsetI)
    fix c assume \<open>c \<in> C\<close>
    then obtain EF E F x y where c_def: \<open>c = (EF,(F,E,y,x))\<close>
      by (metis surj_pair)
    from \<open>c \<in> C\<close> have EF_def: \<open>EF = E o\<^sub>C\<^sub>L F\<close>
      using C_subset by (auto intro!: simp: c_def)
    from \<open>c \<in> C\<close> have 1: \<open>(F,y) \<in> CF\<close>
      apply (simp add: CF_def c_def)
      by force
    from \<open>c \<in> C\<close> have 2: \<open>(E,x) \<in> CE y\<close>
      apply (simp add: CE_def c_def)
      by force
    from 1 2 show \<open>c \<in> (\<lambda>((F, y), E, x). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F, y):CF. CE y)\<close>
      apply (simp add: c_def EF_def)
      by force
  qed

  have CE_sub_\<EE>: \<open>CE y \<subseteq> Rep_kraus_family (\<EE> y)\<close> and \<open>CF \<subseteq> Rep_kraus_family \<FF>\<close> for y
    using C_subset by (auto simp add: CE_def CF_def \<FF>x\<EE>_def case_prod_unfold)
  have CE_BE: \<open>(\<Sum>(E, x)\<in>CE y. (E* o\<^sub>C\<^sub>L E)) \<le> BE\<close> for y
    using BE[where y=y] CE_sub_\<EE>[of y]
    by auto

  have \<open>A \<le> (\<Sum>(E,x) \<in> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):CF. CE y). E* o\<^sub>C\<^sub>L E)\<close>
    using C_C1C2 apply (auto intro!: finite_imageI sum_mono2 simp: A_def)
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
  also have \<open>B *\<^sub>R BF = (B * kraus_family_norm \<FF>) *\<^sub>R id_cblinfun\<close>
    by (simp add: BF_def)
  finally show \<open>A \<le> (B * kraus_family_norm \<FF>) *\<^sub>R id_cblinfun\<close>
    by -
qed


lift_definition kraus_family_comp_dependent_raw :: \<open>('x \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'y) kraus_family) \<Rightarrow> ('a::chilbert_space,'b,'x) kraus_family
                    \<Rightarrow> ('a, 'c, 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'b \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'x \<times> 'y) kraus_family\<close> is
  \<open>\<lambda>\<EE> \<FF>. if bdd_above ((kraus_family_norm o \<EE>) ` UNIV) then
    (\<lambda>((F,y), (E::'b\<Rightarrow>\<^sub>C\<^sub>L'c,x::'y)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F::'a\<Rightarrow>\<^sub>C\<^sub>L'b,y::'x):Rep_kraus_family \<FF>. (Rep_kraus_family (\<EE> y)))
    else {}\<close>
proof (rename_tac \<EE> \<FF>)
  fix \<EE> :: \<open>'x \<Rightarrow> ('b, 'c, 'y) kraus_family\<close> and \<FF> :: \<open>('a, 'b, 'x) kraus_family\<close>
  show \<open>(if bdd_above (range (kraus_family_norm o \<EE>))
        then (\<lambda>((F, y), E, x). (E o\<^sub>C\<^sub>L F, (F, E, y, x))) ` (SIGMA (F, y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))
        else {})
       \<in> Collect kraus_family\<close>
  proof (cases \<open>bdd_above (range (kraus_family_norm o \<EE>))\<close>)
    case True
    from True obtain B where \<EE>_uniform: \<open>kraus_family_norm (\<EE> y) \<le> B\<close> for y
      by (auto simp: bdd_above_def)
    define \<FF>x\<EE> where \<open>\<FF>x\<EE> = (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
    have \<open>bdd_above ((\<lambda>M. \<Sum>(E,x)\<in>M. E* o\<^sub>C\<^sub>L E) `
            {M. M \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` \<FF>x\<EE> \<and> finite M})\<close>
    proof (rule bdd_aboveI, rename_tac A)
      fix A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
      assume \<open>A \<in> (\<lambda>M. \<Sum>(E, x)\<in>M. E* o\<^sub>C\<^sub>L E) ` {M. M \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` \<FF>x\<EE> \<and> finite M}\<close>
      then obtain C where A_def: \<open>A = (\<Sum>(E,x)\<in>C. E* o\<^sub>C\<^sub>L E)\<close>
        and C\<FF>\<EE>: \<open>C \<subseteq> (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` \<FF>x\<EE>\<close>
        and [simp]: \<open>finite C\<close>
        by auto
      from kraus_family_comp_dependent_raw_norm_aux[OF \<EE>_uniform \<open>finite C\<close>]
      show \<open>A \<le> (B * kraus_family_norm \<FF>) *\<^sub>R id_cblinfun\<close>
        using C\<FF>\<EE>
        by (auto intro!: simp: A_def \<FF>x\<EE>_def)
    qed
    then have \<open>kraus_family ((\<lambda>((F, y), E, x). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F, y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y)))\<close>
      by (auto intro!: kraus_familyI simp: conj_commute \<FF>x\<EE>_def)
    then show ?thesis
      using True by simp
  next
    case False
    then show ?thesis
      by (auto simp: kraus_family_def)
  qed
qed

lemma kraus_family_comp_dependent_raw_norm:
  assumes \<open>\<And>x. kraus_family_norm (\<EE> x) \<le> B\<close>
  shows \<open>kraus_family_norm (kraus_family_comp_dependent_raw \<EE> \<FF>) \<le> B * kraus_family_norm \<FF>\<close>
proof (cases \<open>class.not_singleton TYPE('e)\<close>)
  case True
  show ?thesis
  proof (rule kraus_family_norm_leqI)
    fix F assume \<open>finite F\<close> and F_subset: \<open>F \<subseteq> Rep_kraus_family (kraus_family_comp_dependent_raw \<EE> \<FF>)\<close>
    have bpos: \<open>B \<ge> 0\<close>
      using assms[of undefined] 
      by (smt (verit, best) kraus_family_norm_geq0)
    have [simp]: \<open>norm (id_cblinfun :: 'e \<Rightarrow>\<^sub>C\<^sub>L 'e) = 1\<close>
      apply (rule norm_cblinfun_id[internalize_sort' 'a])
      apply (rule complex_normed_vector_axioms)
      by (rule True)
    from assms have bdd: \<open>bdd_above (range (\<lambda>x. kraus_family_norm (\<EE> x)))\<close>
      by fast
    have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> (B * kraus_family_norm \<FF>) *\<^sub>R id_cblinfun\<close>
      using assms \<open>finite F\<close> apply (rule kraus_family_comp_dependent_raw_norm_aux)
      using F_subset by (simp add: kraus_family_comp_dependent_raw.rep_eq bdd)
    then have \<open>norm (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> norm ((B * kraus_family_norm \<FF>) *\<^sub>R (id_cblinfun :: 'e \<Rightarrow>\<^sub>C\<^sub>L 'e))\<close>
      apply (rule norm_cblinfun_mono[rotated])
      apply (auto intro!: sum_nonneg)
      using positive_cblinfun_squareI by blast
    then show \<open>norm (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B * kraus_family_norm \<FF>\<close>
      using \<open>B \<ge> 0\<close> by auto
  qed
next
  case False
  have bpos: \<open>B \<ge> 0\<close>
    using assms[of undefined] 
    by (smt (verit, best) \<open>kraus_family_norm (\<EE> undefined) \<le> B\<close> kraus_family_norm_geq0)
  show ?thesis
    using not_not_singleton_kraus_family_norm[OF False, of \<open>kraus_family_comp_dependent_raw \<EE> \<FF>\<close>]
    using bpos by auto
qed

hide_fact kraus_family_comp_dependent_raw_norm_aux

lift_definition kraus_family_remove_0 :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family \<Rightarrow> ('a,'b,'x) kraus_family\<close> is
  \<open>Set.filter (\<lambda>(E,x). E\<noteq>0)\<close>
proof -
  fix \<EE> :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'c) set\<close>
  have *: \<open>{F. finite F \<and> F \<subseteq> Set.filter (\<lambda>p. fst p \<noteq> 0) \<EE>} \<subseteq> {F. finite F \<and> F \<subseteq> \<EE>}\<close>
    by auto
  show \<open>\<EE> \<in> Collect kraus_family \<Longrightarrow> Set.filter (\<lambda>(E, x). E \<noteq> 0) \<EE> \<in> Collect kraus_family\<close>
    by (auto intro: bdd_above_mono2[OF _ *] simp add: kraus_family_def case_prod_unfold)
qed

(* lemma kraus_family_map_outcome_inj:
  assumes \<open>inj f\<close>
  shows \<open>Rep_kraus_family (kraus_family_map_outcome f \<EE>) = (\<lambda>(E,x). (E, f x)) ` Rep_kraus_family (kraus_family_remove_0 \<EE>)\<close>
proof (intro Set.set_eqI iffI)
  fix Ex
  assume asm: \<open>Ex \<in> Rep_kraus_family (kraus_family_map_outcome f \<EE>)\<close>
  obtain E x where [simp]: \<open>Ex = (E,x)\<close>
    by fastforce
  from asm
  have norm_EE: \<open>norm (E* o\<^sub>C\<^sub>L E) = kraus_family_op_weight (kraus_family_filter (\<lambda>y. f y = x) \<EE>) E\<close> and \<open>E \<noteq> 0\<close>
    by (simp_all add: kraus_family_map_outcome.rep_eq)

  have \<open>kraus_family_op_weight (kraus_family_filter (\<lambda>y. f y = x) \<EE>) E \<noteq> 0\<close>
    using \<open>E \<noteq> 0\<close> norm_EE by force
  then have \<open>{(F, xa). (F, xa) \<in> Rep_kraus_family (kraus_family_filter (\<lambda>y. f y = x) \<EE>) \<and> (\<exists>r>0. E = r *\<^sub>R F)} \<noteq> {}\<close>
    apply (simp add: kraus_family_op_weight_def kraus_family_related_ops_def)
    by (smt (verit, ccfv_SIG) case_prodE infsum_0 mem_Collect_eq)
  then obtain F y r where Fy_filter: \<open>(F, y) \<in> Rep_kraus_family (kraus_family_filter (\<lambda>y. f y = x) \<EE>)\<close>
    and \<open>r > 0\<close> and \<open>E = r *\<^sub>R F\<close>
    by blast
  from Fy_filter have Fy_\<EE>: \<open>(F, y) \<in> Rep_kraus_family \<EE>\<close> and \<open>f y = x\<close>
    by (simp_all add: kraus_family_filter.rep_eq)
  with \<open>r > 0\<close> \<open>E = r *\<^sub>R F\<close> \<open>E \<noteq> 0\<close> have \<open>F \<noteq> 0\<close>
    by auto
  with Fy_\<EE> have \<open>(F, y) \<in> Rep_kraus_family (kraus_family_remove_0 \<EE>)\<close>
    by (simp add: kraus_family_remove_0.rep_eq)
  then show \<open>Ex \<in> (\<lambda>(E, x). (E, f x)) ` Rep_kraus_family (kraus_family_remove_0 \<EE>)\<close>
    apply (rule rev_image_eqI)
apply (auto intro!: simp: \<open>E = r *\<^sub>R F\<close>)
try0
sledgehammer [dont_slice]
by -
next
  fix Ex
  assume \<open>Ex \<in> (\<lambda>(E, x). (E, f x)) ` Rep_kraus_family (kraus_family_remove_0 \<EE>)\<close>
  obtain E x where [simp]: \<open>Ex = (E,x)\<close>
    by fastforce
  show \<open>Ex \<in> Rep_kraus_family (kraus_family_map_outcome f \<EE>)\<close>


  apply (simp add: kraus_family_map_outcome.rep_eq)
  apply (auto intro!: simp: kraus_family_map_outcome.rep_eq) *)


definition \<open>kraus_family_comp_dependent \<EE> \<FF> = kraus_family_map_outcome (\<lambda>(F,E,y,x). (y,x)) (kraus_family_comp_dependent_raw \<EE> \<FF>)\<close>

definition \<open>kraus_family_comp \<EE> \<FF> = kraus_family_comp_dependent (\<lambda>_. \<EE>) \<FF>\<close>

lemma kraus_family_comp_dependent_norm:
  assumes \<open>\<And>x. kraus_family_norm (\<EE> x) \<le> B\<close>
  shows \<open>kraus_family_norm (kraus_family_comp_dependent \<EE> \<FF>) \<le> B * kraus_family_norm \<FF>\<close>
  using assms by (auto intro!: kraus_family_comp_dependent_raw_norm simp: kraus_family_comp_dependent_def)

lemma kraus_family_comp_norm:
  shows \<open>kraus_family_norm (kraus_family_comp \<EE> \<FF>) \<le> kraus_family_norm \<EE> * kraus_family_norm \<FF>\<close>
  by (auto intro!: kraus_family_comp_dependent_norm simp: kraus_family_comp_def)

(* lemma Rep_kraus_family_comp: \<open>Rep_kraus_family (kraus_family_comp \<EE> \<FF>) = xxx\<close>
  apply (auto intro!: simp: kraus_family_comp_def kraus_family_comp_dependent_def kraus_family_comp_dependent_raw.rep_eq
id_def) 
  by xxx *)

lemma kraus_family_comp_dependent_raw_apply:
  fixes \<EE> :: \<open>'y \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('c::chilbert_space, 'a, 'y) kraus_family\<close>
  assumes \<open>bdd_above (range (kraus_family_norm o \<EE>))\<close>
  shows \<open>kraus_family_map (kraus_family_comp_dependent_raw \<EE> \<FF>) \<rho>
      = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. kraus_family_map (\<EE> y) (sandwich_tc F \<rho>))\<close>
proof -
(*   have family: \<open>kraus_family (kraus_family_comp_dependent_raw \<EE> \<FF>)\<close>
    by (auto intro!: kraus_family_kraus_family_comp_dependent_raw assms) *)

  have sum2: \<open>(\<lambda>(F, x). sandwich_tc F \<rho>) summable_on (Rep_kraus_family \<FF>)\<close>
    using kraus_family_map_summable[of \<rho> \<FF>] (* kraus\<FF> *) by (simp add: case_prod_unfold)
  have \<open>(\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on 
          (\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
    using kraus_family_map_summable[of _ \<open>kraus_family_comp_dependent_raw \<EE> \<FF>\<close>] assms
    by (simp add: kraus_family_comp_dependent_raw.rep_eq case_prod_unfold)
  then have sum1: \<open>(\<lambda>((F,y), (E,x)). sandwich_tc (E o\<^sub>C\<^sub>L F) \<rho>) summable_on (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y))\<close>
    apply (subst (asm) summable_on_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)

  have \<open>kraus_family_map (kraus_family_comp_dependent_raw \<EE> \<FF>) \<rho>
          = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>((F,y), (E,x)). (E o\<^sub>C\<^sub>L F, (F,E,y,x))) ` (SIGMA (F,y):Rep_kraus_family \<FF>. Rep_kraus_family (\<EE> y)). sandwich_tc (fst E) \<rho>)\<close>
    using assms by (simp add: kraus_family_map_def kraus_family_comp_dependent_raw.rep_eq case_prod_unfold)
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

lemma kraus_family_comp_dependent_apply:
  fixes \<EE> :: \<open>'y \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'x) kraus_family\<close>
    and \<FF> :: \<open>('c::chilbert_space, 'a, 'y) kraus_family\<close>
  assumes \<open>bdd_above (range (kraus_family_norm o \<EE>))\<close>
  shows \<open>kraus_family_map (kraus_family_comp_dependent \<EE> \<FF>) \<rho>
      = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. kraus_family_map (\<EE> y) (sandwich_tc F \<rho>))\<close>
  using assms by (simp add: kraus_family_comp_dependent_def kraus_family_map_outcome_same_map
      kraus_family_comp_dependent_raw_apply)

lemma kraus_family_comp_apply:
  shows \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) = kraus_family_map \<EE> \<circ> kraus_family_map \<FF>\<close>
proof (rule ext, rename_tac \<rho>)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>

  have sumF: \<open>(\<lambda>(F, y). sandwich_tc F \<rho>) summable_on Rep_kraus_family \<FF>\<close>
    by (rule kraus_family_map_summable)
  have \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) \<rho> = (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. kraus_family_map \<EE> (sandwich_tc F \<rho>))\<close>
    by (auto intro!: kraus_family_comp_dependent_apply simp: kraus_family_comp_def)
  also have \<open>\<dots> = kraus_family_map \<EE> (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. sandwich_tc F \<rho>)\<close>
    apply (subst infsum_bounded_linear[symmetric, where h=\<open>kraus_family_map \<EE>\<close>])
    using sumF by (auto intro!: bounded_clinear.bounded_linear kraus_family_map_bounded_clinear
        simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (kraus_family_map \<EE> \<circ> kraus_family_map \<FF>) \<rho>\<close>
    by (simp add: o_def kraus_family_map_def case_prod_unfold)
  finally show \<open>kraus_family_map (kraus_family_comp \<EE> \<FF>) \<rho> = (kraus_family_map \<EE> \<circ> kraus_family_map \<FF>) \<rho>\<close>
    by -
qed

definition kraus_map :: \<open>(('a::chilbert_space,'a) trace_class \<Rightarrow> ('b::chilbert_space,'b) trace_class) \<Rightarrow> bool\<close> where
  \<open>kraus_map \<EE> \<longleftrightarrow> (\<exists>EE :: ('a,'b,unit) kraus_family. \<EE> = kraus_family_map EE)\<close>

lemma kraus_map_def': \<open>kraus_map \<EE> \<longleftrightarrow> (\<exists>EE :: ('a::chilbert_space,'b::chilbert_space,'x) kraus_family. \<EE> = kraus_family_map EE)\<close>
proof (rule iffI)
  assume \<open>kraus_map \<EE>\<close>
  then obtain EE :: \<open>('a,'b,unit) kraus_family\<close> where EE: \<open>\<EE> = kraus_family_map EE\<close>
    using kraus_map_def by blast
  define EE' :: \<open>('a,'b,'x) kraus_family\<close> where \<open>EE' = kraus_family_map_outcome (\<lambda>_. undefined) EE\<close>
  have \<open>kraus_family_map EE' = kraus_family_map EE\<close>
    by (simp add: EE'_def kraus_family_map_outcome_same_map)
  with EE show \<open>\<exists>EE :: ('a,'b,'x) kraus_family. \<EE> = kraus_family_map EE\<close>
    by metis
next
  assume \<open>\<exists>EE :: ('a,'b,'x) kraus_family. \<EE> = kraus_family_map EE\<close>
  then obtain EE :: \<open>('a,'b,'x) kraus_family\<close> where EE: \<open>\<EE> = kraus_family_map EE\<close>
    using kraus_map_def by blast
  define EE' :: \<open>('a,'b,unit) kraus_family\<close> where \<open>EE' = kraus_family_map_outcome (\<lambda>_. ()) EE\<close>
  have \<open>kraus_family_map EE' = kraus_family_map EE\<close>
    by (simp add: EE'_def kraus_family_map_outcome_same_map)
  with EE show \<open>kraus_map \<EE>\<close>
    apply (simp add: kraus_map_def)
    by metis
qed

lemma kraus_mapI:
  assumes \<open>\<EE> = kraus_family_map EE\<close>
  shows \<open>kraus_map \<EE>\<close>
  using assms kraus_map_def' by blast

lemma kraus_map_kraus_family_map[iff]: \<open>kraus_map (kraus_family_map \<EE>)\<close>
  using kraus_map_def'
  by blast

(* lift_definition kraus_map_comp :: \<open>('a::chilbert_space,'b::chilbert_space) kraus_map
                                \<Rightarrow> ('c::chilbert_space,'a) kraus_map \<Rightarrow> ('c,'b) kraus_map\<close>
  is \<open>\<lambda>\<EE> \<FF>. kraus_family_flatten (kraus_family_comp \<EE> \<FF>)\<close>
  by (auto intro!: 
      simp add: kraus_equivalent_def kraus_family_comp_apply kraus_family_map_outcome_same_map) *)

definition \<open>kraus_family_id = kraus_family_of_op id_cblinfun\<close>

lemma kraus_family_norm_id_le: \<open>kraus_family_norm kraus_family_id \<le> 1\<close>
  apply (simp add: kraus_family_id_def)
  apply transfer
  by (auto intro!: power_le_one onorm_pos_le onorm_id_le)

lemma kraus_map_norm_id[simp]: \<open>kraus_family_norm (kraus_family_id :: ('a :: {chilbert_space, not_singleton},'a,unit) kraus_family) = 1\<close>
  by (auto intro!: antisym kraus_family_norm_id_le simp: kraus_family_id_def)

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

instantiation kraus_family :: (chilbert_space, chilbert_space, type) scaleR begin
lift_definition scaleR_kraus_family :: \<open>real \<Rightarrow> ('a::chilbert_space,'b::chilbert_space,'x) kraus_family \<Rightarrow> ('a,'b,'x) kraus_family\<close> is
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
instance..
end

lemma kraus_family_scale_map:
  assumes \<open>r \<ge> 0\<close>
  shows \<open>kraus_family_map (r *\<^sub>R \<EE>) \<rho> = r *\<^sub>R kraus_family_map \<EE> \<rho>\<close>
proof (cases \<open>r > 0\<close>)
  case True
  then show ?thesis
    apply (simp add: scaleR_kraus_family.rep_eq kraus_family_map_def)
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI
        simp: kraus_family_map_def case_prod_unfold
        o_def sandwich_tc_scaleR_left cblinfun.scaleR_left infsum_scaleR_right)
next
  case False
  with assms show ?thesis
    by (simp add: kraus_family_map.rep_eq scaleR_kraus_family.rep_eq)
qed

(* instantiation kraus_map :: (chilbert_space, chilbert_space) \<open>{zero,plus,scaleR}\<close> begin
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
end *)


(* instantiation kraus_map :: (chilbert_space, chilbert_space) comm_monoid_add begin
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
end *)


(* lift_definition kraus_map_apply :: \<open>('a::chilbert_space,'b::chilbert_space) kraus_map \<Rightarrow> ('a,'a) trace_class \<Rightarrow> ('b,'b) trace_class\<close> is
  \<open>kraus_family_map\<close>
  by (auto simp: kraus_equivalent_def) *)

(* lemma kraus_map_apply_bounded_clinear[bounded_clinear]:
  \<open>bounded_clinear (kraus_map_apply \<EE>)\<close>
  apply transfer
  using kraus_equivalent_def kraus_family_map_bounded_clinear by blast *)

lemma kraus_family_of_op_apply: \<open>kraus_family_map (kraus_family_of_op E) \<rho> = sandwich_tc E \<rho>\<close>
  by (simp add: kraus_family_map_def kraus_family_of_op.rep_eq)


(* lemma kraus_map_of_op_apply: \<open>kraus_map_apply (kraus_map_of_op E) \<rho> = sandwich_tc E \<rho>\<close>
  apply (transfer' fixing: \<rho>)
  by (simp add: kraus_family_of_op_apply) *)

lemma kraus_family_id_apply[simp]: \<open>kraus_family_map kraus_family_id \<rho> = \<rho>\<close>
  by (simp add: kraus_family_id_def kraus_family_of_op_apply)

(* lemma kraus_family_rep_kraus_map[simp]: \<open>kraus_family (rep_kraus_map \<EE>)\<close>
  using Quotient_rep_reflp[OF Quotient_kraus_map]
  by (auto simp add: kraus_equivalent_def) *)

(* lemma kraus_family_scaleR:
  assumes \<open>r \<ge> 0\<close>
  shows \<open>kraus_family_map (r *\<^sub>R \<EE>) \<rho> = r *\<^sub>R kraus_family_map \<EE> \<rho>\<close>
proof -
  have \<open>kraus_family_map (r *\<^sub>R \<EE>) \<rho> = kraus_family_family (kraus_family_scale r (rep_kraus_family \<EE>)) \<rho>\<close>
    by (simp add: scaleR_kraus_family_def kraus_family_map.abs_eq kraus_equivalent_reflI)
  also have \<open>\<dots> = r *\<^sub>R kraus_family_family (rep_kraus_family \<EE>) \<rho>\<close>
    by (simp add: kraus_family_scale_family assms)
  also have \<open>\<dots> = r *\<^sub>R kraus_family_map \<EE> \<rho>\<close>
    by (simp flip: kraus_family_map.rep_eq add: cblinfun.scaleR_left)
  finally show \<open>kraus_family_map (r *\<^sub>R \<EE>) \<rho> = r *\<^sub>R kraus_family_map \<EE> \<rho>\<close>
    by -
qed *)

lemma kraus_map_scaleR_neg:
  assumes \<open>r \<le> 0\<close>
  shows \<open>kraus_family_map (r *\<^sub>R \<EE>) = 0\<close>
  apply (transfer fixing: r)
  using assms
  by (auto intro!: ext simp: scaleR_kraus_family.rep_eq kraus_family_map.rep_eq)

(* lemma kraus_map_norm_0[simp]: \<open>kraus_family_norm 0 = 0\<close>
  apply transfer by simp *)


(* instantiation kraus_map :: (chilbert_space, chilbert_space) dist begin
definition dist_kraus_map :: \<open>('a,'b) kraus_map \<Rightarrow> ('a,'b) kraus_map \<Rightarrow> real\<close> where
  \<open>dist_kraus_map E F = (\<Squnion>\<rho>. dist (kraus_map_apply E \<rho>) (kraus_map_apply F \<rho>) / norm \<rho>)\<close>
instance..
end *)

(* lemma kraus_map_apply_inj: \<open>kraus_map_apply x = kraus_map_apply y \<Longrightarrow> x = y\<close>
  apply transfer
  by (simp add: kraus_equivalent_def) *)

(* lemma norm_kraus_map_apply: \<open>norm (kraus_map_apply E \<rho>) \<le> 4 * kraus_map_norm E * norm \<rho>\<close>
  apply (transfer fixing: \<rho>)
  using kraus_equivalent_def kraus_family_map_bounded by blast *)

(* lemma norm_kraus_map_apply_pos: \<open>norm (kraus_map_apply E \<rho>) \<le> kraus_map_norm E * norm \<rho>\<close> if \<open>\<rho> \<ge> 0\<close>
  apply (transfer fixing: \<rho>)
  by (simp add: kraus_equivalent_def kraus_family_map_bounded_pos that) *)

(* lemma kraus_map_norm_geq0[simp]: \<open>kraus_map_norm E \<ge> 0\<close>
  apply transfer
  by (simp add: kraus_equivalent_def kraus_family_norm_geq0) *)

(* lemma dist_kraus_map_bdd: \<open>bdd_above (range (\<lambda>\<rho>. dist (kraus_map_apply x \<rho>) (kraus_map_apply y \<rho>) / norm \<rho>))\<close>
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
qed *)


lemma kraus_family_apply_0_left[iff]: \<open>kraus_family_map 0 \<rho> = 0\<close>
  apply (transfer' fixing: \<rho>)
  by simp

(* lemma kraus_map_apply_0_left[iff]: \<open>kraus_map_apply 0 \<rho> = 0\<close>
proof -
  have \<open>kraus_map_apply 0 \<rho> = x\<close> if \<open>x = 0\<close> for x
    apply (transfer fixing: \<rho> x)
    by (simp add: that)
  then show ?thesis
    by simp
qed *)

lemma kraus_family_map_clinear[iff]: \<open>clinear (kraus_family_map \<EE>)\<close>
  by (simp add: bounded_clinear.axioms(1) kraus_family_map_bounded_clinear)

lemma kraus_map_apply_0_right[iff]: \<open>kraus_family_map \<EE> 0 = 0\<close>
  by (metis ab_left_minus kraus_family_map_plus_right kraus_family_map_uminus_right)

(* lemma kraus_map_apply_0_right[iff]: \<open>kraus_map_apply \<EE> 0 = 0\<close>
  by (intro Linear_Algebra.linear_simps bounded_clinear.bounded_linear kraus_map_apply_bounded_clinear) *)


(* instantiation kraus_map :: (chilbert_space, chilbert_space) metric_space begin
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
end *)

(* lemma kraus_map_apply_comp: \<open>kraus_map_apply (kraus_map_comp E F) = kraus_map_apply E o kraus_map_apply F\<close>
  apply transfer
  by (simp add: kraus_equivalent_def kraus_family_map_outcome_same_map kraus_family_comp_apply) *)

(* lemma kraus_map_comp_assoc: \<open>kraus_map_comp (kraus_map_comp E F) G = kraus_map_comp E (kraus_map_comp F G)\<close>
  apply (rule kraus_map_apply_inj)
  by (simp add: kraus_map_apply_comp o_def) *)

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

lemma complete_measurement_is_family: 
  assumes \<open>is_ortho_set B\<close>
  shows \<open>kraus_family ((\<lambda>x. (selfbutter (sgn x), x)) ` B)\<close>
proof -
  define family :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a \<times> 'a) set\<close> where \<open>family = (\<lambda>x. (selfbutter (sgn x), x)) ` B\<close>
  show \<open>kraus_family family\<close>
  proof -
    have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> id_cblinfun\<close> if \<open>finite F\<close> and FB: \<open>F \<subseteq> family\<close> for F :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a \<times> 'a) set\<close>
    proof -
      obtain G where \<open>finite G\<close> and \<open>G \<subseteq> B\<close> and FG: \<open>F = (\<lambda>x. (selfbutter (sgn x), x)) ` G\<close>
        apply atomize_elim
        using \<open>finite F\<close> and FB
        apply (simp add: family_def)
        by (meson finite_subset_image)
      from \<open>G \<subseteq> B\<close> have [simp]: \<open>is_ortho_set G\<close>
        by (simp add: \<open>is_ortho_set B\<close> is_ortho_set_antimono)
      then have [simp]: \<open>e \<in> G \<Longrightarrow> norm (sgn e) = 1\<close> for e
        apply (simp add: is_ortho_set_def)
        by (metis norm_sgn)
      have [simp]: \<open>inj_on (\<lambda>x. (selfbutter (sgn x), x)) G\<close>
        by (meson inj_onI prod.inject)
      have [simp]: \<open>inj_on sgn G\<close>
      proof (rule inj_onI, rule ccontr)
        fix x y assume \<open>x \<in> G\<close> and \<open>y \<in> G\<close> and sgn_eq: \<open>sgn x = sgn y\<close> and \<open>x \<noteq> y\<close>
        with \<open>is_ortho_set G\<close> have \<open>is_orthogonal x y\<close>
          by (meson is_ortho_set_def)
        then have \<open>is_orthogonal (sgn x) (sgn y)\<close>
          by fastforce
        with sgn_eq have \<open>sgn x = 0\<close>
          by force
        with \<open>x \<in> G\<close> \<open>is_ortho_set G\<close> show False
          by (metis \<open>x \<noteq> y\<close> local.sgn_eq sgn_zero_iff)
      qed
      have \<open>(\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) = (\<Sum>x\<in>G. selfbutter (sgn x))\<close>
        by (simp add: FG sum.reindex cdot_square_norm)
      also have \<open>(\<Sum>x\<in>G. selfbutter (sgn x)) \<le> id_cblinfun\<close>
        apply (subst sum.reindex[where h=sgn, unfolded o_def, symmetric])
        using \<open>is_ortho_set G\<close>
         apply (auto intro!: sum_butterfly_leq_id simp: is_ortho_set_def sgn_zero_iff)
        by fast
      finally show ?thesis
        by -
    qed
    then show ?thesis
      by (auto intro!: bdd_aboveI[where M=id_cblinfun] kraus_familyI)
  qed
qed

lift_definition complete_measurement :: \<open>'a set \<Rightarrow> ('a::chilbert_space, 'a, 'a) kraus_family\<close> is
  \<open>\<lambda>B. if is_ortho_set B then (\<lambda>x. (selfbutter (sgn x), x)) ` B else {}\<close>
  by (auto intro!: complete_measurement_is_family)

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

(* lift_definition trace_kraus_map :: \<open>('a::chilbert_space, 'b::one_dim) kraus_map\<close> is
  \<open>kraus_family_flatten (trace_kraus_family some_chilbert_basis)\<close>. *)

lemma trace_is_kraus_map: \<open>kraus_map (one_dim_iso o trace_tc)\<close>
  by (auto intro!: ext kraus_mapI[of _ \<open>trace_kraus_family some_chilbert_basis\<close>]
      simp: trace_kraus_family_is_trace)

lemma id_is_kraus_map[iff]: \<open>kraus_map id\<close>
  by (auto intro!: ext kraus_mapI[of _ kraus_family_id])

(* lemma trace_kraus_map_is_trace: \<open>kraus_map_apply trace_kraus_map \<rho> = one_dim_iso (trace_tc \<rho>)\<close>
  apply (transfer' fixing: \<rho>)
  by (simp add: kraus_family_map_outcome_same_map trace_kraus_family_is_trace) *)

definition \<open>trace_preserving_map \<EE> \<longleftrightarrow> clinear \<EE> \<and> (\<forall>\<rho>. trace_tc (\<EE> \<rho>) = trace_tc \<rho>)\<close>

lemma trace_preserving_id[iff]: \<open>trace_preserving_map id\<close>
  by (simp add: trace_preserving_map_def complex_vector.linear_id)

lemma trace_preserving_trace_kraus_map[iff]: \<open>trace_preserving_map (one_dim_iso o trace_tc)\<close>
  by (auto intro!: clinear_compose simp add: trace_preserving_map_def bounded_clinear.clinear)

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

lemma kraus_map_eqI:
  assumes \<open>kraus_equivalent \<EE> \<FF>\<close>
  shows \<open>kraus_family_map \<EE> \<rho> = kraus_family_map \<FF> \<rho>\<close>
  using assms by (simp add: kraus_equivalent_def)

lemma kraus_family_filter_twice:
  \<open>kraus_family_filter P (kraus_family_filter Q \<EE>) = kraus_family_filter (\<lambda>x. P x \<and> Q x) \<EE>\<close>
  apply (transfer' fixing: P Q)
  by auto

lemma kraus_family_filter_map_outcome:
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  shows \<open>kraus_family_filter P (kraus_family_map_outcome f \<EE>) = kraus_family_map_outcome f (kraus_family_filter (\<lambda>x. P (f x)) \<EE>)\<close>
proof -
  have \<open>(E,x) \<in> Set.filter (\<lambda>(E, y). P y) {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kraus_family_op_weight (kraus_family_filter (\<lambda>x. f x = y) \<EE>) E \<and> E \<noteq> 0}
   \<longleftrightarrow> (E,x) \<in> {(E, y). norm (E* o\<^sub>C\<^sub>L E) = kraus_family_op_weight (kraus_family_filter (\<lambda>x. f x = y) (kraus_family_filter (\<lambda>x. P (f x)) \<EE>)) E \<and> E \<noteq> 0}\<close>
    for E x and \<EE> :: \<open>('a, 'b, 'x) kraus_family\<close>
  proof (cases \<open>P x\<close>)
    case True
    then show ?thesis
      apply (auto simp: kraus_family_filter_twice)
      by metis+
  next
    case False
    then have [simp]: \<open>(\<lambda>z. f z = x \<and> P (f z)) = (\<lambda>_. False)\<close>
      by auto
    from False show ?thesis
      by (auto intro!: simp: kraus_family_filter_twice)
  qed
  then show ?thesis
    apply (transfer' fixing: P f)
    by blast
qed


(* TODO: delete fact later *)
lemma kraus_family_tensor_raw_bound_aux:
  fixes \<EE> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'x) set\<close> and \<FF> :: \<open>('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2 \<times> 'y) set\<close>
  assumes \<open>\<And>S. finite S \<Longrightarrow> S \<subseteq> \<EE> \<Longrightarrow> (\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> B\<close>
  assumes \<open>\<And>S. finite S \<Longrightarrow> S \<subseteq> \<FF> \<Longrightarrow> (\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> C\<close>
  assumes \<open>finite U\<close>
  assumes \<open>U \<subseteq> ((\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)) ` (\<EE> \<times> \<FF>))\<close>
  shows \<open>(\<Sum>(G, z)\<in>U. G* o\<^sub>C\<^sub>L G) \<le> B \<otimes>\<^sub>o C\<close>
proof -
  from assms(1)[where S=\<open>{}\<close>] have [simp]: \<open>B \<ge> 0\<close>
    by simp
  define f :: \<open>(('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<times> 'x) \<times> ('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2 \<times> 'y)) \<Rightarrow> _\<close>
    where \<open>f = (\<lambda>((E,x), (F,y)). (E \<otimes>\<^sub>o F, (E,F,x,y)))\<close>
  from assms
  obtain V where V_subset: \<open>V \<subseteq> \<EE> \<times> \<FF>\<close> and [simp]: \<open>finite V\<close> and \<open>U = f ` V\<close>
    apply (simp flip: f_def)
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
    by (auto intro!: tensor_op_mono assms sum_nonneg intro: positive_cblinfun_squareI)
  finally show ?thesis
    by-
qed


lift_definition kraus_family_tensor_raw :: \<open>('a ell2, 'b ell2, 'x) kraus_family \<Rightarrow> ('c ell2, 'd ell2, 'y) kraus_family \<Rightarrow> 
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
      using that by (auto intro!: kraus_family_tensor_raw_bound_aux B C simp: tensor_def)
    then show \<open>bdd_above ((\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> tensor})\<close>
      by fast
  qed
qed

lemma kraus_family_map_tensor_raw:
  shows \<open>kraus_family_map (kraus_family_tensor_raw \<EE> \<FF>) (tc_tensor \<rho> \<sigma>) = tc_tensor (kraus_family_map \<EE> \<rho>) (kraus_family_map \<FF> \<sigma>)\<close>
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

  from kraus_family_map_summable[of _ \<open>kraus_family_tensor_raw \<EE> \<FF>\<close>]
  have sum1: \<open>(\<lambda>((E, x), F, y). sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>)) summable_on Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>\<close>
    apply (simp add: kraus_family_map.rep_eq kraus_family_tensor_raw.rep_eq summable_on_reindex inj o_def)
    by (simp add: case_prod_unfold)

  have \<open>kraus_family_map (kraus_family_tensor_raw \<EE> \<FF>) (tc_tensor \<rho> \<sigma>)
      = (\<Sum>\<^sub>\<infinity>((E,x),(F,y))\<in>Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>))\<close>
    apply (simp add: kraus_family_map.rep_eq kraus_family_tensor_raw.rep_eq infsum_reindex inj o_def)
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. \<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. sandwich_tc (E \<otimes>\<^sub>o F) (tc_tensor \<rho> \<sigma>))\<close>
    apply (subst infsum_Sigma_banach[symmetric])
    using sum1 by (auto intro!: simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. \<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. tc_tensor (sandwich_tc E \<rho>) (sandwich_tc F \<sigma>))\<close>
    by (simp add: sandwich_tc_tensor)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. tc_tensor (sandwich_tc E \<rho>) (\<Sum>\<^sub>\<infinity>(F,y)\<in>Rep_kraus_family \<FF>. (sandwich_tc F \<sigma>)))\<close>
    apply (subst infsum_bounded_linear[where h=\<open>tc_tensor (sandwich_tc _ \<rho>)\<close>, symmetric])
      apply (auto intro!: sum3)[2]
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. tc_tensor (sandwich_tc E \<rho>) (kraus_family_map \<FF> \<sigma>))\<close>
    by (simp add: kraus_family_map_def case_prod_unfold)
  also have \<open>\<dots> = tc_tensor (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. sandwich_tc E \<rho>) (kraus_family_map \<FF> \<sigma>)\<close>
    apply (subst infsum_bounded_linear[where h=\<open>\<lambda>x. tc_tensor x (kraus_family_map \<FF> \<sigma>)\<close>, symmetric])
      apply (auto intro!: sum2)[2]
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = tc_tensor (kraus_family_map \<EE> \<rho>) (kraus_family_map \<FF> \<sigma>)\<close>
    by (simp add: kraus_family_map_def case_prod_unfold)
  finally show ?thesis
    by -
qed


(* lemma kraus_family_bound_tensor_raw:
  \<open>kraus_family_bound (kraus_family_tensor_raw \<EE> \<FF>) \<le> kraus_family_bound \<EE> \<otimes>\<^sub>o kraus_family_bound \<FF>\<close>
  (* Actually equality holds. *)
  by (auto intro!: kraus_family_bound_leqI
      kraus_family_tensor_raw_bound_aux[where \<EE>=\<open>Rep_kraus_family \<EE>\<close> and \<FF>=\<open>Rep_kraus_family \<FF>\<close>]
      kraus_family_sums_bounded_by_bound simp: kraus_family_tensor_raw.rep_eq) *)

hide_fact kraus_family_tensor_raw_bound_aux

definition \<open>kraus_family_tensor \<EE> \<FF> = kraus_family_map_outcome (\<lambda>(E, F, x, y). (x,y)) (kraus_family_tensor_raw \<EE> \<FF>)\<close>

lemma kraus_family_map_tensor:
  \<open>kraus_family_map (kraus_family_tensor \<EE> \<FF>) (tc_tensor \<rho> \<sigma>)= tc_tensor (kraus_family_map \<EE> \<rho>) (kraus_family_map \<FF> \<sigma>)\<close>
  by (auto intro!: simp: kraus_family_tensor_def kraus_family_map_outcome_same_map kraus_family_map_tensor_raw)


lemma kraus_family_bound_tensor_raw:
  \<open>kraus_family_bound (kraus_family_tensor_raw \<EE> \<FF>) = kraus_family_bound \<EE> \<otimes>\<^sub>o kraus_family_bound \<FF>\<close>
proof (rule cblinfun_cinner_tensor_eqI)
  fix \<psi> \<phi>

  from kraus_family_bound_summable[of \<open>kraus_family_tensor_raw \<EE> \<FF>\<close>]
  have sum1: \<open>summable_on_in cweak_operator_topology (\<lambda>((E,x),(F,y)). (E \<otimes>\<^sub>o F)* o\<^sub>C\<^sub>L (E \<otimes>\<^sub>o F))
     (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>)\<close>
    unfolding kraus_family_tensor_raw.rep_eq
    apply (subst (asm) summable_on_in_reindex)
    by (auto simp add: kraus_family_tensor_raw.rep_eq case_prod_unfold inj_on_def o_def)
  have sum4: \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>)\<close>
    using kraus_family_bound_summable by blast
  have sum5: \<open>summable_on_in cweak_operator_topology (\<lambda>(F,y). F* o\<^sub>C\<^sub>L F) (Rep_kraus_family \<FF>)\<close>
    using kraus_family_bound_summable by blast
  have sum2: \<open>(\<lambda>(E, x). \<psi> \<bullet>\<^sub>C ((E* o\<^sub>C\<^sub>L E) *\<^sub>V \<psi>)) abs_summable_on Rep_kraus_family \<EE>\<close>
    using kraus_family_bound_summable by (auto intro!: summable_on_in_cweak_operator_topology_pointwise 
        simp add: case_prod_unfold simp flip: summable_on_iff_abs_summable_on_complex
        simp del: cblinfun_apply_cblinfun_compose)
  have sum3: \<open>(\<lambda>(F,y). \<phi> \<bullet>\<^sub>C ((F* o\<^sub>C\<^sub>L F) *\<^sub>V \<phi>)) abs_summable_on Rep_kraus_family \<FF>\<close>
    using kraus_family_bound_summable by (auto intro!: summable_on_in_cweak_operator_topology_pointwise
        simp add: case_prod_unfold simp flip: summable_on_iff_abs_summable_on_complex
        simp del: cblinfun_apply_cblinfun_compose)

  have \<open>(\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C (kraus_family_bound (kraus_family_tensor_raw \<EE> \<FF>) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi>)
      = (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C
        (infsum_in cweak_operator_topology ((\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) \<circ> (\<lambda>((E, x), F, y). (E \<otimes>\<^sub>o F, E, F, x, y)))
          (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>) *\<^sub>V
         \<psi> \<otimes>\<^sub>s \<phi>)\<close>
    unfolding kraus_family_bound.rep_eq kraus_family_tensor_raw.rep_eq
    apply (subst infsum_in_reindex)
    by (auto simp add: inj_on_def case_prod_unfold)
  also have \<open>\<dots> = (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C
        (infsum_in cweak_operator_topology (\<lambda>((E,x),(F,y)). (E \<otimes>\<^sub>o F)* o\<^sub>C\<^sub>L (E \<otimes>\<^sub>o F))
            (Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>) *\<^sub>V
         \<psi> \<otimes>\<^sub>s \<phi>)\<close>
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((E,x),(F,y)) \<in> Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>.
                         (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C ((E \<otimes>\<^sub>o F)* o\<^sub>C\<^sub>L (E \<otimes>\<^sub>o F)) (\<psi> \<otimes>\<^sub>s \<phi>))\<close>
    apply (subst infsum_in_cweak_operator_topology_pointwise)
    using sum1 by (auto intro!: simp: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>((E,x),(F,y)) \<in> Rep_kraus_family \<EE> \<times> Rep_kraus_family \<FF>.
                     (\<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<psi>) * (\<phi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>))\<close>
    apply (rule infsum_cong)
    by (simp_all add: tensor_op_adjoint tensor_op_ell2)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x) \<in> Rep_kraus_family \<EE>. \<psi> \<bullet>\<^sub>C (E* o\<^sub>C\<^sub>L E) \<psi>)
                      * (\<Sum>\<^sub>\<infinity>(F,y) \<in> Rep_kraus_family \<FF>. \<phi> \<bullet>\<^sub>C (F* o\<^sub>C\<^sub>L F) \<phi>)\<close>
    apply (subst infsum_product')
    using sum2 sum3 by (simp_all add: case_prod_unfold)
  also have \<open>\<dots> = (\<psi> \<bullet>\<^sub>C kraus_family_bound \<EE> \<psi>) * (\<phi> \<bullet>\<^sub>C kraus_family_bound \<FF> \<phi>)\<close>
    unfolding kraus_family_bound.rep_eq case_prod_unfold
    apply (subst infsum_in_cweak_operator_topology_pointwise[symmetric])
    using sum4 apply (simp add: case_prod_unfold)
    apply (subst infsum_in_cweak_operator_topology_pointwise[symmetric])
    using sum5 apply (simp add: case_prod_unfold)
    by (rule refl)
  also have \<open>\<dots> = (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C ((kraus_family_bound \<EE> \<otimes>\<^sub>o kraus_family_bound \<FF>) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi>)\<close>
    by (simp add: tensor_op_ell2)
  finally show \<open>(\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C (kraus_family_bound (kraus_family_tensor_raw \<EE> \<FF>) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi>) =
       (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C ((kraus_family_bound \<EE> \<otimes>\<^sub>o kraus_family_bound \<FF>) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi>)\<close>
    by -
qed


lemma kraus_family_bound_tensor:
  \<open>kraus_family_bound (kraus_family_tensor \<EE> \<FF>) = kraus_family_bound \<EE> \<otimes>\<^sub>o kraus_family_bound \<FF>\<close>
  by (simp add: kraus_family_tensor_def kraus_family_map_outcome_bound kraus_family_bound_tensor_raw) 

lemma kraus_family_norm_tensor:
  \<open>kraus_family_norm (kraus_family_tensor \<EE> \<FF>) = kraus_family_norm \<EE> * kraus_family_norm \<FF>\<close>
  by (auto intro!: norm_cblinfun_mono
      simp add: kraus_family_norm_def kraus_family_bound_tensor
      simp flip: tensor_op_norm)

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

lemma kraus_family_filter_tensor:
  \<open>kraus_family_filter (\<lambda>(x,y). P x \<and> Q y) (kraus_family_tensor \<EE> \<FF>) = kraus_family_tensor (kraus_family_filter P \<EE>) (kraus_family_filter Q \<FF>)\<close>
  apply (auto intro!: arg_cong[where f=\<open>kraus_family_map_outcome _\<close>] simp: kraus_family_tensor_def kraus_family_filter_map_outcome)
  apply transfer
  by (force simp add: image_iff case_prod_unfold)

lemma kraus_family_map'_union_has_sum:
  assumes \<open>\<And>X Y. X\<in>F \<Longrightarrow> Y\<in>F \<Longrightarrow> X\<noteq>Y \<Longrightarrow> disjnt X Y\<close>
  shows \<open>((\<lambda>X. kraus_family_map' X \<EE> \<rho>) has_sum (kraus_family_map' (\<Union>F) \<EE> \<rho>)) F\<close>
proof -
  define EE EEf where \<open>EE = Rep_kraus_family \<EE>\<close> and \<open>EEf X = Set.filter (\<lambda>(E,x). x\<in>X) EE\<close> for X
  have inj: \<open>inj_on snd (SIGMA X:F. EEf X)\<close>
    using assms by (force intro!: simp: inj_on_def disjnt_def EEf_def)
  have snd_Sigma: \<open>snd ` (SIGMA X:F. EEf X) = EEf (\<Union>F)\<close>
    apply (auto simp: EEf_def)
    by force
  have map'_infsum: \<open>kraus_family_map' X \<EE> \<rho> = (\<Sum>\<^sub>\<infinity>(E, x)\<in>EEf X. sandwich_tc E \<rho>)\<close> for X
    by (simp add: kraus_family_map'_def kraus_family_map.rep_eq EEf_def kraus_family_filter.rep_eq EE_def case_prod_unfold)
  have has_sum: \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum (kraus_family_map' X \<EE> \<rho>)) (EEf X)\<close> for X
    using kraus_family_map_has_sum[of \<rho> \<open>kraus_family_filter (\<lambda>x. x \<in> X) \<EE>\<close>]
    by (simp add: kraus_family_map'_def kraus_family_filter.rep_eq EEf_def EE_def)
  then have \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum (kraus_family_map' (\<Union>F) \<EE> \<rho>)) (snd ` (SIGMA X:F. EEf X))\<close>
    by (simp add: snd_Sigma)
  then have \<open>((\<lambda>(X,(E,x)). sandwich_tc E \<rho>) has_sum (kraus_family_map' (\<Union>F) \<EE> \<rho>)) (SIGMA X:F. EEf X)\<close>
    apply (subst (asm) has_sum_reindex)
     apply (rule inj)
    by (simp add: o_def case_prod_unfold)
  then have \<open>((\<lambda>X. \<Sum>\<^sub>\<infinity>(E, x)\<in>EEf X. sandwich_tc E \<rho>) has_sum kraus_family_map' (\<Union> F) \<EE> \<rho>) F\<close>
    by (rule has_sum_Sigma'_banach)
  then show \<open>((\<lambda>X. kraus_family_map' X \<EE> \<rho>) has_sum kraus_family_map' (\<Union> F) \<EE> \<rho>) F\<close>
    by (auto intro: has_sum_cong[THEN iffD2, rotated] simp: map'_infsum)
qed


lemma kraus_family_map'_union_eqI:
  assumes \<open>\<And>X. X\<in>F \<Longrightarrow> kraus_family_map' X \<EE> \<rho> = kraus_family_map' X \<FF> \<rho>\<close>
  assumes \<open>\<And>X Y. X\<in>F \<Longrightarrow> Y\<in>F \<Longrightarrow> X\<noteq>Y \<Longrightarrow> disjnt X Y\<close>
  shows \<open>kraus_family_map' (\<Union>F) \<EE> \<rho> = kraus_family_map' (\<Union>F) \<FF> \<rho>\<close>
proof -
  have \<open>((\<lambda>X. kraus_family_map' X \<EE> \<rho>) has_sum kraus_family_map' (\<Union> F) \<EE> \<rho>) F\<close>
    using assms(2) by (rule kraus_family_map'_union_has_sum)
  moreover have \<open>((\<lambda>X. kraus_family_map' X \<FF> \<rho>) has_sum kraus_family_map' (\<Union> F) \<FF> \<rho>) F\<close>
    using assms(2) by (rule kraus_family_map'_union_has_sum)
  then have \<open>((\<lambda>X. kraus_family_map' X \<EE> \<rho>) has_sum kraus_family_map' (\<Union> F) \<FF> \<rho>) F\<close>
    using assms(1) by (rule has_sum_cong[THEN iffD2, rotated])
  ultimately show ?thesis
    using has_sum_unique by blast
qed


lemma kraus_family_map'_UNIV[simp]: \<open>kraus_family_map' UNIV = kraus_family_map\<close>
  by (auto intro!: ext simp: kraus_family_map'_def)

lemma kraus_equivalent'_imp_equivalent:
  assumes \<open>kraus_equivalent' \<EE> \<FF>\<close>
  shows \<open>kraus_equivalent \<EE> \<FF>\<close>
  using kraus_family_map'_union_eqI[where F=\<open>range (\<lambda>x. {x})\<close> and \<EE>=\<EE> and \<FF>=\<FF>] assms
  by (force intro!: ext simp: kraus_equivalent'_def kraus_equivalent_def)


lemma kraus_family_filter_cong:
  assumes \<open>kraus_equivalent' \<EE> \<FF>\<close>
  shows \<open>kraus_equivalent' (kraus_family_filter P \<EE>) (kraus_family_filter P \<FF>)\<close>
proof (unfold kraus_equivalent'_def, intro allI)
  fix x
  have \<open>kraus_family_map (kraus_family_filter (\<lambda>xa. xa = x \<and> P xa) \<EE>)
      = kraus_family_map (kraus_family_filter (\<lambda>xa. xa = x \<and> P xa) \<FF>)\<close>
  proof (cases \<open>P x\<close>)
    case True
    then have \<open>(z = x \<and> P z) \<longleftrightarrow> (z = x)\<close> for z
      by auto
    with assms show ?thesis
      by (simp add: kraus_equivalent'_def kraus_family_map'_def)
  next
    case False
    then have [simp]: \<open>(z = x \<and> P z) \<longleftrightarrow> False\<close> for z
      by auto
    show ?thesis
      by (simp add: kraus_equivalent'_def kraus_family_map'_def)
  qed
  then show \<open>kraus_family_map' {x} (kraus_family_filter P \<EE>) = kraus_family_map' {x} (kraus_family_filter P \<FF>)\<close>
    by (simp add: kraus_family_map'_def kraus_family_filter_twice)
qed


lemma kraus_family_tensor_cong':
  fixes \<EE> \<EE>' :: \<open>('a ell2, 'b ell2, 'x) kraus_family\<close>
    and \<FF> \<FF>' :: \<open>('c ell2, 'd ell2, 'y) kraus_family\<close>
  assumes \<open>kraus_equivalent' \<EE> \<EE>'\<close>
  assumes \<open>kraus_equivalent' \<FF> \<FF>'\<close>
  shows \<open>kraus_equivalent' (kraus_family_tensor \<EE> \<FF>) (kraus_family_tensor \<EE>' \<FF>')\<close>
proof (rule kraus_equivalent'I)
  fix xy :: \<open>'x \<times> 'y\<close> and \<rho>
  obtain x y where [simp]: \<open>xy = (x,y)\<close>
    by fastforce
  have aux1: \<open>(\<lambda>xy'. xy' = (x, y)) = (\<lambda>(x', y'). x' = x \<and> y' = y)\<close>
    by auto
  have \<open>kraus_family_map' {xy} (kraus_family_tensor \<EE> \<FF>) \<rho>
         = kraus_family_map (kraus_family_tensor (kraus_family_filter (\<lambda>z. z = x) \<EE>) (kraus_family_filter (\<lambda>z. z = y) \<FF>)) \<rho>\<close>
    by (simp add: kraus_family_map'_def aux1 kraus_family_filter_tensor)
  also have \<open>\<dots> = kraus_family_map (kraus_family_tensor (kraus_family_filter (\<lambda>z. z = x) \<EE>') (kraus_family_filter (\<lambda>z. z = y) \<FF>')) \<rho>\<close>
    by (intro kraus_map_eqI kraus_tensor_cong kraus_equivalent'_imp_equivalent kraus_family_filter_cong assms)
  also have \<open>\<dots> = kraus_family_map' {xy} (kraus_family_tensor \<EE>' \<FF>') \<rho>\<close>
    by (simp add: kraus_family_map'_def aux1 kraus_family_filter_tensor)
  finally show \<open>kraus_family_map' {xy} (kraus_family_tensor \<EE> \<FF>) \<rho> = kraus_family_map' {xy} (kraus_family_tensor \<EE>' \<FF>') \<rho>\<close>
    by -
qed


(* lift_definition kraus_map_tensor :: \<open>('a ell2, 'b ell2) kraus_map \<Rightarrow> ('c ell2, 'd ell2) kraus_map \<Rightarrow> (('a\<times>'c) ell2, ('b\<times>'d) ell2) kraus_map\<close> is
  \<open>\<lambda>\<EE> \<FF>. kraus_family_flatten (kraus_family_tensor \<EE> \<FF>)\<close>
  by (intro kraus_equivalent_kraus_family_map_outcome_left kraus_equivalent_kraus_family_map_outcome_right kraus_tensor_cong) *)

(* lemma kraus_map_tensor:
  shows \<open>kraus_map_apply (kraus_map_tensor \<EE> \<FF>) (tc_tensor \<rho> \<sigma>) = tc_tensor (kraus_map_apply \<EE> \<rho>) (kraus_map_apply \<FF> \<sigma>)\<close>
  apply (transfer fixing: \<rho> \<sigma>)
  by (simp add: kraus_equivalent_def kraus_family_map_outcome_same_map kraus_family_map_tensor) *)

lemma kraus_map_tensor_compose_distribute:
  shows \<open>kraus_equivalent (kraus_family_tensor (kraus_family_comp \<EE> \<FF>) (kraus_family_comp \<GG> \<HH>))
                          (kraus_family_comp (kraus_family_tensor \<EE> \<GG>) (kraus_family_tensor \<FF> \<HH>))\<close>
  by (auto intro!: eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor]
      kraus_family_map_bounded_clinear comp_bounded_clinear
      simp: kraus_equivalent_def kraus_family_map_tensor kraus_family_comp_apply)

(* lemma kraus_map_tensor_compose_distribute:
  shows \<open>kraus_map_tensor (kraus_map_comp \<EE> \<FF>) (kraus_map_comp \<GG> \<HH>) = kraus_map_comp (kraus_map_tensor \<EE> \<GG>) (kraus_map_tensor \<FF> \<HH>)\<close>
  apply (intro kraus_map_apply_inj cblinfun_apply_inject[THEN iffD1] eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
  by (auto intro!: bounded_linear_intros simp: kraus_map_tensor kraus_map_apply_comp o_def) *)

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

lemma trace_kraus_family_is_trace': 
  assumes \<open>is_onb B\<close>
  shows \<open>trace_tc t = one_dim_iso (kraus_family_map (trace_kraus_family B) t)\<close>
  by (simp add: trace_kraus_family_is_trace assms)

(* lemma trace_kraus_map_is_trace': \<open>trace_tc t = one_dim_iso (kraus_map_apply trace_kraus_map t)\<close>
  apply (transfer fixing: t)
  by (simp add: kraus_family_map_outcome_same_map trace_kraus_family_is_trace) *)

lift_definition kraus_map_domain :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family \<Rightarrow> 'x set\<close> is
  \<open>\<lambda>\<EE>. snd ` Set.filter (\<lambda>(E,x). E \<noteq> 0) \<EE>\<close>.

lemma kraus_family_map_map_outcome_inj:
  assumes \<open>inj_on f (kraus_map_domain \<EE>)\<close>
  shows \<open>kraus_family_map (kraus_family_map_outcome_inj f \<EE>) \<rho> = kraus_family_map \<EE> \<rho>\<close>
proof -
  define EE where \<open>EE = Set.filter (\<lambda>(E,x). E\<noteq>0) (Rep_kraus_family \<EE>)\<close>
  have \<open>kraus_family_map (kraus_family_map_outcome_inj f \<EE>) \<rho> = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>(E, x). (E, f x)) ` Rep_kraus_family \<EE>. sandwich_tc (fst E) \<rho>)\<close>
    by (simp add: kraus_family_map.rep_eq kraus_family_map_outcome_inj.rep_eq)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>(E, x). (E, f x)) ` EE. sandwich_tc (fst E) \<rho>)\<close>
    apply (rule infsum_cong_neutral)
      apply (auto simp: EE_def)
    by fastforce
  also have \<open>\<dots> = infsum ((\<lambda>E. sandwich_tc (fst E) \<rho>) \<circ> (\<lambda>(E, x). (E, f x))) EE\<close>
    apply (rule infsum_reindex)
    using assms
    apply (auto intro!: simp: inj_on_def kraus_map_domain.rep_eq EE_def)
    by (metis (mono_tags, lifting) Set.member_filter case_prodI snd_conv)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>EE. sandwich_tc E \<rho>)\<close>
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. sandwich_tc E \<rho>)\<close>
    apply (rule infsum_cong_neutral)
    by (auto simp: EE_def)
  also have \<open>\<dots> = kraus_family_map \<EE> \<rho>\<close>
    by (metis (no_types, lifting) infsum_cong kraus_family_map.rep_eq prod.case_eq_if)
  finally show \<open>kraus_family_map (kraus_family_map_outcome_inj f \<EE>) \<rho> = kraus_family_map \<EE> \<rho>\<close>
    by -
qed



lemma kraus_equivalent'_map_outcome_inj:
  assumes \<open>inj_on f (kraus_map_domain \<EE>)\<close>
  shows \<open>kraus_equivalent' (kraus_family_map_outcome_inj f \<EE>) (kraus_family_map_outcome f \<EE>)\<close>
proof (rule kraus_equivalent'I)
  fix x \<rho>
  define \<EE>fx where \<open>\<EE>fx = kraus_family_filter (\<lambda>z. f z = x) \<EE>\<close>
  from assms have inj_\<EE>fx: \<open>inj_on f (kraus_map_domain \<EE>fx)\<close>
    by (simp add: inj_on_def kraus_map_domain.rep_eq \<EE>fx_def kraus_family_filter.rep_eq)
  have \<open>kraus_family_map' {x} (kraus_family_map_outcome_inj f \<EE>) \<rho> = kraus_family_map (kraus_family_filter (\<lambda>z. z=x) (kraus_family_map_outcome_inj f \<EE>)) \<rho>\<close>
    by (simp add: kraus_family_map'_def)
  also have \<open>\<dots> = kraus_family_map (kraus_family_map_outcome_inj f \<EE>fx) \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kraus_family_map t \<rho>\<close>])
    unfolding \<EE>fx_def
    apply (transfer' fixing: f)
    by force
  also have \<open>\<dots> = kraus_family_map \<EE>fx \<rho>\<close>
    using inj_\<EE>fx by (rule kraus_family_map_map_outcome_inj)
  also have \<open>\<dots> = kraus_family_map (kraus_family_map_outcome f (kraus_family_filter (\<lambda>z. f z = x) \<EE>)) \<rho>\<close>
    by (simp add: \<EE>fx_def)
  also have \<open>\<dots> = kraus_family_map (kraus_family_filter (\<lambda>xa. xa = x) (kraus_family_map_outcome f \<EE>)) \<rho>\<close>
    apply (subst kraus_family_filter_map_outcome)
    by simp
  also have \<open>\<dots> = kraus_family_map' {x} (kraus_family_map_outcome f \<EE>) \<rho>\<close>
    by (simp add: kraus_family_map'_def)
  finally show \<open>kraus_family_map' {x} (kraus_family_map_outcome_inj f \<EE>) \<rho> = kraus_family_map' {x} (kraus_family_map_outcome f \<EE>) \<rho>\<close>
    by -
qed



lemma 
  fixes \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'x) kraus_family\<close>
  assumes \<open>inj_on f (kraus_map_domain \<EE>)\<close>
  shows kraus_family_map_outcome_inj_same_map[simp]: \<open>kraus_family_map (kraus_family_map_outcome_inj f \<EE>) = kraus_family_map \<EE>\<close>
    and kraus_family_map_outcome_inj_bound: \<open>kraus_family_bound (kraus_family_map_outcome_inj f \<EE>) = kraus_family_bound \<EE>\<close>
    and kraus_family_map_outcome_inj_norm[simp]: \<open>kraus_family_norm (kraus_family_map_outcome_inj f \<EE>) = kraus_family_norm \<EE>\<close>
  apply (metis assms kraus_equivalent'_imp_equivalent kraus_equivalent'_map_outcome_inj kraus_equivalent_def kraus_family_map_outcome_same_map)
  apply (metis assms kraus_equivalent'_imp_equivalent kraus_equivalent'_map_outcome_inj kraus_family_bound_welldefined kraus_family_map_outcome_bound)
  using assms kraus_equivalent'_imp_equivalent kraus_equivalent'_map_outcome_inj kraus_family_norm_welldefined by fastforce


definition kraus_map_partial_trace :: \<open>'b ell2 set \<Rightarrow> (('a\<times>'b) ell2, 'a ell2, 'b) kraus_family\<close> where
\<open>kraus_map_partial_trace B = kraus_family_map_outcome (\<lambda>((_,b),_). inv ket b)
(kraus_family_comp (kraus_family_of_op (tensor_ell2_right (ket ())*))
 (kraus_family_tensor kraus_family_id (trace_kraus_family B)))\<close>

lemma partial_trace_as_kraus_map: 
  fixes B :: \<open>'b ell2 set\<close>
  assumes \<open>is_onb B\<close>
  shows \<open>partial_trace t = kraus_family_map (kraus_map_partial_trace B) t\<close>
(* TODO: also "kraus_map_apply (kraus_map_tensor kraus_map_id kraus_map_trace) t = ... partial_trace ... *)
proof -
  have \<open>partial_trace t = kraus_family_map (kraus_family_of_op (tensor_ell2_right (ket ())*))
  (kraus_family_map (kraus_family_tensor kraus_family_id (trace_kraus_family B)) t)\<close>
  proof (rule fun_cong[where x=t], rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
    show \<open>bounded_clinear partial_trace\<close>
      by simp
    show \<open>bounded_clinear
     (\<lambda>t. kraus_family_map (kraus_family_of_op (tensor_ell2_right (ket ())*))
           (kraus_family_map (kraus_family_tensor kraus_family_id (trace_kraus_family B)) t))\<close>
      by (intro bounded_linear_intros)
    fix \<rho> :: \<open>('a ell2, 'a ell2) trace_class\<close> and \<sigma> :: \<open>('b ell2, 'b ell2) trace_class\<close>
    show \<open>partial_trace (tc_tensor \<rho> \<sigma>) =
           kraus_family_map (kraus_family_of_op (tensor_ell2_right (ket ())*))
            (kraus_family_map (kraus_family_tensor kraus_family_id (trace_kraus_family B)) (tc_tensor \<rho> \<sigma>))\<close>
       apply (auto intro!: from_trace_class_inject[THEN iffD1]
          simp: assms partial_trace_tensor kraus_family_map_tensor trace_kraus_family_is_trace kraus_family_of_op_apply
          from_trace_class_sandwich_tc sandwich_apply trace_tc.rep_eq tc_tensor.rep_eq scaleC_trace_class.rep_eq)
      by (auto intro!: cblinfun_eqI simp: tensor_op_ell2 ket_CARD_1_is_1)
  qed
  then show ?thesis
    by (simp add: kraus_map_partial_trace_def kraus_family_comp_apply)
qed

(* lemma partial_trace_as_kraus_map: \<open>partial_trace t = 
  kraus_map_apply (kraus_map_of_op (tensor_ell2_right 1* ))
  (kraus_map_apply (kraus_map_tensor kraus_map_id trace_kraus_map) t)\<close>
(* TODO: also "kraus_map_apply (kraus_map_tensor kraus_map_id kraus_map_trace) t = ... partial_trace ... *)
proof (rule fun_cong[where x=t], rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
  show \<open>bounded_clinear partial_trace\<close>
    by simp
  show \<open>bounded_clinear
     (\<lambda>a. kraus_map_apply (kraus_map_of_op (tensor_ell2_right 1* ))
           (kraus_map_apply (kraus_map_tensor kraus_map_id trace_kraus_map) a))\<close>
    by (intro bounded_linear_intros)
  fix \<rho> :: \<open>('a ell2, 'a ell2) trace_class\<close> and \<sigma> :: \<open>('b ell2, 'b ell2) trace_class\<close>
  show \<open>partial_trace (tc_tensor \<rho> \<sigma>) =
           kraus_map_apply (kraus_map_of_op (tensor_ell2_right 1* ))
           (kraus_map_apply (kraus_map_tensor kraus_map_id trace_kraus_map) (tc_tensor \<rho> \<sigma>))\<close>
    apply (auto intro!: from_trace_class_inject[THEN iffD1]
        simp: partial_trace_tensor kraus_map_tensor trace_kraus_map_is_trace kraus_map_of_op_apply
        from_trace_class_sandwich_tc sandwich_apply trace_tc.rep_eq tc_tensor.rep_eq scaleC_trace_class.rep_eq)
    by (auto intro!: cblinfun_eqI simp: tensor_op_ell2)
qed *)

lemma partial_trace_ignore_trace_preserving_map:
  assumes \<open>trace_preserving_map (kraus_family_map \<EE>)\<close>
  shows \<open>partial_trace (kraus_family_map (kraus_family_tensor kraus_family_id \<EE>) \<rho>) = partial_trace \<rho>\<close>
proof (rule fun_cong[where x=\<rho>], rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
  show \<open>bounded_clinear (\<lambda>a. partial_trace (kraus_family_map (kraus_family_tensor kraus_family_id \<EE>) a))\<close>
    by (intro bounded_linear_intros)
  show \<open>bounded_clinear partial_trace\<close>
    by (intro bounded_linear_intros)
  fix \<rho> :: \<open>('d ell2, 'd ell2) trace_class\<close> and \<sigma> :: \<open>('a ell2, 'a ell2) trace_class\<close>
  from assms
  show \<open>partial_trace (kraus_family_map (kraus_family_tensor kraus_family_id \<EE>) (tc_tensor \<rho> \<sigma>)) =
           partial_trace (tc_tensor \<rho> \<sigma>)\<close>
  (* show \<open>partial_trace (kraus_map_apply (kraus_map_tensor kraus_map_id \<EE>) (tc_tensor \<rho> \<sigma>)) = partial_trace (tc_tensor \<rho> \<sigma>)\<close> *)
    by (auto intro!: simp: kraus_family_map_tensor partial_trace_tensor trace_preserving_map_def)
qed

(* lemma kraus_map_comp_id_left[simp]: \<open>kraus_map_comp kraus_map_id \<EE> = \<EE>\<close>
  by (auto intro!: kraus_map_apply_inj cblinfun_eqI simp: kraus_map_apply_comp kraus_map_id_apply)

lemma kraus_map_comp_id_right[simp]: \<open>kraus_map_comp \<EE> kraus_map_id = \<EE>\<close>
  by (auto intro!: kraus_map_apply_inj cblinfun_eqI simp: kraus_map_apply_comp kraus_map_id_apply) *)


lemma kraus_family_reconstruct_is_family:
  assumes \<open>bounded_clinear \<EE>\<close> (* Is this necessary? *)
  assumes sum: \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum \<EE> \<rho>) A\<close>
  defines \<open>F \<equiv> (\<lambda>a. (f a,a)) ` A\<close>
  shows \<open>kraus_family F\<close>
proof -
  from \<open>bounded_clinear \<EE>\<close> obtain B where B: \<open>norm (\<EE> \<rho>) \<le> B * norm \<rho>\<close> for \<rho>
    apply atomize_elim
    by (simp add: bounded_clinear_axioms_def bounded_clinear_def mult.commute)
  show ?thesis
  proof (intro kraus_familyI bdd_aboveI2)
    fix S assume \<open>S \<in> {S. finite S \<and> S \<subseteq> F}\<close>
    then have \<open>S \<subseteq> F\<close> and \<open>finite S\<close>
      by auto
    then obtain A' where \<open>finite A'\<close> and \<open>A' \<subseteq> A\<close> and S_A': \<open>S = (\<lambda>a. (f a,a)) ` A'\<close>
      by (metis (no_types, lifting) F_def finite_subset_image)
    show \<open>(\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> B *\<^sub>C id_cblinfun\<close>
    proof (rule cblinfun_leI)
      fix h :: 'a assume \<open>norm h = 1\<close>
      have \<open>h \<bullet>\<^sub>C ((\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) h) = h \<bullet>\<^sub>C (\<Sum>a\<in>A'. (f a)* o\<^sub>C\<^sub>L f a) h\<close>
        by (simp add: S_A' sum.reindex inj_on_def)
      also have \<open>\<dots> = (\<Sum>a\<in>A'. h \<bullet>\<^sub>C ((f a)* o\<^sub>C\<^sub>L f a) h)\<close>
        apply (rule complex_vector.linear_sum)
        by (simp add: bounded_clinear.clinear bounded_clinear_cinner_right_comp) 
      also have \<open>\<dots> = (\<Sum>a\<in>A'. trace_tc (sandwich_tc (f a) (tc_butterfly h h)))\<close>
        by (auto intro!: sum.cong[OF refl]
            simp: trace_tc.rep_eq from_trace_class_sandwich_tc (* sandwich_apply *)
            tc_butterfly.rep_eq cblinfun_comp_butterfly sandwich_apply trace_butterfly_comp)
      also have \<open>\<dots> = trace_tc (\<Sum>a\<in>A'. sandwich_tc (f a) (tc_butterfly h h))\<close>
        apply (rule complex_vector.linear_sum[symmetric])
        using clinearI trace_tc_plus trace_tc_scaleC by blast
      also have \<open>\<dots> = trace_tc (\<Sum>\<^sub>\<infinity>a\<in>A'. sandwich_tc (f a) (tc_butterfly h h))\<close>
        by (simp add: \<open>finite A'\<close>)
      also have \<open>\<dots> \<le> trace_tc (\<Sum>\<^sub>\<infinity>a\<in>A. (sandwich_tc (f a) (tc_butterfly h h)))\<close>
        apply (intro trace_tc_mono infsum_mono_neutral_traceclass)
        using \<open>A' \<subseteq> A\<close> sum[of \<open>tc_butterfly h h\<close>]
        by (auto intro!: sandwich_tc_pos has_sum_imp_summable simp: \<open>finite A'\<close>)
      also have \<open>\<dots> = trace_tc (\<EE> (tc_butterfly h h))\<close>
        by (metis sum infsumI)
      also have \<open>\<dots> = norm (\<EE> (tc_butterfly h h))\<close>
        by (metis (no_types, lifting) infsumI infsum_nonneg_traceclass norm_tc_pos sandwich_tc_pos sum tc_butterfly_pos)
      also from B have \<open>\<dots> \<le> B * norm (tc_butterfly h h)\<close>
        using complex_of_real_mono by blast
      also have \<open>\<dots> = B\<close>
        by (simp add: \<open>norm h = 1\<close> norm_tc_butterfly)
      also have \<open>\<dots> = h \<bullet>\<^sub>C (complex_of_real B *\<^sub>C id_cblinfun *\<^sub>V h)\<close>
        using \<open>norm h = 1\<close> cnorm_eq_1 by auto
      finally show \<open>h \<bullet>\<^sub>C ((\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) *\<^sub>V h) \<le> h \<bullet>\<^sub>C (complex_of_real B *\<^sub>C id_cblinfun *\<^sub>V h)\<close>
        by -
    qed
  qed
qed

lemma kraus_family_reconstruct:
  assumes \<open>bounded_clinear \<EE>\<close> (* Is this necessary? *)
  assumes sum: \<open>\<And>\<rho>. ((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum \<EE> \<rho>) A\<close>
  defines \<open>F \<equiv> Abs_kraus_family ((\<lambda>a. (f a,a)) ` A)\<close>
  shows \<open>kraus_family_map F = \<EE>\<close>
proof (rule ext)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  have Rep_F: \<open>Rep_kraus_family F = (\<lambda>a. (f a,a)) ` A\<close>
    unfolding F_def
    apply (rule Abs_kraus_family_inverse)
    by (auto intro!: kraus_family_reconstruct_is_family[of \<EE>] assms simp: F_def)
  have \<open>((\<lambda>(E,x). sandwich_tc E \<rho>) has_sum kraus_family_map F \<rho>) (Rep_kraus_family F)\<close>
    by (auto intro!: kraus_family_map_has_sum)
  then have \<open>((\<lambda>a. sandwich_tc (f a) \<rho>) has_sum kraus_family_map F \<rho>) A\<close>
    unfolding Rep_F
    apply (subst (asm) has_sum_reindex)
    by (auto simp: inj_on_def o_def)
  with sum show \<open>kraus_family_map F \<rho> = \<EE> \<rho>\<close>
    by (metis (no_types, lifting) infsumI)
qed

lemma complete_measurement_idem[simp]:
  \<open>kraus_family_map (complete_measurement B) (kraus_family_map (complete_measurement B) \<rho>)
      = kraus_family_map (complete_measurement B) \<rho>\<close>
proof (cases \<open>is_ortho_set B\<close>)
  case True
  have \<open>(\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. 
            sandwich_tc (fst E) (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. sandwich_tc (fst E) \<rho>)) =
        (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. sandwich_tc (fst E) \<rho>)\<close>
  proof (rule infsum_cong)
    fix hh assume hh_B: \<open>hh \<in> (\<lambda>h. (selfbutter (sgn h), h)) ` B\<close>
    then obtain h where \<open>h \<in> B\<close> and [simp]: \<open>hh = (selfbutter (sgn h), h)\<close>
      by blast
    from kraus_family_map_abs_summable[OF complete_measurement_is_family[OF \<open>is_ortho_set B\<close>]]
    have summ: \<open>(\<lambda>x. sandwich_tc (fst x) \<rho>) summable_on (\<lambda>x. (selfbutter (sgn x), x)) ` B\<close>
      by (auto intro: abs_summable_summable simp: case_prod_beta)
    have \<open>sandwich_tc (selfbutter (sgn h)) (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. sandwich_tc (fst E) \<rho>)
            = (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. sandwich_tc (selfbutter (sgn h)) (sandwich_tc (fst E) \<rho>))\<close>
      apply (rule infsum_bounded_linear[unfolded o_def, symmetric])
       apply (intro bounded_linear_intros)
      by (rule summ)
    also have \<open>\<dots> = sandwich_tc (selfbutter (sgn h)) \<rho>\<close>
    proof (subst infsum_single[where i=hh])
      fix hh' assume \<open>hh' \<noteq> hh\<close> and \<open>hh' \<in> (\<lambda>h. (selfbutter (sgn h), h)) ` B\<close>
      then obtain h' where \<open>h' \<in> B\<close> and [simp]: \<open>hh' = (selfbutter (sgn h'), h')\<close>
        by blast
      with \<open>hh' \<noteq> hh\<close> have \<open>h \<noteq> h'\<close>
        by force
      then have *: \<open>sgn h \<bullet>\<^sub>C sgn h' = 0\<close>
        using True \<open>h \<in> B\<close> \<open>h' \<in> B\<close> is_ortho_set_def by fastforce
      show \<open>sandwich_tc (selfbutter (sgn h)) (sandwich_tc (fst hh') \<rho>) = 0\<close>
        by (simp add: * flip: sandwich_tc_compose[unfolded o_def, THEN fun_cong])
    next
      have *: \<open>sgn h \<bullet>\<^sub>C sgn h = 1\<close>
        by (metis True \<open>h \<in> B\<close> cnorm_eq_1 is_ortho_set_def norm_sgn)
      have \<open>(if hh \<in> (\<lambda>x. (selfbutter (sgn x), x)) ` B then sandwich_tc (selfbutter (sgn h)) (sandwich_tc (fst hh) \<rho>) else 0)
      = sandwich_tc (selfbutter (sgn h)) (sandwich_tc (fst hh) \<rho>)\<close> (is \<open>?lhs = _\<close>)
        using hh_B by presburger
      also have \<open>\<dots> = sandwich_tc (selfbutter (sgn h)) \<rho>\<close>
        by (simp add: * flip: sandwich_tc_compose[unfolded o_def, THEN fun_cong])
      finally show \<open>?lhs = \<dots>\<close>
        by -
    qed
    finally show \<open>sandwich_tc (fst hh) (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. sandwich_tc (fst E) \<rho>) = sandwich_tc (fst hh) \<rho>\<close>
      by simp
  qed
  with True show ?thesis
    apply (transfer fixing: B \<rho>)
    by simp
next
  case False
  then show ?thesis
    apply (transfer fixing: B \<rho>)
    by simp
qed


lemma kraus_family_map_complete_measurement:
  assumes [simp]: \<open>is_ortho_set B\<close>
  shows \<open>kraus_family_map (complete_measurement B) t = 
    (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter (sgn x)) t)\<close>
proof -
  have \<open>kraus_family_map (complete_measurement B) t = 
      (\<Sum>\<^sub>\<infinity>E\<in>(\<lambda>x. (selfbutter (sgn x), x)) ` B. sandwich_tc (fst E) t)\<close>
    apply (transfer' fixing: B t)
    by simp
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter (sgn x)) t)\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def)
  finally show ?thesis
    by -
qed

lemma kraus_family_map_complete_measurement_onb:
  assumes \<open>is_onb B\<close>
  shows \<open>kraus_family_map (complete_measurement B) t = 
    (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter x) t)\<close>
proof -
  have [simp]: \<open>is_ortho_set B\<close>
    using assms by (simp add: is_onb_def)
  have [simp]: \<open>sgn x = x\<close> if \<open>x \<in> B\<close> for x
    using assms that
    by (simp add: is_onb_def sgn_div_norm)
  have \<open>kraus_family_map (complete_measurement B) t = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter (sgn x)) t)\<close>
    by (simp add: kraus_family_map_complete_measurement)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B. sandwich_tc (selfbutter x) t)\<close>
    apply (rule infsum_cong)
    by simp
  finally show ?thesis
    by -
qed

lemma kraus_family_map_complete_measurement_ket:
  \<open>kraus_family_map (complete_measurement (range ket)) t = 
    (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x)) t)\<close>
proof -
  have \<open>kraus_family_map (complete_measurement (range ket)) t = 
    (\<Sum>\<^sub>\<infinity>x\<in>range ket. sandwich_tc (selfbutter x) t)\<close>
    by (simp add: kraus_family_map_complete_measurement_onb)
  also have \<open>\<dots>  = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x)) t)\<close>
    by (simp add: infsum_reindex o_def)
  finally show ?thesis
    by -
qed

lift_definition constant_kraus_family :: \<open>('b,'b) trace_class \<Rightarrow> ('a::one_dim, 'b::chilbert_space, unit) kraus_family\<close> is
  \<open>\<lambda>t::('b,'b) trace_class. if t \<ge> 0 then
    (\<lambda>v. (vector_to_cblinfun v,())) ` spectral_dec_vecs_tc t
  else {}\<close>
proof (rule CollectI, rename_tac t)
(* TODO why does this wlog not work:

  fix t :: \<open>('b,'b) trace_class\<close>
  let ?thesis = \<open>kraus_family (if selfadjoint_tc t then range (\<lambda>n. (vector_to_cblinfun (spectral_dec_vec_tc t n) :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b, n)) else {})\<close>
  wlog self_adjoint: \<open>selfadjoint_tc t\<close> 
    goal ?thesis
    using hypothesis by auto
  fix t :: \<open>('b,'b) trace_class\<close>
  assume  \<open>selfadjoint_tc t\<close> 
  show \<open>kraus_family
          (if selfadjoint_tc t then range (\<lambda>n. (vector_to_cblinfun (spectral_dec_vec_tc t n) :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b, n)) else {})\<close>
  show \<open>kraus_family (if selfadjoint_tc t then range (\<lambda>n. (vector_to_cblinfun (spectral_dec_vec_tc t n) :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b, n)) else {})\<close>
*)
  fix t :: \<open>('b,'b) trace_class\<close>
  show \<open>kraus_family (if t \<ge> 0 then (\<lambda>v. (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b,())) ` spectral_dec_vecs_tc t else {})\<close>
  proof (cases \<open>t \<ge> 0\<close>)
    case True
    have \<open>kraus_family ((\<lambda>v. (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b,())) ` spectral_dec_vecs_tc t)\<close>
    proof (intro kraus_familyI bdd_aboveI, rename_tac E)
      fix E :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
      assume \<open>E \<in> (\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> (\<lambda>v. (vector_to_cblinfun v, ())) ` spectral_dec_vecs_tc t}\<close>
      then obtain F where E_def: \<open>E = (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close> and \<open>finite F\<close> and \<open>F \<subseteq> (\<lambda>v. (vector_to_cblinfun v, ())) ` spectral_dec_vecs_tc t\<close>
        by blast
      then obtain F' where F_def: \<open>F = (\<lambda>v. (vector_to_cblinfun v, ())) ` F'\<close> and \<open>finite F'\<close> and F'_subset: \<open>F' \<subseteq> spectral_dec_vecs_tc t\<close>
        by (meson finite_subset_image)
      have inj: \<open>inj_on (\<lambda>v. (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b, ())) F'\<close>
      proof (rule inj_onI, rule ccontr)
        fix x y
        assume \<open>x \<in> F'\<close> and \<open>y \<in> F'\<close>
        assume eq: \<open>(vector_to_cblinfun x :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b, ()) = (vector_to_cblinfun y, ())\<close>
        assume \<open>x \<noteq> y\<close>
        have ortho: \<open>is_ortho_set (spectral_dec_vecs (from_trace_class t))\<close>
          using True
          by (auto intro!: spectral_dec_vecs_ortho trace_class_compact pos_selfadjoint
              simp: selfadjoint_tc.rep_eq from_trace_class_pos)
        with \<open>x \<noteq> y\<close> F'_subset \<open>x \<in> F'\<close> \<open>y \<in> F'\<close>
        have \<open>x \<bullet>\<^sub>C y = 0\<close>
          by (auto simp: spectral_dec_vecs_tc.rep_eq is_ortho_set_def)
        then have \<open>(vector_to_cblinfun x :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b)* o\<^sub>C\<^sub>L (vector_to_cblinfun y :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b) = 0\<close>
          by simp
        with eq have \<open>(vector_to_cblinfun x :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b)= 0\<close>
          by force
        then have \<open>norm x = 0\<close>
          by (smt (verit, del_insts) norm_vector_to_cblinfun norm_zero)
        with ortho F'_subset \<open>x \<in> F'\<close> show False
          by (auto simp: spectral_dec_vecs_tc.rep_eq is_ortho_set_def)
      qed
      have \<open>E = (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close>
        by (simp add: E_def)
      also have \<open>\<dots> = (\<Sum>v\<in>F'. (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b)* o\<^sub>C\<^sub>L vector_to_cblinfun v)\<close>
        unfolding F_def
        apply (subst sum.reindex)
        by (auto intro!: inj)
      also have \<open>\<dots> = (\<Sum>v\<in>F'. ((norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1)\<close>
        by (auto intro!: sum.cong simp: power2_norm_eq_cinner scaleR_scaleC)
      also have \<open>\<dots> = (\<Sum>v\<in>F'. (norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1\<close>
        by (metis scaleR_left.sum)
      also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>v\<in>F'. (norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1\<close>
        using \<open>finite F'\<close> by force
      also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>v\<in>spectral_dec_vecs_tc t. (norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1\<close>
        apply (intro scaleR_right_mono infsum_mono_neutral)
        using F'_subset
        by (auto intro!: one_dim_cblinfun_one_pos spectral_dec_vec_tc_norm_summable True
            simp: \<open>finite F'\<close> )
      finally show \<open>E \<le> (\<Sum>\<^sub>\<infinity>v\<in>spectral_dec_vecs_tc t. (norm (vector_to_cblinfun v :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b))\<^sup>2) *\<^sub>R 1\<close>
        by -
    qed
    with True show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by simp
  qed
qed

lemma vector_to_cblinfun_inj: \<open>inj_on (vector_to_cblinfun :: 'a::complex_normed_vector \<Rightarrow> 'b::one_dim \<Rightarrow>\<^sub>C\<^sub>L _) X\<close>
proof (rule inj_onI)
  fix x y :: 'a
  assume \<open>vector_to_cblinfun x = (vector_to_cblinfun y :: 'b \<Rightarrow>\<^sub>C\<^sub>L _)\<close>
  then have \<open>vector_to_cblinfun x (1::'b) = vector_to_cblinfun y (1::'b)\<close>
    by simp
  then show \<open>x = y\<close>
    by simp
qed

lemma kraus_family_map_constant: 
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kraus_family_map (constant_kraus_family \<rho>) \<sigma> = one_dim_iso \<sigma> *\<^sub>C \<rho>\<close>
proof -
  have \<open>kraus_family_map (constant_kraus_family \<rho>) \<sigma>
         = (\<Sum>\<^sub>\<infinity>(E,x)\<in>(\<lambda>v. (vector_to_cblinfun v, ())) ` spectral_dec_vecs_tc \<rho>. sandwich_tc E \<sigma>)\<close>
    by (simp add: assms kraus_family_map.rep_eq constant_kraus_family.rep_eq case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>v \<in> spectral_dec_vecs_tc \<rho>. sandwich_tc (vector_to_cblinfun v) \<sigma>)\<close>
    apply (subst infsum_reindex)
    using vector_to_cblinfun_inj[of UNIV]
    by (auto simp: o_def inj_on_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>v \<in> spectral_dec_vecs_tc \<rho>. one_dim_iso \<sigma> *\<^sub>C tc_butterfly v v)\<close>
    apply (rule infsum_cong)
    apply (subst one_dim_scaleC_1[symmetric])
    apply (rule from_trace_class_inject[THEN iffD1])
    apply (simp only: sandwich_tc_def compose_tcl.rep_eq compose_tcr.rep_eq scaleC_trace_class.rep_eq
        tc_butterfly.rep_eq cblinfun_compose_scaleC_right cblinfun_compose_scaleC_left)
    by (simp flip: butterfly_def_one_dim)
  also have \<open>\<dots> = one_dim_iso \<sigma> *\<^sub>C (\<Sum>\<^sub>\<infinity>v \<in> spectral_dec_vecs_tc \<rho>. tc_butterfly v v)\<close>
    using infsum_scaleC_right by fastforce
  also have \<open>\<dots> = one_dim_iso \<sigma> *\<^sub>C \<rho>\<close>
    by (simp add: assms butterfly_spectral_dec_vec_tc_has_sum infsumI)
  finally show ?thesis
    by -
qed

lemma complete_measurement_diag[simp]:
  \<open>kraus_family_map (complete_measurement (range ket)) (diagonal_operator_tc f) = diagonal_operator_tc f\<close>
proof (cases \<open>f abs_summable_on UNIV\<close>)
  case True
  have \<open>kraus_family_map (complete_measurement (range ket)) (diagonal_operator_tc f) = 
            (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x)) (diagonal_operator_tc f))\<close>
    by (simp add: kraus_family_map_complete_measurement_ket)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. sandwich_tc (selfbutter (ket x)) (\<Sum>\<^sub>\<infinity>y. f y *\<^sub>C tc_butterfly (ket y) (ket y)))\<close>
    by (simp add: flip: tc_butterfly_scaleC_infsum)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. sandwich_tc (selfbutter (ket x)) (f y *\<^sub>C tc_butterfly (ket y) (ket y)))\<close>
    apply (rule infsum_cong)
    apply (rule infsum_bounded_linear[unfolded o_def, symmetric])
    by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_sandwich_tc tc_butterfly_scaleC_summable True)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. \<Sum>\<^sub>\<infinity>y. of_bool (y=x) *\<^sub>C f x *\<^sub>C tc_butterfly (ket x) (ket x))\<close>
    apply (rule infsum_cong)+
    apply (transfer' fixing: f)
    by (simp add: sandwich_apply)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. f x *\<^sub>C tc_butterfly (ket x) (ket x))\<close>
    apply (subst infsum_of_bool_scaleC)
    by simp
  also have \<open>\<dots> = diagonal_operator_tc f\<close>
    by (simp add: flip: tc_butterfly_scaleC_infsum)
  finally show ?thesis
    by -
next
  case False
  then have \<open>diagonal_operator_tc f = 0\<close>
    by (rule diagonal_operator_tc_invalid)
  then show ?thesis
    by simp
qed

lemma kraus_family_comp_dependent_raw_assoc: 
  fixes \<EE> :: \<open>'f \<Rightarrow> ('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>'g \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  defines \<open>reorder :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'c \<Rightarrow>\<^sub>C\<^sub>L 'd \<times> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'b \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'g \<times> 'f) \<times> 'e
                   \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'b \<Rightarrow>\<^sub>C\<^sub>L 'd \<times> 'g \<times> 'b \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'c \<Rightarrow>\<^sub>C\<^sub>L 'd \<times> 'f \<times> 'e \<equiv>
             \<lambda>(FG::'a \<Rightarrow>\<^sub>C\<^sub>L 'c, E::'c \<Rightarrow>\<^sub>C\<^sub>L 'd, (G::'a \<Rightarrow>\<^sub>C\<^sub>L 'b, F::'b \<Rightarrow>\<^sub>C\<^sub>L 'c, g::'g, f::'f), e::'e). 
              (G, E o\<^sub>C\<^sub>L F, g, F, E, f, e)\<close>
  assumes bdd_E: \<open>bdd_above (range (kraus_family_norm o \<EE>))\<close>
  assumes bdd_F: \<open>bdd_above (range (kraus_family_norm o \<FF>))\<close>
  shows \<open>kraus_family_comp_dependent_raw (\<lambda>g::'g. kraus_family_comp_dependent_raw \<EE> (\<FF> g)) \<GG>
        = kraus_family_map_outcome_inj reorder (kraus_family_comp_dependent_raw (\<lambda>(_,_,_,f). \<EE> f) (kraus_family_comp_dependent_raw \<FF> \<GG>))\<close>
    (is \<open>?lhs = ?rhs\<close>)
proof (rule Rep_kraus_family_inject[THEN iffD1])
  have bdd1: \<open>bdd_above (range (\<lambda>x. kraus_family_norm (kraus_family_comp_dependent_raw \<EE> (\<FF> x))))\<close>
  proof -
    from bdd_F obtain BF where BF: \<open>kraus_family_norm (\<FF> x) \<le> BF\<close> for x
      by (auto simp: bdd_above_def)
    moreover from bdd_E obtain BE where BE: \<open>kraus_family_norm (\<EE> x) \<le> BE\<close> for x
      by (auto simp: bdd_above_def)
    (* from kraus_family_comp_dependent_raw_norm[OF BE] *)
    ultimately have \<open>kraus_family_norm (kraus_family_comp_dependent_raw (\<lambda>x. \<EE> x) (\<FF> x)) \<le> BE * BF\<close> for x
      by (smt (verit, best) kraus_family_comp_dependent_raw_norm kraus_family_norm_geq0 landau_omega.R_mult_left_mono)
    then show ?thesis
      by (auto intro!: bdd_aboveI)
  qed
  have bdd2: \<open>bdd_above (range (kraus_family_norm \<circ> (\<lambda>(_::'a \<Rightarrow>\<^sub>C\<^sub>L 'b, _::'b \<Rightarrow>\<^sub>C\<^sub>L 'c, _::'g, y::'f). \<EE> y)))\<close>
    using assms(2) by (simp add: bdd_above_def)
  define EE FF GG where \<open>EE f = Rep_kraus_family (\<EE> f)\<close> and \<open>FF g = Rep_kraus_family (\<FF> g)\<close> and \<open>GG = Rep_kraus_family \<GG>\<close> for f g
  have \<open>Rep_kraus_family ?lhs
        = (\<lambda>((F,y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, x)) `
          (SIGMA (F, y):GG. Rep_kraus_family (kraus_family_comp_dependent_raw \<EE> (\<FF> y)))\<close>
    apply (subst kraus_family_comp_dependent_raw.rep_eq)
    using bdd1 by (simp add:  GG_def)
  also have \<open>\<dots> = (\<lambda>((G, g), (EF, x)). (EF o\<^sub>C\<^sub>L G, G, EF, g, x)) `
    (SIGMA (G, g):GG. (\<lambda>((F, f), (E, e)). (E o\<^sub>C\<^sub>L F, F, E, f, e)) ` (SIGMA (F, f):FF g. EE f))\<close>
    unfolding EE_def FF_def
    apply (subst kraus_family_comp_dependent_raw.rep_eq)
    using assms by (simp add: case_prod_beta)
  also have \<open>\<dots> = (\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, reorder (F, E, y, x))) ` 
         (SIGMA (FG, _, _, _, y):(\<lambda>((G, g), (F, f)). (F o\<^sub>C\<^sub>L G, G, F, g, f)) ` (SIGMA (G, g):GG. FF g). EE y)\<close>
    by (force simp: reorder_def image_iff case_prod_unfold cblinfun_compose_assoc)
  also have \<open>\<dots> = (\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, reorder (F, E, y, x))) `
    (SIGMA (FG, (_, _, _, f)):Rep_kraus_family (kraus_family_comp_dependent_raw \<FF> \<GG>). EE f)\<close>
    apply (subst kraus_family_comp_dependent_raw.rep_eq)
    using assms
    by (simp add: flip: FF_def GG_def)
  also have \<open>\<dots> =  (\<lambda>(E,z). (E, reorder z)) ` (\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, x)) `
    (SIGMA (FG, (_, _, _, f)):Rep_kraus_family (kraus_family_comp_dependent_raw \<FF> \<GG>).
        EE f)\<close>
    by (simp add: image_image case_prod_beta)
  also have \<open>\<dots> = (\<lambda>(E,x). (E,reorder x)) ` Rep_kraus_family
     (kraus_family_comp_dependent_raw (\<lambda>(_, _, _, y). \<EE> y) (kraus_family_comp_dependent_raw \<FF> \<GG>))\<close>
    apply (subst (2) kraus_family_comp_dependent_raw.rep_eq)
    using bdd2 by (simp add: case_prod_unfold EE_def)
  also have \<open>\<dots> = Rep_kraus_family ?rhs\<close>
    by (simp add: kraus_family_map_outcome_inj.rep_eq case_prod_beta)
  finally show \<open>Rep_kraus_family ?lhs = Rep_kraus_family ?rhs\<close>
    by -
qed


(* lemma kraus_family_comp_dependent_raw_map1:
(* TODO: same for kraus_family_comp_dependent *)
  fixes \<EE> :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
    and h :: \<open>'e \<Rightarrow> 'h\<close>
  shows \<open>kraus_family_map' (UNIV\<times>UNIV\<times>UNIV\<times>{x}) (kraus_family_comp_dependent_raw (\<lambda>e. kraus_family_map_outcome h (\<EE> e)) \<FF>)
     = kraus_family_map' (UNIV\<times>UNIV\<times>UNIV\<times>{x}) (kraus_family_map_outcome (\<lambda>(E,F,e,f). (E,F,e,h f)) (kraus_family_comp_dependent_raw \<EE> \<FF>))\<close>
proof (rule ext)
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>
  obtain a b where x_def: \<open>x = (a,b)\<close> by force
  have bdd1: \<open>bdd_above (range (\<lambda>x. kraus_family_norm (kraus_family_map_outcome h (\<EE> x))))\<close>
    by x
  have bdd2: \<open>bdd_above
        (range
          (\<lambda>x. kraus_family_norm
                 (kraus_family_filter (\<lambda>(E, x). x = b) (kraus_family_map_outcome h (\<EE> x)))))\<close>
    for b
    by x
  have \<open>kraus_family_map' (UNIV \<times> UNIV \<times> UNIV \<times> {x})
           (kraus_family_comp_dependent_raw (\<lambda>e. kraus_family_map_outcome h (\<EE> e)) \<FF>) \<rho>
        = kraus_family_map (kraus_family_comp_dependent_raw 
        (\<lambda>e. (kraus_family_filter (\<lambda>(E,x). x=b) (kraus_family_map_outcome h (\<EE> e))))
         (kraus_family_filter (\<lambda>(E,x). x=a) \<FF>)) \<rho>\<close>
    unfolding kraus_family_map'_def x_def
    apply (rule arg_cong[where f=\<open>\<lambda>x. kraus_family_map x \<rho>\<close>])
    apply (transfer' fixing: \<EE> \<FF> h a b)
    apply (simp add: bdd1 bdd2)
    apply (auto intro!: simp: kraus_family_filter.rep_eq image_iff case_prod_beta)
    by force+
  also have \<open>\<dots> 
        = kraus_family_map (kraus_family_comp_dependent_raw 
        (\<lambda>e. (kraus_family_map_outcome h (kraus_family_filter (\<lambda>(E,x). h x=b) (\<EE> e))))
         (kraus_family_filter (\<lambda>(E,x). x=a) \<FF>)) \<rho>\<close>


  fix z :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'b \<Rightarrow>\<^sub>C\<^sub>L 'c \<times> 'f \<times> 'h\<close>
  obtain E F x y where \<open>z = (E,F,x,y)\<close> 
try0
sledgehammer [dont_slice]
by -
  fix \<rho> :: \<open>('a, 'a) trace_class\<close>


  by x

lemma kraus_family_comp_dependent_raw_map2:
(* TODO: same for kraus_family_comp_dependent *)
  fixes \<EE> :: \<open>'h \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
    and h :: \<open>'f \<Rightarrow> 'h\<close>
  shows \<open>kraus_equivalent' (kraus_family_comp_dependent_raw \<EE> (kraus_family_map_outcome h \<FF>))
      (kraus_family_map_outcome (\<lambda>(E,F,f,e). (E, F, h f, e)) (kraus_family_comp_dependent_raw (\<EE> o h) \<FF>))\<close>
by - *)

lemma kraus_family_map_outcome_twice:
  \<open>kraus_equivalent' (kraus_family_map_outcome f (kraus_family_map_outcome g \<EE>))
                     (kraus_family_map_outcome (f \<circ> g) \<EE>)\<close>
  apply (rule kraus_equivalent'I)
  by (simp add: kraus_family_filter_map_outcome kraus_family_map'_def)

lemma kraus_equivalent'_refl[iff]: \<open>kraus_equivalent' \<EE> \<EE>\<close>
  using kraus_equivalent'_def by blast

lemma kraus_equivalent'_trans[trans]:
  assumes \<open>kraus_equivalent' \<EE> \<FF>\<close>
  assumes \<open>kraus_equivalent' \<FF> \<GG>\<close>
  shows \<open>kraus_equivalent' \<EE> \<GG>\<close>
  by (metis assms(1) assms(2) kraus_equivalent'_def)

lemma kraus_equivalent'_sym[sym]:
  assumes \<open>kraus_equivalent' \<EE> \<FF>\<close>
  shows \<open>kraus_equivalent' \<FF> \<EE>\<close>
  by (metis assms kraus_equivalent'_def)

lemma kraus_family_map'_union_summable_on:
  assumes \<open>\<And>X Y. X\<in>F \<Longrightarrow> Y\<in>F \<Longrightarrow> X\<noteq>Y \<Longrightarrow> disjnt X Y\<close>
  shows \<open>(\<lambda>X. kraus_family_map' X \<EE> \<rho>) summable_on F\<close>
  using assms by (auto intro!: has_sum_imp_summable kraus_family_map'_union_has_sum)

lemma kraus_family_map'_union_infsum:
  assumes \<open>\<And>X Y. X\<in>F \<Longrightarrow> Y\<in>F \<Longrightarrow> X\<noteq>Y \<Longrightarrow> disjnt X Y\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>X\<in>F. kraus_family_map' X \<EE> \<rho>) = kraus_family_map' (\<Union>F) \<EE> \<rho>\<close>
  by (metis assms infsumI kraus_family_map'_union_has_sum)

lemma kraus_family_map'_eqI:
  assumes \<open>kraus_equivalent' \<EE> \<FF>\<close>
  shows \<open>kraus_family_map' X \<EE> \<rho> = kraus_family_map' X \<FF> \<rho>\<close>
  apply (subst asm_rl[of \<open>X=\<Union>((\<lambda>x.{x})`X)\<close>], simp)
  apply (subst (2) asm_rl[of \<open>X=\<Union>((\<lambda>x.{x})`X)\<close>], simp)
  apply (rule kraus_family_map'_union_eqI)
  using assms by (auto simp: kraus_equivalent'_def)

lemma kraus_equivalent'_map_cong:
  assumes \<open>kraus_equivalent' \<EE> \<FF>\<close>
  shows \<open>kraus_equivalent' (kraus_family_map_outcome f \<EE>) (kraus_family_map_outcome f \<FF>)\<close>
proof -
  from assms 
  have \<open>kraus_family_map' (f-`{x}) \<EE> \<rho> = kraus_family_map' (f-`{x}) \<FF> \<rho>\<close> for x \<rho>
    by (rule kraus_family_map'_eqI)
  then show ?thesis
    apply (rule_tac kraus_equivalent'I)
    by (simp add: kraus_family_map'_def kraus_family_filter_map_outcome)
qed

lemma kraus_family_bound_filter:
  \<open>kraus_family_bound (kraus_family_filter P \<EE>) \<le> kraus_family_bound \<EE>\<close>
proof (unfold kraus_family_bound.rep_eq, rule infsum_mono_neutral_wot)
  show \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family (kraus_family_filter P \<EE>))\<close>
    using Rep_kraus_family kraus_family_def2 by blast
  show \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family \<EE>)\<close>
    using Rep_kraus_family kraus_family_def2 by blast
  fix Ex :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<times> 'c\<close>
  show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) \<le> (case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E)\<close>
    by simp
  show \<open>0 \<le> (case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E)\<close>
    by (auto intro!: positive_cblinfun_squareI simp: case_prod_unfold)
  show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) \<le> 0\<close>
    if \<open>Ex \<in> Rep_kraus_family (kraus_family_filter P \<EE>) - Rep_kraus_family \<EE>\<close>
    using that
    by (auto simp: kraus_family_filter.rep_eq)
qed

lemma kraus_family_norm_filter:
  \<open>kraus_family_norm (kraus_family_filter P \<EE>) \<le> kraus_family_norm \<EE>\<close>
  unfolding kraus_family_norm_def
  apply (rule norm_cblinfun_mono)
  by (simp_all add: kraus_family_bound_filter)


lemma kraus_family_filter_comp_dependent:
  fixes \<FF> :: \<open>'e \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<EE> :: \<open>('a::chilbert_space,'b::chilbert_space,'e) kraus_family\<close>
  assumes \<open>bdd_above (range (kraus_family_norm o \<FF>))\<close>
  shows \<open>kraus_family_filter (\<lambda>(e,f). F e f \<and> E e) (kraus_family_comp_dependent \<FF> \<EE>)
      = kraus_family_comp_dependent (\<lambda>e. kraus_family_filter (F e) (\<FF> e)) (kraus_family_filter E \<EE>)\<close>
proof -
  from assms
  have bdd2: \<open>bdd_above (range (\<lambda>e. kraus_family_norm (kraus_family_filter (F e) (\<FF> e))))\<close>
    apply (rule bdd_above_mono2)
    by (auto intro!: kraus_family_norm_filter)
  show ?thesis
    unfolding kraus_family_comp_dependent_def kraus_family_filter_map_outcome
    apply (rule arg_cong[where f=\<open>kraus_family_map_outcome _\<close>])
    using assms bdd2 apply (transfer' fixing: F E)
    by (auto intro!: simp: kraus_family_filter.rep_eq case_prod_unfold image_iff Bex_def)
qed

lemma kraus_family_comp_assoc: 
  fixes \<EE> :: \<open>('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  shows \<open>kraus_equivalent
  (kraus_family_comp (kraus_family_comp \<EE> \<FF>) \<GG>)
  (kraus_family_comp \<EE> (kraus_family_comp \<FF> \<GG>))\<close>
  apply (rule kraus_equivalentI)
  by (simp add: kraus_family_comp_apply)

lemma kraus_family_comp_dependent_raw_cong_left:
  assumes \<open>bdd_above (range (kraus_family_norm o \<EE>))\<close>
  assumes \<open>bdd_above (range (kraus_family_norm o \<EE>'))\<close>
  assumes \<open>\<And>x. x \<in> snd ` Rep_kraus_family \<FF> \<Longrightarrow> \<EE> x = \<EE>' x\<close>
  shows \<open>kraus_family_comp_dependent_raw \<EE> \<FF> = kraus_family_comp_dependent_raw \<EE>' \<FF>\<close>
proof -
  show ?thesis
  apply (rule Rep_kraus_family_inject[THEN iffD1])
  using assms
  by (force simp: kraus_family_comp_dependent_def kraus_family_comp_dependent_raw.rep_eq
      image_iff case_prod_beta Bex_def)
qed

lemma kraus_family_map_remove_0[simp]:
  \<open>kraus_family_map (kraus_family_remove_0 \<EE>) = kraus_family_map \<EE>\<close>
  by (auto intro!: ext infsum_cong_neutral simp add: kraus_family_map_def kraus_family_remove_0.rep_eq)

lemma kraus_family_norm_remove_0[simp]:
  \<open>kraus_family_norm (kraus_family_remove_0 \<EE>) = kraus_family_norm \<EE>\<close>
  by (auto intro!: kraus_equivalentI kraus_family_norm_welldefined)

lemma kraus_family_filter_remove0:
  \<open>kraus_family_filter f (kraus_family_remove_0 \<EE>) = kraus_family_remove_0 (kraus_family_filter f \<EE>)\<close>
  apply (transfer' fixing: f)
  by auto

lemma kraus_family_related_ops_remove_0:
  assumes \<open>E \<noteq> 0\<close>
  shows \<open>kraus_family_related_ops (kraus_family_remove_0 \<EE>) E = kraus_family_related_ops \<EE> E\<close>
  using assms by (auto simp: kraus_family_related_ops_def kraus_family_remove_0.rep_eq)

lemma kraus_family_op_weight_remove_0[simp]:
  \<open>kraus_family_op_weight (kraus_family_remove_0 \<EE>) E = kraus_family_op_weight \<EE> E\<close>
proof (cases \<open>E = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  then show ?thesis
    by (simp add: kraus_family_op_weight_def kraus_family_related_ops_remove_0)
qed

lemma kraus_family_map_outcome_remove0[simp]:
  \<open>kraus_family_map_outcome f (kraus_family_remove_0 \<EE>) = kraus_family_map_outcome f \<EE>\<close>
  apply (transfer' fixing: f)
  by (simp add: kraus_family_map_outcome.rep_eq kraus_family_filter_remove0)

lemma kraus_family_remove_0_comp_dependent_raw:
  \<open>kraus_family_remove_0 (kraus_family_comp_dependent_raw \<EE> \<FF>) =
      kraus_family_remove_0 (kraus_family_comp_dependent_raw (\<lambda>x. kraus_family_remove_0 (\<EE> x)) (kraus_family_remove_0 \<FF>))\<close>
  apply transfer'
  by (auto intro!: simp: image_iff case_prod_beta kraus_family_remove_0.rep_eq Bex_def)

lemma kraus_family_comp_dependent_cong_left:
  assumes \<open>bdd_above (range (kraus_family_norm o \<EE>))\<close>
  assumes \<open>bdd_above (range (kraus_family_norm o \<EE>'))\<close>
  assumes \<open>\<And>x. x \<in> kraus_map_domain \<FF> \<Longrightarrow> \<EE> x = \<EE>' x\<close>
  shows \<open>kraus_family_comp_dependent \<EE> \<FF> = kraus_family_comp_dependent \<EE>' \<FF>\<close>
proof -
  have \<open>kraus_family_comp_dependent \<EE> \<FF> = kraus_family_map_outcome (\<lambda>(F, E, y). y) (kraus_family_comp_dependent_raw \<EE> \<FF>)\<close>
    by (simp add: kraus_family_comp_dependent_def id_def)
  also have \<open>\<dots> = kraus_family_map_outcome (\<lambda>(F, E, y). y) (kraus_family_remove_0 (kraus_family_comp_dependent_raw \<EE> \<FF>))\<close>
    by simp
  also have \<open>\<dots> = kraus_family_map_outcome (\<lambda>(F, E, y). y) (kraus_family_remove_0 (kraus_family_comp_dependent_raw (\<lambda>x. kraus_family_remove_0 (\<EE> x)) (kraus_family_remove_0 \<FF>)))\<close>
    apply (subst kraus_family_remove_0_comp_dependent_raw)
    by simp
  also have \<open>\<dots> = kraus_family_map_outcome (\<lambda>(F, E, y). y) (kraus_family_remove_0 (kraus_family_comp_dependent_raw (\<lambda>x. kraus_family_remove_0 (\<EE>' x)) (kraus_family_remove_0 \<FF>)))\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kraus_family_map_outcome _ (kraus_family_remove_0 t)\<close>])
    apply (rule kraus_family_comp_dependent_raw_cong_left)
    using assms by (auto intro!: simp: kraus_map_domain.rep_eq kraus_family_remove_0.rep_eq)
  also have \<open>\<dots> = kraus_family_map_outcome (\<lambda>(F, E, y). y) (kraus_family_remove_0 (kraus_family_comp_dependent_raw \<EE>' \<FF>))\<close>
    apply (subst kraus_family_remove_0_comp_dependent_raw[symmetric])
    by simp
  also have \<open>\<dots> = kraus_family_map_outcome (\<lambda>(F, E, y). y) (kraus_family_comp_dependent_raw \<EE>' \<FF>)\<close>
    by simp
  also have \<open>\<dots> = kraus_family_comp_dependent \<EE>' \<FF>\<close>
    by (simp add: kraus_family_comp_dependent_def id_def)
  finally show ?thesis
    by -
qed

lemma kraus_family_map_outcome_remove_0:
  \<open>kraus_family_remove_0 (kraus_family_map_outcome f \<EE>) = kraus_family_map_outcome f \<EE>\<close>
  apply (transfer' fixing: f)
  by auto


lemma kraus_map_domain_map_outcome[simp]:
  \<open>kraus_map_domain (kraus_family_map_outcome f \<EE>) = f ` kraus_map_domain \<EE>\<close>
proof (rule Set.set_eqI, rule iffI)
  fix x assume \<open>x \<in> kraus_map_domain (kraus_family_map_outcome f \<EE>)\<close>
  then obtain a where \<open>(norm a)\<^sup>2 = kraus_family_op_weight (kraus_family_filter (\<lambda>xa. f xa = x) \<EE>) a\<close> and \<open>a \<noteq> 0\<close>
    by (auto intro!: simp: kraus_map_domain.rep_eq kraus_family_map_outcome.rep_eq)
  then have \<open>kraus_family_op_weight (kraus_family_filter (\<lambda>xa. f xa = x) \<EE>) a \<noteq> 0\<close>
    by force
  then have \<open>(\<Sum>\<^sub>\<infinity>(E, _)\<in>kraus_family_related_ops (kraus_family_filter (\<lambda>xa. f xa = x) \<EE>) a. (norm E)\<^sup>2) \<noteq> 0\<close>
    by (simp add: kraus_family_op_weight_def)
  from this[unfolded not_def, rule_format, OF infsum_0]
  obtain E x' where rel_ops: \<open>(E,x') \<in> kraus_family_related_ops (kraus_family_filter (\<lambda>xa. f xa = x) \<EE>) a\<close>
    and \<open>(norm E)\<^sup>2 \<noteq> 0\<close>
    by fast
  then have \<open>E \<noteq> 0\<close>
    by force
  with rel_ops obtain E' where \<open>E' \<noteq> 0\<close> and \<open>(E',x') \<in> Rep_kraus_family (kraus_family_filter (\<lambda>xa. f xa = x) \<EE>)\<close>
    apply atomize_elim
    by (auto simp: kraus_family_related_ops_def)
  then have \<open>(E',x') \<in> Rep_kraus_family \<EE>\<close> and \<open>f x' = x\<close>
    by (auto simp: kraus_family_filter.rep_eq)
  with \<open>E' \<noteq> 0\<close> have \<open>x' \<in> kraus_map_domain \<EE>\<close>
    by (force simp: kraus_map_domain.rep_eq)
  with \<open>f x' = x\<close>
  show \<open>x \<in> f ` kraus_map_domain \<EE>\<close>
    by fast
next
  fix x assume \<open>x \<in> f ` kraus_map_domain \<EE>\<close>
  then obtain y where \<open>x = f y\<close> and \<open>y \<in> kraus_map_domain \<EE>\<close>
    by blast
  then obtain E where \<open>E \<noteq> 0\<close> and \<open>(E,y) \<in> Rep_kraus_family \<EE>\<close>
    by (auto simp: kraus_map_domain.rep_eq)
  then have Ey: \<open>(E,y) \<in> Rep_kraus_family (kraus_family_filter (\<lambda>z. f z=x) \<EE>)\<close>
    by (simp add: kraus_family_filter.rep_eq \<open>x = f y\<close>)
  then have \<open>kraus_family_bound (kraus_family_filter (\<lambda>z. f z=x) \<EE>) \<noteq> 0\<close>
  proof -
    define B where \<open>B = kraus_family_bound (kraus_family_filter (\<lambda>z. f z=x) \<EE>)\<close>
    have \<open>has_sum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) {(E,y)} (E* o\<^sub>C\<^sub>L E)\<close>
      apply (subst asm_rl[of \<open>E* o\<^sub>C\<^sub>L E = (\<Sum>(E,x)\<in>{(E,y)}. E* o\<^sub>C\<^sub>L E)\<close>], simp)
      apply (rule has_sum_in_finite)
      by auto
    moreover have \<open>has_sum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family (kraus_family_filter (\<lambda>z. f z = x) \<EE>)) B\<close>
      using kraus_family_bound_has_sum B_def by blast
    ultimately have \<open>B \<ge> E* o\<^sub>C\<^sub>L E\<close>
      apply (rule has_sum_mono_neutral_wot)
      using Ey positive_cblinfun_squareI by auto
    then show \<open>B \<noteq> 0\<close>
      by (meson \<open>E \<noteq> 0\<close> basic_trans_rules(24) op_square_nondegenerate positive_cblinfun_squareI)
  qed
  then have \<open>kraus_family_bound (kraus_family_map_outcome f (kraus_family_filter (\<lambda>z. f z=x) \<EE>)) \<noteq> 0\<close>
    by (simp add: kraus_family_map_outcome_bound)
  then have \<open>kraus_family_bound (kraus_family_filter (\<lambda>z. z=x) (kraus_family_map_outcome f \<EE>)) \<noteq> 0\<close>
    by (simp add: kraus_family_filter_map_outcome)
  from this[unfolded not_def kraus_family_bound.rep_eq, rule_format, OF infsum_in_0]
  obtain E' x' where \<open>(E',x') \<in> Rep_kraus_family (kraus_family_filter (\<lambda>z. z=x) (kraus_family_map_outcome f \<EE>))\<close>
    and \<open>E' \<noteq> 0\<close>
    by fastforce
  then have \<open>(E',x') \<in> Rep_kraus_family (kraus_family_map_outcome f \<EE>)\<close> and \<open>x' = x\<close>
    by (auto simp: kraus_family_filter.rep_eq)
  with \<open>E' \<noteq> 0\<close> show \<open>x \<in> kraus_map_domain (kraus_family_map_outcome f \<EE>)\<close>
    by (auto simp: kraus_map_domain.rep_eq image_iff Bex_def)
qed

lemma kraus_map_domain_comp_dependent:
  \<open>kraus_map_domain (kraus_family_comp_dependent \<EE> \<FF>) \<subseteq> (SIGMA x:kraus_map_domain \<FF>. kraus_map_domain (\<EE> x))\<close>
  apply (simp add: kraus_family_comp_dependent_def kraus_map_domain_map_outcome id_def)
  apply (auto intro!: simp: kraus_family_comp_dependent_raw.rep_eq kraus_map_domain.rep_eq image_iff Bex_def)
   apply force
  by force


lemma kraus_map_domain_filter[simp]:
  \<open>kraus_map_domain (kraus_family_filter P \<EE>) = Set.filter P (kraus_map_domain \<EE>)\<close>
  apply (transfer' fixing: P)
  by (auto simp: image_iff Bex_def)

lemma kraus_family_comp_dependent_assoc': 
  fixes \<EE> :: \<open>'f \<Rightarrow> ('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>'g \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  assumes bdd_E: \<open>bdd_above (range (kraus_family_norm o \<EE>))\<close>
  assumes bdd_F: \<open>bdd_above (range (kraus_family_norm o \<FF>))\<close>
  shows \<open>kraus_equivalent'
  (kraus_family_comp_dependent (\<lambda>g. kraus_family_comp_dependent \<EE> (\<FF> g)) \<GG>)
  (kraus_family_map_outcome (\<lambda>((g,f),e). (g,f,e)) (kraus_family_comp_dependent (\<lambda>(_,f). \<EE> f) (kraus_family_comp_dependent \<FF> \<GG>)))\<close>
    (is \<open>kraus_equivalent' ?lhs ?rhs\<close>)
proof (rule kraus_equivalent'I)
  fix gfe :: \<open>'g \<times> 'f \<times> 'e\<close> and \<rho>
  obtain g f e where gfe_def: \<open>gfe = (g,f,e)\<close>
    apply atomize_elim
    apply (rule exI[of _ \<open>fst gfe\<close>])
    apply (rule exI[of _ \<open>fst (snd gfe)\<close>])
    apply (rule exI[of _ \<open>snd (snd gfe)\<close>])
    by simp
  have aux: \<open>(\<lambda>x. (fst (fst x), snd (fst x), snd x) = gfe) = (\<lambda>x. x=((g,f),e))\<close>
    by (auto simp: gfe_def)
  have bdd5: \<open>bdd_above (range (\<lambda>x. kraus_family_norm (kraus_family_filter (\<lambda>x. x = f) (\<FF> x))))\<close>
    using kraus_family_norm_filter bdd_F
    by (metis (mono_tags, lifting) bdd_above_mono2 o_def subset_UNIV)
  have bdd2: \<open>bdd_above (range (\<lambda>x. kraus_family_norm (kraus_family_filter (\<lambda>x. x = e) (\<EE> x))))\<close>
    using kraus_family_norm_filter bdd_E
    by (metis (mono_tags, lifting) bdd_above_mono2 o_def subset_UNIV)
  then have bdd3: \<open>bdd_above (range (\<lambda>(g, f). kraus_family_norm (kraus_family_filter (\<lambda>x. x = e) (\<EE> f))))\<close>
    by (simp add: bdd_above_def)
  have bdd1: \<open>bdd_above (range (\<lambda>x. kraus_family_norm (kraus_family_comp_dependent
               (\<lambda>f. kraus_family_filter (\<lambda>x. x = e) (\<EE> f)) (kraus_family_filter (\<lambda>x. x = f) (\<FF> x)))))\<close>
  proof -
    from bdd2 obtain BE where BE: \<open>kraus_family_norm (kraus_family_filter (\<lambda>x. x = e) (\<EE> x)) \<le> BE\<close> for x
      by (auto simp: bdd_above_def)
    then have \<open>BE \<ge> 0\<close>
      by (smt (z3) kraus_family_norm_geq0)
    from bdd5 obtain BF where BF: \<open>kraus_family_norm (kraus_family_filter (\<lambda>x. x = f) (\<FF> x)) \<le> BF\<close> for x
      by (auto simp: bdd_above_def)
    have \<open>kraus_family_norm (kraus_family_comp_dependent (\<lambda>x. kraus_family_filter (\<lambda>x. x = e) (\<EE> x)) (kraus_family_filter (\<lambda>x. x = f) (\<FF> x)))
      \<le> BE * kraus_family_norm (kraus_family_filter (\<lambda>x. x = f) (\<FF> x))\<close> for x
      using kraus_family_comp_dependent_norm[OF BE] by fast
    then have \<open>kraus_family_norm (kraus_family_comp_dependent 
           (\<lambda>x. kraus_family_filter (\<lambda>x. x = e) (\<EE> x)) (kraus_family_filter (\<lambda>x. x = f) (\<FF> x)))
      \<le> BE * BF\<close> for x
      apply (rule order_trans)      
      using BF \<open>BE \<ge> 0\<close>
      by (auto intro!: mult_left_mono)
    then
    show ?thesis
      by (auto intro!: bdd_aboveI)
  qed
  have bdd6: \<open>bdd_above (range (kraus_family_norm \<circ> (\<lambda>g. kraus_family_comp_dependent \<EE> (\<FF> g))))\<close>
  proof -
    from bdd_E obtain BE where BE: \<open>kraus_family_norm (\<EE> x) \<le> BE\<close> for x
      by (auto simp: bdd_above_def)
    then have \<open>BE \<ge> 0\<close>
      by (smt (z3) kraus_family_norm_geq0)
    from bdd_F obtain BF where BF: \<open>kraus_family_norm (\<FF> x) \<le> BF\<close> for x
      by (auto simp: bdd_above_def)
    have \<open>kraus_family_norm (kraus_family_comp_dependent \<EE> (\<FF> x))
                  \<le> BE * kraus_family_norm (\<FF> x)\<close> for x
      using kraus_family_comp_dependent_norm[OF BE] by fast
    then have \<open>kraus_family_norm (kraus_family_comp_dependent \<EE> (\<FF> x))
      \<le> BE * BF\<close> for x
      apply (rule order_trans)      
      using BF \<open>BE \<ge> 0\<close>
      by (auto intro!: mult_left_mono)
    then
    show ?thesis
      by (auto intro!: bdd_aboveI)
  qed

  have \<open>kraus_family_map' {gfe} ?lhs \<rho>
       = kraus_family_map (kraus_family_comp_dependent 
            (\<lambda>g. kraus_family_filter (\<lambda>x. x=(f,e)) (kraus_family_comp_dependent \<EE> (\<FF> g)))
            (kraus_family_filter (\<lambda>x. x=g) \<GG>)) \<rho>\<close>
    unfolding kraus_family_map'_def
    apply (subst kraus_family_filter_comp_dependent[symmetric])
    using bdd6 apply blast
    apply (subst asm_rl[of \<open>(\<lambda>(x, y). y = (f, e) \<and> x = g) = (\<lambda>x. x \<in> {gfe})\<close>])
    by (auto simp: gfe_def)
  also have \<open>\<dots> = kraus_family_map (kraus_family_comp_dependent
            (\<lambda>g. kraus_family_comp_dependent
                       (\<lambda>f. kraus_family_filter (\<lambda>x. x=e) (\<EE> f)) (kraus_family_filter (\<lambda>x. x=f) (\<FF> g)))
            (kraus_family_filter (\<lambda>x. x=g) \<GG>)) \<rho>\<close>
    apply (subst (2) kraus_family_filter_comp_dependent[symmetric])
    using bdd_E apply blast 
    apply (subst asm_rl[of \<open>(\<lambda>(ea, fa). fa = e \<and> ea = f) = (\<lambda>x. x = (f, e))\<close>])
    by auto
  also have \<open>\<dots> = kraus_family_map (kraus_family_comp_dependent
            (\<lambda>_. kraus_family_comp_dependent
                       (\<lambda>f. kraus_family_filter (\<lambda>x. x=e) (\<EE> f)) (kraus_family_filter (\<lambda>x. x=f) (\<FF> g)))
            (kraus_family_filter (\<lambda>x. x=g) \<GG>)) \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kraus_family_map t \<rho>\<close>])
    apply (rule kraus_family_comp_dependent_cong_left)
    using bdd1 by (auto intro!: simp: kraus_map_domain.rep_eq kraus_family_filter.rep_eq)
  also have \<open>\<dots> = kraus_family_map (kraus_family_comp_dependent
            (\<lambda>_. kraus_family_comp_dependent
                       (\<lambda>_. kraus_family_filter (\<lambda>x. x=e) (\<EE> f)) (kraus_family_filter (\<lambda>x. x=f) (\<FF> g)))
            (kraus_family_filter (\<lambda>x. x=g) \<GG>)) \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kraus_family_map (kraus_family_comp_dependent t _) \<rho>\<close>])
    apply (rule ext)
    apply (rule kraus_family_comp_dependent_cong_left)
    using bdd2 by (auto intro!: simp: kraus_map_domain.rep_eq kraus_family_filter.rep_eq)
  also have \<open>\<dots> = kraus_family_map (kraus_family_comp
            (kraus_family_comp
                       (kraus_family_filter (\<lambda>x. x=e) (\<EE> f)) (kraus_family_filter (\<lambda>x. x=f) (\<FF> g)))
            (kraus_family_filter (\<lambda>x. x=g) \<GG>)) \<rho>\<close>
    by (simp add: kraus_family_comp_def)
  also have \<open>\<dots> = kraus_family_map (kraus_family_comp
                       (kraus_family_filter (\<lambda>x. x=e) (\<EE> f)) (kraus_family_comp
            (kraus_family_filter (\<lambda>x. x=f) (\<FF> g))
            (kraus_family_filter (\<lambda>x. x=g) \<GG>))) \<rho>\<close>
    by (simp add: kraus_family_comp_assoc[unfolded kraus_equivalent_def])
  also have \<open>\<dots> = kraus_family_map (kraus_family_comp_dependent (\<lambda>_. kraus_family_filter (\<lambda>x. x=e) (\<EE> f))
            (kraus_family_comp_dependent (\<lambda>_. kraus_family_filter (\<lambda>x. x=f) (\<FF> g))
                                         (kraus_family_filter (\<lambda>x. x=g) \<GG>))) \<rho>\<close>
    by (simp add: kraus_family_comp_def)
  also have \<open>\<dots> = kraus_family_map (kraus_family_comp_dependent (\<lambda>(g,f). kraus_family_filter (\<lambda>x. x=e) (\<EE> f))
            (kraus_family_comp_dependent (\<lambda>_. kraus_family_filter (\<lambda>x. x=f) (\<FF> g))
                                         (kraus_family_filter (\<lambda>x. x=g) \<GG>))) \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kraus_family_map t \<rho>\<close>])
    apply (rule kraus_family_comp_dependent_cong_left)
    using bdd3 apply auto[2]
    using kraus_map_domain_comp_dependent[of \<open>(\<lambda>_. kraus_family_filter (\<lambda>x. x = f) (\<FF> g))\<close> \<open>kraus_family_filter (\<lambda>x. x = g) \<GG>\<close>]
    by (auto intro!: simp: kraus_family_filter.rep_eq case_prod_unfold)
  also have \<open>\<dots> = kraus_family_map (kraus_family_comp_dependent (\<lambda>(g,f). kraus_family_filter (\<lambda>x. x=e) (\<EE> f))
            (kraus_family_comp_dependent (\<lambda>g. kraus_family_filter (\<lambda>x. x=f) (\<FF> g))
                                         (kraus_family_filter (\<lambda>x. x=g) \<GG>))) \<rho>\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>t. kraus_family_map (kraus_family_comp_dependent _ t) _\<close>])
    apply (rule kraus_family_comp_dependent_cong_left)
    using bdd5 by (auto intro!: simp: kraus_map_domain.rep_eq kraus_family_filter.rep_eq)
  also have \<open>\<dots> = kraus_family_map (kraus_family_comp_dependent (\<lambda>(g,f). kraus_family_filter (\<lambda>x. x=e) (\<EE> f))
            (kraus_family_filter (\<lambda>x. x=(g,f)) (kraus_family_comp_dependent \<FF> \<GG>))) \<rho>\<close>
    apply (subst kraus_family_filter_comp_dependent[symmetric])
    using bdd_F apply blast 
    apply (subst asm_rl[of \<open>(\<lambda>(e, fa). fa = f \<and> e = g) = (\<lambda>x. x = (g, f))\<close>])
    by auto
  also have \<open>\<dots> = kraus_family_map (kraus_family_filter (\<lambda>x. x=((g,f),e))
       (kraus_family_comp_dependent (\<lambda>(g,f). \<EE> f) (kraus_family_comp_dependent \<FF> \<GG>))) \<rho>\<close>
    unfolding case_prod_beta
    apply (subst kraus_family_filter_comp_dependent[symmetric])
     apply (smt (verit, del_insts) bdd_E comp_eq_dest_lhs image_cong range_composition range_snd)
    apply (subst asm_rl[of \<open>(\<lambda>(ea, fa). fa = e \<and> ea = (g, f)) = (\<lambda>x. x = ((g, f), e))\<close>])
    by auto
  also have \<open>\<dots> = kraus_family_map (kraus_family_filter (\<lambda>x. x=gfe)
        (kraus_family_map_outcome (\<lambda>((g, f), e). (g, f, e))
       (kraus_family_comp_dependent (\<lambda>(g,f). \<EE> f) (kraus_family_comp_dependent \<FF> \<GG>)))) \<rho>\<close>
    by (simp add: kraus_family_filter_map_outcome case_prod_beta aux)
  also have \<open>\<dots> = kraus_family_map' {gfe} ?rhs \<rho>\<close>
    by (simp add: kraus_family_map'_def)
  finally show \<open>kraus_family_map' {gfe} ?lhs \<rho> = kraus_family_map' {gfe} ?rhs \<rho>\<close>
    by -
qed
(* proof -
  write kraus_equivalent' (infix "~~" 50)

  have inj: \<open>inj_on (\<lambda>(FG, E, (G, F, g, f), e). (G, E o\<^sub>C\<^sub>L F, g, F, E, f, e))
     (kraus_mapkraus_map_domainn
       (kraus_family_comp_dependent_raw (\<lambda>(_, _, _, y). \<EE> y) (kraus_family_comp_dependent_raw \<FF> \<GG>)))\<close>
    apply transfer'
    apply (simp add: kraus_family_comp_dependent_raw.rep_eq inj_on_def)
    by fastforce

  have \<open>?lhs = kraus_family_map_outcome (\<lambda>(_, _, gfe). gfe)
     (kraus_family_comp_dependent_raw
       (\<lambda>g. kraus_family_map_outcome (\<lambda>(_, _, fe). fe) (kraus_family_comp_dependent_raw \<EE> (\<FF> g))) \<GG>) \<close>
    by (simp add: kraus_family_comp_dependent_def id_def)
  also have \<open>\<dots> ~~ kraus_family_map_outcome (\<lambda>(_, _, gfe). gfe)
     (kraus_family_map_outcome (\<lambda>(G, EF, g, (_,_,fe)). (G, EF, g, fe))
       (kraus_family_comp_dependent_raw (\<lambda>g. kraus_family_comp_dependent_raw \<EE> (\<FF> g)) \<GG>))\<close>
    apply (rule kraus_equivalent'_trans)
    apply (rule kraus_equivalent'_map_cong)
    apply (rule kraus_family_comp_dependent_raw_map1)
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> ~~ kraus_family_map_outcome ((\<lambda>(_, _, gfe). gfe) \<circ> (\<lambda>(G, EF, g, (_,_,fe)). (G, EF, g, fe)))
       (kraus_family_comp_dependent_raw (\<lambda>g. kraus_family_comp_dependent_raw \<EE> (\<FF> g)) \<GG>)\<close>
    by (rule kraus_family_map_outcome_twice)
  also have \<open>\<dots> = (kraus_family_map_outcome (\<lambda>(G, EF, g, (_,_,fe)). (g, fe))
       (kraus_family_comp_dependent_raw (\<lambda>g. kraus_family_comp_dependent_raw \<EE> (\<FF> g)) \<GG>))\<close>
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> = kraus_family_map_outcome (\<lambda>(G, EF, g, _, _, fe). (g, fe))
     (kraus_family_map_outcome_inj (\<lambda>(FG, E, (G, F, g, f), e). (G, E o\<^sub>C\<^sub>L F, g, F, E, f, e))
       (kraus_family_comp_dependent_raw (\<lambda>(_, _, _, y). \<EE> y) (kraus_family_comp_dependent_raw \<FF> \<GG>)))\<close>
    apply (subst kraus_family_comp_dependent_raw_assoc)
    using assms by auto
  also have \<open>\<dots> ~~ kraus_family_map_outcome (\<lambda>(G, EF, g, _, _, fe). (g, fe))
     (kraus_family_map_outcome (\<lambda>(FG, E, (G, F, g, f), e). (G, E o\<^sub>C\<^sub>L F, g, F, E, f, e))
       (kraus_family_comp_dependent_raw (\<lambda>(_, _, _, y). \<EE> y) (kraus_family_comp_dependent_raw \<FF> \<GG>)))\<close>
    apply (rule kraus_equivalent'_map_cong)
    using inj by (rule kraus_equivalent'_map_outcome_inj)
  also have \<open>\<dots> ~~ kraus_family_map_outcome ((\<lambda>(G, EF, g, _, _, fe). (g, fe)) \<circ>
     (\<lambda>(FG, E, (G, F, g, f), e). (G, E o\<^sub>C\<^sub>L F, g, F, E, f, e)))
       (kraus_family_comp_dependent_raw (\<lambda>(_, _, _, y). \<EE> y) (kraus_family_comp_dependent_raw \<FF> \<GG>))\<close>
    by (rule kraus_family_map_outcome_twice)
  also have \<open>\<dots> = (kraus_family_map_outcome 
     (\<lambda>(FG, E, (G, F, g, f), e). (g,f,e))
       (kraus_family_comp_dependent_raw (\<lambda>(_, _, _, y). \<EE> y) (kraus_family_comp_dependent_raw \<FF> \<GG>)))\<close>
    (is \<open>\<dots> = ?mid\<close>)
    by (simp add: case_prod_unfold o_def)
  finally have lhs_mid: \<open>?lhs ~~ ?mid\<close>
    by -

  have \<open>?rhs = kraus_family_map_outcome (\<lambda>((g,f),e). (g,f,e))
           (kraus_family_map_outcome (\<lambda>(_, _, gfe). gfe)
             (kraus_family_comp_dependent_raw (\<lambda>(_, f). \<EE> f)
               (kraus_family_map_outcome (\<lambda>(F, E, gf). gf) (kraus_family_comp_dependent_raw \<FF> \<GG>))))\<close>
    by (simp add: kraus_family_comp_dependent_def id_def)
  also have \<open>\<dots> ~~ kraus_family_map_outcome ((\<lambda>((g,f),e). (g,f,e)) o (\<lambda>(_, _, gfe). gfe))
             (kraus_family_comp_dependent_raw (\<lambda>(_, f). \<EE> f)
               (kraus_family_map_outcome (\<lambda>(F, E, gf). gf) (kraus_family_comp_dependent_raw \<FF> \<GG>)))\<close>
    using kraus_family_map_outcome_twice by blast
  also have \<open>\<dots> ~~ kraus_family_map_outcome (\<lambda>(_, _, ((g,f),e)). (g,f,e))
             (kraus_family_comp_dependent_raw (\<lambda>(_, f). \<EE> f)
               (kraus_family_map_outcome (\<lambda>(F, E, gf). gf) (kraus_family_comp_dependent_raw \<FF> \<GG>)))\<close>
    by (simp add: case_prod_unfold o_def)
  also have \<open>\<dots> ~~ kraus_family_map_outcome (\<lambda>(_, _, (g, f), e). (g, f, e))
     (kraus_family_map_outcome (\<lambda>(E, F, (_,_,gf), e). (E, F, gf, e))
       (kraus_family_comp_dependent_raw (\<lambda>(_, _, _, f). \<EE> f)
         (kraus_family_comp_dependent_raw \<FF> \<GG>)))\<close>
    apply (rule kraus_equivalent'_trans)
    apply (rule kraus_equivalent'_map_cong)
     apply (rule kraus_family_comp_dependent_raw_map2)
    by (simp add: o_def case_prod_unfold)
  also have \<open>\<dots> ~~ ?mid\<close>
    apply (rule kraus_equivalent'_trans)
     apply (rule kraus_family_map_outcome_twice)
    by (simp add: o_def case_prod_unfold)
  finally have rhs_mid: \<open>?rhs ~~ ?mid\<close>
    by -

  from lhs_mid rhs_mid show ?thesis
    using kraus_equivalent'_sym kraus_equivalent'_trans by blast
qed *)

lemma kraus_family_comp_assoc': 
  fixes \<EE> :: \<open>('c::chilbert_space,'d::chilbert_space,'e) kraus_family\<close>
    and \<FF> :: \<open>('b::chilbert_space,'c::chilbert_space,'f) kraus_family\<close>
    and \<GG> :: \<open>('a::chilbert_space,'b::chilbert_space,'g) kraus_family\<close>
  shows \<open>kraus_equivalent'
  (kraus_family_comp (kraus_family_comp \<EE> \<FF>) \<GG>)
  (kraus_family_map_outcome (\<lambda>((g,f),e). (g,f,e)) (kraus_family_comp \<EE> (kraus_family_comp \<FF> \<GG>)))\<close>
  apply (simp add: kraus_family_comp_def)
  apply (rule kraus_equivalent'_trans)
   apply (rule kraus_family_comp_dependent_assoc')
  by (auto simp: case_prod_unfold)




lemma kraus_map_eq0I:
  assumes \<open>kraus_equivalent \<EE> 0\<close>
  shows \<open>kraus_family_map \<EE> \<rho> = 0\<close>
  using assms kraus_equivalent_def by force

lemma kraus_family_remove_0_equivalent: \<open>kraus_equivalent (kraus_family_remove_0 \<EE>) \<EE>\<close>
  by (simp add: kraus_equivalent_def)

lemma kraus_family_remove_0_equivalent': \<open>kraus_equivalent' (kraus_family_remove_0 \<EE>) \<EE>\<close>
  by (simp add: kraus_equivalent'_def kraus_family_map'_def kraus_family_filter_remove0)

lemma kraus_family_filter_domain[simp]:
  \<open>kraus_equivalent' (kraus_family_filter (\<lambda>x. x \<in> kraus_map_domain \<EE>) \<EE>) \<EE>\<close>
proof -
  have \<open>kraus_equivalent' (kraus_family_filter (\<lambda>x. x \<in> kraus_map_domain \<EE>) \<EE>)
            (kraus_family_remove_0 (kraus_family_filter (\<lambda>x. x \<in> kraus_map_domain \<EE>) \<EE>))\<close>
    using kraus_equivalent'_sym kraus_family_remove_0_equivalent' by blast
  also have \<open>\<dots> = kraus_family_filter (\<lambda>x. x \<in> kraus_map_domain \<EE>) (kraus_family_remove_0 \<EE>)\<close>
    by (simp add: kraus_family_filter_remove0)
  also have \<open>\<dots> = kraus_family_remove_0 \<EE>\<close>
    apply transfer'
    by (auto simp: image_iff Bex_def)
  also have \<open>kraus_equivalent' \<dots> \<EE>\<close>
    by (simp add: kraus_family_remove_0_equivalent')
  finally show ?thesis
    by -
qed

lemma kraus_family_comp_dependent_cong':
  fixes \<EE> \<EE>' :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e) kraus_family\<close>
    and \<FF> \<FF>' :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
  assumes bdd: \<open>bdd_above (range (kraus_family_norm o \<EE>))\<close>
  assumes bdd': \<open>bdd_above (range (kraus_family_norm o \<EE>'))\<close>
  assumes \<open>\<And>x. x \<in> kraus_map_domain \<FF> \<Longrightarrow> kraus_equivalent' (\<EE> x) (\<EE>' x)\<close>
  assumes \<open>kraus_equivalent' \<FF> \<FF>'\<close>
  shows \<open>kraus_equivalent' (kraus_family_comp_dependent \<EE> \<FF>) (kraus_family_comp_dependent \<EE>' \<FF>')\<close>
proof (rule kraus_equivalent'I)
  fix x :: \<open>'f \<times> 'e\<close> and \<rho>
  obtain f e where x_def: \<open>x = (f,e)\<close>
    by force

  have rewrite_comp: \<open>kraus_family_map' {x} (kraus_family_comp_dependent \<EE> \<FF>) \<rho> = 
        kraus_family_map (kraus_family_comp (kraus_family_filter (\<lambda>e'. e' = e) (\<EE> f))
                                           (kraus_family_filter (\<lambda>f'. f' = f) \<FF>)) \<rho>\<close>
    if \<open>bdd_above (range (kraus_family_norm o \<EE>))\<close> 
    for \<EE> :: \<open>'f \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'e) kraus_family\<close> and \<FF> :: \<open>('a::chilbert_space,'b::chilbert_space,'f) kraus_family\<close>
  proof -
    from that
    have bdd_filter: \<open>bdd_above (range (kraus_family_norm \<circ> (\<lambda>f. kraus_family_filter (\<lambda>e'. e' = e) (\<EE> f))))\<close>
      using kraus_family_norm_filter
      apply (auto intro!: simp: bdd_above_def)
      using order_trans by blast
    have *: \<open>kraus_family_filter (\<lambda>x. x = (f, e)) (kraus_family_comp_dependent \<EE> \<FF>)
        = kraus_family_comp_dependent (\<lambda>f. kraus_family_filter (\<lambda>e'. e' = e) (\<EE> f))
               (kraus_family_filter (\<lambda>f'. f' = f) \<FF>)\<close>
      using kraus_family_filter_comp_dependent[where \<EE>=\<FF> and \<FF>=\<EE> and F=\<open>\<lambda>_ x. x=e\<close> and E=\<open>\<lambda>x. x=f\<close>]
        that
      apply (subst (asm) asm_rl[of \<open>(\<lambda>(ea, fa). fa = e \<and> ea = f) = (\<lambda>y. y=(f,e))\<close>])
      by auto

    have \<open>kraus_family_map' {x} (kraus_family_comp_dependent \<EE> \<FF>) \<rho>
      = kraus_family_map (kraus_family_comp_dependent (\<lambda>f. kraus_family_filter (\<lambda>e'. e' = e) (\<EE> f))
                                                     (kraus_family_filter (\<lambda>f'. f' = f) \<FF>)) \<rho>\<close>
      by (auto intro!: simp: x_def kraus_family_map'_def * )
    also have \<open>\<dots> = kraus_family_map
     (kraus_family_comp_dependent (\<lambda>_. kraus_family_filter (\<lambda>e'. e' = e) (\<EE> f))
       (kraus_family_filter (\<lambda>f'. f' = f) \<FF>)) \<rho>\<close>
      apply (rule arg_cong[where f="\<lambda>z. kraus_family_map z _"])
      apply (rule kraus_family_comp_dependent_cong_left)
      using bdd_filter by auto
    also have \<open>\<dots> = kraus_family_map (kraus_family_comp (kraus_family_filter (\<lambda>e'. e' = e) (\<EE> f))
       (kraus_family_filter (\<lambda>f'. f' = f) \<FF>)) \<rho>\<close>
      by (simp add: kraus_family_comp_def)
    finally show ?thesis
      by -
  qed

  have rew_\<EE>: \<open>kraus_family_map (kraus_family_filter (\<lambda>e'. e' = e) (\<EE> f))
      = kraus_family_map (kraus_family_filter (\<lambda>e'. e' = e) (\<EE>' f))\<close>
    if \<open>f \<in> kraus_map_domain \<FF>\<close>
    using that 
    by (intro ext kraus_map_eqI kraus_equivalent'_imp_equivalent kraus_family_filter_cong assms)
  have rew_\<FF>: \<open>kraus_family_map (kraus_family_filter (\<lambda>f'. f' = f) \<FF>') \<rho>
     = kraus_family_map (kraus_family_filter (\<lambda>f'. f' = f) \<FF>) \<rho>\<close>
    apply (rule sym)
    by (intro ext kraus_map_eqI kraus_equivalent'_imp_equivalent
        kraus_family_filter_cong assms)
  have \<FF>_0: \<open>kraus_family_map (kraus_family_filter (\<lambda>f'. f' = f) \<FF>) \<rho> = 0\<close>
    if \<open>f \<notin> kraus_map_domain \<FF>\<close>
  proof -
    have *: \<open>(x = f \<and> x \<in> kraus_map_domain \<FF>) \<longleftrightarrow> False\<close> for x
      using that by simp

    have \<open>kraus_equivalent' (kraus_family_filter (\<lambda>f'. f' = f) \<FF>)
             (kraus_family_filter (\<lambda>f'. f' = f) (kraus_family_filter (\<lambda>x. x \<in> kraus_map_domain \<FF>) \<FF>))\<close>
      by (auto intro!: kraus_family_filter_cong kraus_family_filter_domain intro: kraus_equivalent'_sym)
    also have \<open>kraus_equivalent' \<dots> (kraus_family_filter (\<lambda>_. False) \<FF>)\<close>
      using that by (simp add: kraus_family_filter_twice * del: kraus_family_filter_false)
    also have \<open>kraus_equivalent' \<dots> 0\<close>
      by (simp add: kraus_family_filter_false)
    finally show ?thesis
      by (auto intro!: kraus_map_eq0I kraus_equivalent'_imp_equivalent)
  qed
  show \<open>kraus_family_map' {x} (kraus_family_comp_dependent \<EE> \<FF>) \<rho> =
           kraus_family_map' {x} (kraus_family_comp_dependent \<EE>' \<FF>') \<rho>\<close>
    apply (cases \<open>f \<in> kraus_map_domain \<FF>\<close>)
    by (simp_all add: rewrite_comp[OF bdd] rewrite_comp[OF bdd'] kraus_family_comp_apply
        rew_\<EE> rew_\<FF> \<FF>_0)
qed


lift_definition kraus_map_sample :: \<open>('x \<Rightarrow> real) \<Rightarrow> ('a::chilbert_space, 'a, 'x) kraus_family\<close> is
  \<open>\<lambda>p. if (\<forall>x. p x \<ge> 0) \<and> p summable_on UNIV then range (\<lambda>x. (sqrt (p x) *\<^sub>R id_cblinfun, x)) else {}\<close>
proof -
  fix p :: \<open>'x \<Rightarrow> real\<close>
  show \<open>?thesis p\<close>
  proof (cases \<open>(\<forall>x. p x \<ge> 0) \<and> p summable_on UNIV\<close>)
    case True
    then have \<open>p abs_summable_on UNIV\<close>
      by simp
    from abs_summable_iff_bdd_above[THEN iffD1, OF this]
    obtain B where F_B: \<open>finite F \<Longrightarrow> (\<Sum>x\<in>F. p x) \<le> B\<close> for F
      apply atomize_elim
      using True by (auto simp: bdd_above_def)
    have \<open>(\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) \<le> B *\<^sub>R id_cblinfun\<close>
      if \<open>finite F\<close> and \<open>F \<subseteq> range (\<lambda>x. (sqrt (p x) *\<^sub>R id_cblinfun, x))\<close>
      for F :: \<open>('a\<Rightarrow>\<^sub>C\<^sub>L'a \<times> 'x) set\<close>
    proof -
      from that
      obtain F' where \<open>finite F'\<close> and F_def: \<open>F = (\<lambda>x. (sqrt (p x) *\<^sub>R id_cblinfun, x)) ` F'\<close>
        using finite_subset_image by blast
      then have \<open>(\<Sum>(E,x)\<in>F. E* o\<^sub>C\<^sub>L E) = (\<Sum>x\<in>F'. (sqrt (p x) *\<^sub>R id_cblinfun)* o\<^sub>C\<^sub>L (sqrt (p x) *\<^sub>R id_cblinfun))\<close>
        by (simp add: sum.reindex inj_on_def)
      also have \<open>\<dots> = (\<Sum>x\<in>F'. p x *\<^sub>R id_cblinfun)\<close>
        using True by simp
      also have \<open>\<dots> = (\<Sum>x\<in>F'. p x) *\<^sub>R id_cblinfun\<close>
        by (metis scaleR_left.sum)
      also have \<open>\<dots> \<le> B *\<^sub>R id_cblinfun\<close>
        using \<open>\<And>F. finite F \<Longrightarrow> (\<Sum>x\<in>F. p x) \<le> B\<close> \<open>finite F'\<close> positive_id_cblinfun scaleR_right_mono by blast
      finally show ?thesis
        by -
    qed
    then have \<open>kraus_family (range (\<lambda>x. (sqrt (p x) *\<^sub>R (id_cblinfun ::'a\<Rightarrow>\<^sub>C\<^sub>L_), x)))\<close>
      by (auto intro!: bdd_aboveI[where M=\<open>B *\<^sub>R id_cblinfun\<close>] simp: kraus_family_def case_prod_unfold)
    then show ?thesis
      using True by simp
  next
    case False
    then show ?thesis
      by auto
  qed
qed

lemma kraus_map_sample_norm:
  fixes p :: \<open>'x \<Rightarrow> real\<close>
  assumes \<open>\<And>x. p x \<ge> 0\<close>
  assumes \<open>p summable_on UNIV\<close>
  shows \<open>kraus_family_norm (kraus_map_sample p :: ('a::{chilbert_space,not_singleton},'a,'x) kraus_family)
             = (\<Sum>\<^sub>\<infinity>x. p x)\<close>
proof -
  define B :: \<open>'a\<Rightarrow>\<^sub>C\<^sub>L'a\<close> where \<open>B = kraus_family_bound (kraus_map_sample p)\<close>
  obtain \<psi> :: 'a where \<open>norm \<psi> = 1\<close>
    using ex_norm1_not_singleton by blast

  have \<open>\<psi> \<bullet>\<^sub>C (B *\<^sub>V \<psi>) = \<psi> \<bullet>\<^sub>C ((\<Sum>\<^sub>\<infinity>x. p x) *\<^sub>R id_cblinfun *\<^sub>V \<psi>)\<close> 
    if \<open>norm \<psi> = 1\<close> for \<psi>
  proof -
    have \<open>has_sum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family (kraus_map_sample p)) B\<close>
      using B_def kraus_family_bound_has_sum by blast
    then have \<open>has_sum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (range (\<lambda>x. (sqrt (p x) *\<^sub>R id_cblinfun, x))) B\<close>
      by (simp add: kraus_map_sample.rep_eq assms)
    then have \<open>has_sum_in cweak_operator_topology (\<lambda>x. norm (p x) *\<^sub>R id_cblinfun) UNIV B\<close>
      by (simp add: has_sum_in_reindex inj_on_def o_def)
    then have \<open>has_sum_in cweak_operator_topology (\<lambda>x. p x *\<^sub>R id_cblinfun) UNIV B\<close>
      apply (rule has_sum_in_cong[THEN iffD1, rotated])
      by (simp add: assms(1))
    then have \<open>has_sum_in euclidean (\<lambda>x. \<psi> \<bullet>\<^sub>C (p x *\<^sub>R id_cblinfun) \<psi>) UNIV (\<psi> \<bullet>\<^sub>C B \<psi>)\<close>
      apply (rule has_sum_in_comm_additive[rotated 3, OF cweak_operator_topology_continuous_evaluation, unfolded o_def])
      by (simp_all add: Modules.additive_def cblinfun.add_left cinner_simps)
    then have \<open>((\<lambda>x. of_real (p x)) has_sum (\<psi> \<bullet>\<^sub>C B \<psi>)) UNIV\<close>
      apply (simp add: scaleR_scaleC has_sum_euclidean_iff)
      using \<open>norm \<psi> = 1\<close> cnorm_eq_1 by force
    then have \<open>\<psi> \<bullet>\<^sub>C B \<psi> = (\<Sum>\<^sub>\<infinity>x. of_real (p x))\<close>
      by (simp add: infsumI)
    also have \<open>\<dots> = of_real (\<Sum>\<^sub>\<infinity>x. p x)\<close>
      by (metis infsum_of_real)
    also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C ((\<Sum>\<^sub>\<infinity>x. p x) *\<^sub>R id_cblinfun) \<psi>\<close>
      using \<open>norm \<psi> = 1\<close> by (simp add: scaleR_scaleC cnorm_eq_1)
    finally show ?thesis
      by -
  qed
  then have \<open>B = (\<Sum>\<^sub>\<infinity>x. p x) *\<^sub>R id_cblinfun\<close>
    by (rule cblinfun_cinner_eqI)
  then have \<open>norm B = norm (\<Sum>\<^sub>\<infinity>x. p x)\<close>
    by simp
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. p x)\<close>
    by (simp add: abs_of_nonneg assms infsum_nonneg)
  finally show ?thesis
    by (simp add: kraus_family_norm_def B_def)
qed

lemma kraus_family_map'_0_right[simp]: \<open>kraus_family_map' X \<EE> 0 = 0\<close>
  by (simp add: kraus_family_map'_def)

lift_definition kraus_map_infsum :: \<open>('a \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'x) kraus_family) \<Rightarrow> 'a set \<Rightarrow> ('b,'c,'a\<times>'x) kraus_family\<close> is
  \<open>\<lambda>\<EE> A. if summable_on_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<EE> a)) A
         then (\<lambda>(a,(E,x)). (E,(a,x))) ` Sigma A (\<lambda>a. Rep_kraus_family (\<EE> a)) else {}\<close>
proof (rule CollectI, rename_tac \<EE> A)
  fix \<EE> :: \<open>'a \<Rightarrow> ('b, 'c, 'x) kraus_family\<close> and A
  define \<EE>' where \<open>\<EE>' a = Rep_kraus_family (\<EE> a)\<close> for a
  show \<open>kraus_family (if summable_on_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<EE> a)) A 
                      then (\<lambda>(a,(E,x)). (E,(a,x))) ` Sigma A \<EE>'
                      else {})\<close>
  proof (cases \<open>summable_on_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<EE> a)) A\<close>)
    case True
    have \<open>kraus_family ((\<lambda>(a, E, x). (E, a, x)) ` Sigma A \<EE>')\<close>
    proof (intro kraus_familyI bdd_aboveI)
      fix C assume \<open>C \<in> (\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> (\<lambda>(a, E, x). (E, a, x)) ` Sigma A \<EE>'}\<close>
      then obtain F where \<open>finite F\<close> and F_subset: \<open>F \<subseteq> (\<lambda>(a, E, x). (E, a, x)) ` Sigma A \<EE>'\<close>
        and C_def: \<open>C = (\<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E)\<close>
        by blast
      define B F' where \<open>B = infsum_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<EE> a)) A\<close>
        and \<open>F' = (\<lambda>(E,a,x). (a,E,x)) ` F\<close>

      have [iff]: \<open>finite F'\<close>
        using \<open>finite F\<close> by (auto intro!: simp: F'_def)
      have F'_subset: \<open>F' \<subseteq> Sigma A \<EE>'\<close>
        using F_subset by (auto simp: F'_def)
      have Sigma_decomp: \<open>(SIGMA a:(\<lambda>x. fst x) ` F'. snd ` Set.filter (\<lambda>(a',Ex). a'=a) F') = F'\<close>
        by force

      have \<open>C = (\<Sum>(a, (E, x))\<in>F'. E* o\<^sub>C\<^sub>L E)\<close>
        unfolding F'_def
        apply (subst sum.reindex)
        by (auto intro!: inj_onI simp: C_def case_prod_unfold)
      also have \<open>\<dots> = (\<Sum>a\<in>fst ` F'. \<Sum>(E, x)\<in>snd ` Set.filter (\<lambda>(a',Ex). a'=a) F'. E* o\<^sub>C\<^sub>L E)\<close>
        apply (subst sum.Sigma)
        by (auto intro!: finite_imageI simp: Sigma_decomp)
      also have \<open>\<dots> = (\<Sum>a\<in>fst ` F'. infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (snd ` Set.filter (\<lambda>(a',Ex). a'=a) F'))\<close>
        apply (rule sum.cong[OF refl])
        apply (rule infsum_in_finite[symmetric])
        by auto
      also have \<open>\<dots> \<le> (\<Sum>a\<in>fst ` F'. infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (\<EE>' a))\<close>
      proof (rule sum_mono, rule infsum_mono_neutral_wot)
        fix a assume \<open>a \<in> fst ` F'\<close>
        show \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (snd ` Set.filter (\<lambda>(a', Ex). a' = a) F')\<close>
          by (auto intro!: summable_on_in_finite)
        show \<open>summable_on_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (\<EE>' a)\<close>
          using \<EE>'_def[abs_def] kraus_family_bound_has_sum summable_on_in_def by blast
        show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) \<le> (case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E)\<close> for Ex
          by blast
        have \<open>snd ` Set.filter (\<lambda>(a', Ex). a' = a) F' \<le> \<EE>' a\<close>
          using F'_subset by auto
        then show \<open>(case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E) \<le> 0\<close>
          if \<open>Ex \<in> snd ` Set.filter (\<lambda>(a', Ex). a' = a) F' - \<EE>' a\<close> for Ex
          using that by blast
        show \<open>0 \<le> (case Ex of (E, x) \<Rightarrow> E* o\<^sub>C\<^sub>L E)\<close> for Ex
          by (auto intro!: positive_cblinfun_squareI simp: case_prod_unfold)
      qed
      also have \<open>\<dots> = (\<Sum>a\<in>fst ` F'. kraus_family_bound (\<EE> a))\<close>
        unfolding \<EE>'_def
        apply (transfer' fixing: F')
        by simp
      also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<EE> a)) (fst ` F')\<close>
        apply (rule infsum_in_finite[symmetric])
        by auto
      also have \<open>\<dots> \<le> infsum_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<EE> a)) A\<close>
      proof (rule infsum_mono_neutral_wot)
        show \<open>summable_on_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<EE> a)) (fst ` F')\<close>
          by (auto intro!: summable_on_in_finite)
        show \<open>summable_on_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<EE> a)) A\<close>
          using True by blast
        show \<open>kraus_family_bound (\<EE> a) \<le> kraus_family_bound (\<EE> a)\<close> for a
          by blast
        show \<open>kraus_family_bound (\<EE> a) \<le> 0\<close> if \<open>a \<in> fst ` F' - A\<close> for a
          using F'_subset that by auto
        show \<open>0 \<le> kraus_family_bound (\<EE> a)\<close> for a
          by simp
      qed
      also have \<open>\<dots> = B\<close>
        using B_def by blast
      finally show \<open>C \<le> B\<close>
        by -
    qed
    with True show ?thesis 
      by simp
  next
    case False
    then show ?thesis
      by simp
  qed
qed

(* (* TODO move *)
instantiation cblinfun_wot :: (complex_normed_vector, complex_inner) uniform_space begin
lift_definition uniformity_cblinfun_wot :: \<open>(('a, 'b) cblinfun_wot \<times> ('a, 'b) cblinfun_wot) filter\<close> is
\<open>INF e\<in>{0::real<..}. undefined\<close>.
instance
proof *)


(* (* TODO Ref: following https://proofwiki.org/wiki/Equivalence_of_Definitions_of_REGULAR_Space *)
lemma
  shows regular_space_def_alt: \<open>regular_space T \<longleftrightarrow> (\<forall>U x. openin T U \<longrightarrow> x \<in> U \<longrightarrow> (\<exists>N V. closedin T N \<and> openin T V \<and> x \<in> V \<and> V \<subseteq> N \<and> N \<subseteq> U))\<close>
    (is \<open>_ \<longleftrightarrow> ?alt\<close>)
    and regular_space_def_alt2: \<open>regular_space T \<longleftrightarrow> (\<forall>H. closedin T H \<longrightarrow> H = \<Inter>{N. closedin T N \<and> (\<exists>V. openin T V \<and> H \<subseteq> V \<and> V \<subseteq> N)})\<close>
    (is \<open>_ \<longleftrightarrow> ?alt2\<close>)
proof -
  define \<TT> where \<open>\<TT> = topspace T\<close>
  have 1: \<open>regular_space T \<Longrightarrow> ?alt\<close>
  proof (intro allI impI)
    fix U x
    assume \<open>regular_space T\<close> and \<open>openin T U\<close> and \<open>x \<in> U\<close>
    from \<open>regular_space T\<close>[unfolded regular_space_def, rule_format, where S=\<open>\<TT> - U\<close> and y=x]
      and \<open>openin T U\<close> and \<open>x \<in> U\<close>
    obtain A V where \<open>openin T A\<close> and [iff]: \<open>openin T V\<close> and UA: \<open>\<TT> - U \<subseteq> A\<close> and [simp]: \<open>x \<in> V\<close> and \<open>A \<inter> V = {}\<close>
      apply atomize_elim
      by (metis \<TT>_def Diff_Diff_Int inf.absorb_iff2 inf_commute openin_closedin_eq)
    define N where \<open>N = \<TT> - A\<close>
    have [iff]: \<open>V \<subseteq> N\<close>
      using N_def \<TT>_def \<open>A \<inter> V = {}\<close> \<open>openin T V\<close> openin_subset by fastforce
    have [iff]: \<open>N \<subseteq> U\<close>
      using DiffD2 N_def UA by auto
    have [iff]: \<open>closedin T N\<close>
      using N_def \<open>openin T A\<close> \<TT>_def by blast
    show \<open>\<exists>N V. closedin T N \<and> openin T V \<and> x \<in> V \<and> V \<subseteq> N \<and> N \<subseteq> U\<close>
      apply (rule exI[of _ N], rule exI[of _ V])
      by simp
  qed
  have 2: \<open>?alt \<Longrightarrow> ?alt2\<close>
  proof (intro allI impI)
    fix H
    assume \<open>closedin T H\<close>
    assume alt: \<open>\<forall>U x. openin T U \<longrightarrow> x \<in> U \<longrightarrow> (\<exists>N V. closedin T N \<and> openin T V \<and> x \<in> V \<and> V \<subseteq> N \<and> N \<subseteq> U)\<close>
    define CH where \<open>CH = {N. closedin T N \<and> (\<exists>V. openin T V \<and> H \<subseteq> V \<and> V \<subseteq> N)}\<close>
    have \<open>\<Inter> CH \<subseteq> \<TT>\<close>
      using \<open>closedin T H\<close>
      by (metis (mono_tags, lifting) CH_def Inter_lower \<TT>_def closedin_subset closedin_topspace mem_Collect_eq openin_topspace)
    moreover have \<open>H \<subseteq> \<Inter> CH\<close>
      using CH_def by blast
    moreover have \<open>\<TT> - H \<subseteq> \<TT> - \<Inter> CH\<close>
    proof (rule subsetI)
      fix x assume \<open>x \<in> \<TT> - H\<close>
      with alt[rule_format, where U=\<open>\<TT> - H\<close> and x=x]
      obtain N V where \<open>closedin T N\<close> and \<open>openin T V\<close> and \<open>x \<in> V\<close> and \<open>V \<subseteq> N\<close> and \<open>N \<subseteq> \<TT> - H\<close>
        using \<open>closedin T H\<close> \<TT>_def by blast
      have \<open>H \<subseteq> \<TT> - V\<close>
        using \<open>N \<subseteq> \<TT> - H\<close> \<open>V \<subseteq> N\<close> \<open>closedin T H\<close> \<TT>_def closedin_def by fastforce
      with \<open>N \<subseteq> \<TT> - H\<close> \<open>V \<subseteq> N\<close> \<open>closedin T H\<close> \<open>closedin T N\<close> \<open>openin T V\<close>
      have \<open>\<TT> - V \<in> CH\<close>
        by (smt (verit, del_insts) CH_def \<TT>_def Diff_Diff_Int Diff_mono  closedin_def inf.absorb_iff2 mem_Collect_eq openin_subset openin_topspace)
      from \<open>x \<in> V\<close>
      have \<open>x \<notin> \<Inter> CH\<close>
        using \<open>\<TT> - V \<in> CH\<close> by blast
      then show \<open>x \<in> \<TT> - \<Inter> CH\<close>
        using \<open>x \<in> \<TT> - H\<close> by blast
    qed
    ultimately show \<open>H = \<Inter> CH\<close>
      by auto
  qed
  have 3: \<open>?alt2 \<Longrightarrow> regular_space T\<close>
  proof (unfold regular_space_def, intro allI impI)
    fix S y
    assume \<open>closedin T S\<close> and \<open>y \<in> topspace T - S\<close>
    assume alt2: \<open>\<forall>H. closedin T H \<longrightarrow> H = \<Inter> {N. closedin T N \<and> (\<exists>V. openin T V \<and> H \<subseteq> V \<and> V \<subseteq> N)}\<close>
    from alt2[rule_format, OF \<open>closedin T S\<close>]
    have S_eq: \<open>S = \<Inter> {N. closedin T N \<and> (\<exists>V. openin T V \<and> S \<subseteq> V \<and> V \<subseteq> N)}\<close>
      by -
    with \<open>y \<in> topspace T - S\<close> 
    obtain N V where \<open>closedin T N\<close> and \<open>openin T V\<close> and \<open>S \<subseteq> V\<close> and \<open>V \<subseteq> N\<close> and \<open>y \<notin> N\<close>
      apply atomize_elim by auto
    from \<open>y \<notin> N\<close> have \<open>y \<in> \<TT> - N\<close>
      using \<TT>_def \<open>y \<in> topspace T - S\<close> by blast

    show \<open>\<exists>U V. openin T U \<and> openin T V \<and> y \<in> U \<and> S \<subseteq> V \<and> U \<inter> V = {}\<close>
      apply (rule exI[of _ \<open>\<TT> - N\<close>], rule exI[of _ V])
      using \<open>y \<in> \<TT> - N\<close> \<open>openin T V\<close> \<open>S \<subseteq> V\<close> \<open>closedin T N\<close> \<open>V \<subseteq> N\<close> 
      by (auto simp: \<TT>_def)
  qed
  from 1 2 3
  show \<open>regular_space T \<longleftrightarrow> ?alt\<close> and \<open>regular_space T \<longleftrightarrow> ?alt2\<close>
    by satx+
qed *)





lemma kraus_family_bound_kraus_map_infsum:
  fixes f :: \<open>'a \<Rightarrow> ('b::chilbert_space,'c::chilbert_space,'x) kraus_family\<close>
  assumes \<open>summable_on_in cweak_operator_topology (\<lambda>a. kraus_family_bound (f a)) A\<close>
  shows \<open>kraus_family_bound (kraus_map_infsum f A) = infsum_in cweak_operator_topology (\<lambda>a. kraus_family_bound (f a)) A\<close>
proof -
  have pos: \<open>0 \<le> cblinfun_compose_wot (adj_wot a) a\<close> for a :: \<open>('b,'c) cblinfun_wot\<close>
    apply transfer'
    using positive_cblinfun_squareI by blast
  have sum3: \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>(E,_)\<in>Rep_kraus_family (f x). cblinfun_compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) summable_on A\<close>
  proof -
    define b where \<open>b x = kraus_family_bound (f x)\<close> for x
    have \<open>(\<lambda>x. Abs_cblinfun_wot (b x)) summable_on A\<close>
      using assms 
      apply (subst (asm) b_def[symmetric])
      apply (transfer' fixing: b A)
      by simp
    then show ?thesis
      by (simp add: Rep_cblinfun_wot_inverse kraus_family_bound_def' b_def)
  qed
  have sum2: \<open>(\<lambda>(E, _). cblinfun_compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) summable_on
         Rep_kraus_family (f x)\<close> if \<open>x \<in> A\<close> for x
    by (rule kraus_family_bound_summable')
  have sum1: \<open>(\<lambda>(_, E, _). cblinfun_compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E)) summable_on
    (SIGMA a:A. Rep_kraus_family (f a))\<close>
    apply (rule summable_on_Sigma_wotI)
    using sum3 sum2
    by (auto intro!: pos simp: case_prod_unfold)

  have \<open>Abs_cblinfun_wot (kraus_family_bound (kraus_map_infsum f A)) =
        (\<Sum>\<^sub>\<infinity>(E, x)\<in>Rep_kraus_family (kraus_map_infsum f A).
               cblinfun_compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    by (simp add: kraus_family_bound_def' Rep_cblinfun_wot_inverse)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E, x)\<in>(\<lambda>(a, E, xa). (E, a, xa)) ` (SIGMA a:A. Rep_kraus_family (f a)).
       cblinfun_compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    using assms by (simp add: kraus_map_infsum.rep_eq)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(a, E, x)\<in>(SIGMA a:A. Rep_kraus_family (f a)). cblinfun_compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>a\<in>A. \<Sum>\<^sub>\<infinity>(E, x)\<in>Rep_kraus_family (f a). cblinfun_compose_wot (adj_wot (Abs_cblinfun_wot E)) (Abs_cblinfun_wot E))\<close>
    apply (subst infsum_Sigma)
    using sum1 sum2 by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>a\<in>A. Abs_cblinfun_wot (kraus_family_bound (f a)))\<close>
    by (simp add: kraus_family_bound_def' Rep_cblinfun_wot_inverse)
  also have \<open>\<dots> = Abs_cblinfun_wot (infsum_in cweak_operator_topology (\<lambda>a. kraus_family_bound (f a)) A)\<close>
    apply (simp only: infsum_euclidean_eq[symmetric])
    apply (transfer' fixing: f A)
    by simp
  finally show ?thesis
    apply (rule Abs_cblinfun_wot_inject[THEN iffD1, rotated -1])
    by simp_all
qed


lemma kraus_family_bound_comp_dep_raw:
  shows \<open>kraus_family_bound (kraus_family_comp_dependent_raw \<EE> (kraus_family_of_op U))
       = sandwich (U*) (kraus_family_bound (\<EE> ()))\<close>
proof -
  write compose_wot (infixl "o\<^sub>W" 55)
  define EE where \<open>EE = Rep_kraus_family (\<EE> ())\<close>

  have sum1: \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) EE\<close>
    by (simp add: EE_def kraus_family_bound_summable)
  then have sum2: \<open>summable_on_in cweak_operator_topology (\<lambda>(E,x). U* o\<^sub>C\<^sub>L (E* o\<^sub>C\<^sub>L E)) EE\<close>
    by (simp add: case_prod_unfold summable_on_in_wot_compose_left)

  have \<open>kraus_family_bound (kraus_family_comp_dependent_raw \<EE> (kraus_family_of_op U)) = 
        infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
          ((\<lambda>((F, y), (E, x)). ((E o\<^sub>C\<^sub>L F, F, E, y, x))) ` (SIGMA (F, y):{(U, ())}. EE))\<close>
    by (simp add: kraus_family_bound.rep_eq kraus_family_comp_dependent_raw.rep_eq kraus_family_of_op.rep_eq EE_def)
  also have \<open>\<dots>  = infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
                   ((\<lambda>(E,x). (E o\<^sub>C\<^sub>L U, U, E, (), x)) ` EE)\<close>
    apply (rule arg_cong[where f=\<open>infsum_in _ _\<close>])
    by force
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). (E o\<^sub>C\<^sub>L U)* o\<^sub>C\<^sub>L (E o\<^sub>C\<^sub>L U)) EE\<close>
    apply (subst infsum_in_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold infsum_in_reindex)
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). U* o\<^sub>C\<^sub>L (E* o\<^sub>C\<^sub>L E) o\<^sub>C\<^sub>L U) EE\<close>
    by (metis (no_types, lifting) adj_cblinfun_compose cblinfun_assoc_left(1))
  also have \<open>\<dots> = U* o\<^sub>C\<^sub>L infsum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) EE o\<^sub>C\<^sub>L U\<close>
    using sum1 sum2 by (simp add: case_prod_unfold infsum_in_wot_compose_right infsum_in_wot_compose_left)
  also have \<open>\<dots> = sandwich (U*) (kraus_family_bound (\<EE> ()))\<close>
  by (simp add: EE_def kraus_family_bound.rep_eq sandwich_apply)
  finally show ?thesis
    by -
qed


lemma kraus_family_bound_comp_dep:
  shows \<open>kraus_family_bound (kraus_family_comp_dependent \<EE> (kraus_family_of_op U)) = sandwich (U*) (kraus_family_bound (\<EE> ()))\<close>
  by (simp add: kraus_family_comp_dependent_def kraus_family_map_outcome_bound kraus_family_bound_comp_dep_raw)

lemma kraus_family_bound_comp:
  shows \<open>kraus_family_bound (kraus_family_comp \<EE> (kraus_family_of_op U)) = sandwich (U*) (kraus_family_bound \<EE>)\<close>
  by (simp add: kraus_family_bound_comp_dep kraus_family_comp_def)

lemma kraus_family_norm_comp_dep_coiso:
  assumes \<open>isometry (U*)\<close>
  shows \<open>kraus_family_norm (kraus_family_comp_dependent \<EE> (kraus_family_of_op U)) = kraus_family_norm (\<EE> ())\<close>
  using assms
  by (simp add: kraus_family_bound_comp_dep kraus_family_norm_def sandwich_apply
      norm_isometry_compose norm_isometry_compose')


lemma kraus_family_norm_comp_coiso:
  assumes \<open>isometry (U*)\<close>
  shows \<open>kraus_family_norm (kraus_family_comp \<EE> (kraus_family_of_op U)) = kraus_family_norm \<EE>\<close>
  using assms
  by (simp add: kraus_family_bound_comp kraus_family_norm_def sandwich_apply
      norm_isometry_compose norm_isometry_compose')





lemma kraus_family_bound_comp_dep_raw':
  assumes \<open>isometry U\<close>
  shows \<open>kraus_family_bound (kraus_family_comp_dependent_raw (\<lambda>_. kraus_family_of_op U) \<EE>)
       = kraus_family_bound \<EE>\<close>
proof -
  write compose_wot (infixl "o\<^sub>W" 55)
  define EE where \<open>EE = Rep_kraus_family \<EE>\<close>

  have \<open>kraus_family_bound (kraus_family_comp_dependent_raw (\<lambda>_. kraus_family_of_op U) \<EE>) = 
        infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
           ((\<lambda>((F, y), (E, x)). (E o\<^sub>C\<^sub>L F, F, E, y, ())) ` (SIGMA (F, y):EE. {(U, ())}))\<close>
    by (simp add: kraus_family_bound.rep_eq kraus_family_comp_dependent_raw.rep_eq kraus_family_of_op.rep_eq EE_def)
  also have \<open>\<dots>  = infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E)
                   ((\<lambda>(E,x). (U o\<^sub>C\<^sub>L E, E, U, x, ())) ` EE)\<close>
    apply (rule arg_cong[where f=\<open>infsum_in _ _\<close>])
    by force
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). (U o\<^sub>C\<^sub>L E)* o\<^sub>C\<^sub>L (U o\<^sub>C\<^sub>L E)) EE\<close>
    apply (subst infsum_in_reindex)
    by (auto intro!: inj_onI simp: o_def case_prod_unfold infsum_in_reindex)
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L (U* o\<^sub>C\<^sub>L U) o\<^sub>C\<^sub>L E) EE\<close>
    by (metis (no_types, lifting) adj_cblinfun_compose cblinfun_assoc_left(1))
  also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>(E,x). E* o\<^sub>C\<^sub>L E) EE\<close>
    using assms by simp
  also have \<open>\<dots> = kraus_family_bound \<EE>\<close>
    by (simp add: EE_def kraus_family_bound.rep_eq sandwich_apply)
  finally show ?thesis
    by -
qed



lemma kraus_family_bound_comp_dep':
  assumes \<open>isometry U\<close>
  shows \<open>kraus_family_bound (kraus_family_comp_dependent (\<lambda>_. kraus_family_of_op U) \<EE>) = kraus_family_bound \<EE>\<close>
  using assms by (simp add: kraus_family_comp_dependent_def kraus_family_map_outcome_bound kraus_family_bound_comp_dep_raw')

lemma kraus_family_bound_comp':
  assumes \<open>isometry U\<close>
  shows \<open>kraus_family_bound (kraus_family_comp (kraus_family_of_op U) \<EE>) = kraus_family_bound \<EE>\<close>
  using assms by (simp add: kraus_family_bound_comp_dep' kraus_family_comp_def)

lemma kraus_family_norm_comp_dep':
  assumes \<open>isometry U\<close>
  shows \<open>kraus_family_norm (kraus_family_comp_dependent (\<lambda>_. kraus_family_of_op U) \<EE>) = kraus_family_norm \<EE>\<close>
  using assms
  by (simp add: kraus_family_bound_comp_dep' kraus_family_norm_def sandwich_apply
      norm_isometry_compose norm_isometry_compose')


lemma kraus_family_norm_comp':
  assumes \<open>isometry U\<close>
  shows \<open>kraus_family_norm (kraus_family_comp (kraus_family_of_op U) \<EE>) = kraus_family_norm \<EE>\<close>
  using assms
  by (simp add: kraus_family_bound_comp' kraus_family_norm_def sandwich_apply
      norm_isometry_compose norm_isometry_compose')





definition kraus_family_tensor_op_right :: \<open>('extra ell2, 'extra ell2) trace_class \<Rightarrow> ('qu ell2, ('qu\<times>'extra) ell2, unit) kraus_family\<close> where
  \<open>kraus_family_tensor_op_right \<rho> = 
  kraus_family_map_outcome_inj (\<lambda>_. ())
  (kraus_family_comp (kraus_family_tensor kraus_family_id (constant_kraus_family \<rho>))
   (kraus_family_of_op (tensor_ell2_right (ket ()))))\<close>

lemma kraus_family_bound_constant: 
  fixes \<rho> :: \<open>('a::chilbert_space, 'a) trace_class\<close>
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kraus_family_bound (constant_kraus_family \<rho>) = trace_tc \<rho> *\<^sub>C id_cblinfun\<close>
proof (rule cblinfun_cinner_eqI)
  fix \<psi> :: 'b assume \<open>norm \<psi> = 1\<close>
  have \<open>\<psi> \<bullet>\<^sub>C kraus_family_bound (constant_kraus_family \<rho>) \<psi> = trace_tc (kraus_family_map (constant_kraus_family \<rho>) (tc_butterfly \<psi> \<psi>))\<close>
    by (rule kraus_family_bound_from_map)
  also have \<open>\<dots> = trace_tc (trace_tc (tc_butterfly \<psi> \<psi>) *\<^sub>C \<rho>)\<close>
    by (simp add: kraus_family_map_constant assms)
  also have \<open>\<dots> = trace_tc \<rho>\<close>
    by (metis \<open>norm \<psi> = 1\<close> cinner_complex_def complex_cnj_one complex_vector.vector_space_assms(4) norm_mult norm_one norm_tc_butterfly norm_tc_pos of_real_hom.hom_one one_cinner_one tc_butterfly_pos)
  also have \<open>\<dots> = \<psi> \<bullet>\<^sub>C (trace_tc \<rho> *\<^sub>C id_cblinfun) \<psi>\<close>
    by (metis \<open>norm \<psi> = 1\<close> cblinfun.scaleC_left cinner_scaleC_right cnorm_eq_1 id_apply id_cblinfun.rep_eq of_complex_def one_dim_iso_id one_dim_iso_is_of_complex scaleC_conv_of_complex)
  finally show \<open>\<psi> \<bullet>\<^sub>C kraus_family_bound (constant_kraus_family \<rho>) \<psi> = \<psi> \<bullet>\<^sub>C (trace_tc \<rho> *\<^sub>C id_cblinfun) \<psi>\<close>
    by -
qed

lemma kraus_family_norm_constant:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kraus_family_norm (constant_kraus_family \<rho>) = norm \<rho>\<close>
  using assms
  by (simp add: kraus_family_norm_def kraus_family_bound_constant cmod_Re norm_tc_pos_Re trace_tc_pos)

lemma kraus_family_norm_tensor_op_right[simp]:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>kraus_family_norm (kraus_family_tensor_op_right \<rho>) = norm \<rho>\<close>
proof -
  have [simp]: \<open>isometry (tensor_ell2_right (ket ())*)\<close>
    by (simp add: unitary_tensor_ell2_right_CARD_1)
  show ?thesis
    using assms by (auto intro!: simp: kraus_family_tensor_op_right_def
        kraus_family_map_outcome_inj_norm kraus_family_norm_constant
        inj_on_def kraus_family_norm_comp_coiso
        kraus_family_norm_tensor)
qed


lemma kraus_family_bound_trace:
  assumes \<open>is_onb B\<close>
  shows \<open>kraus_family_bound (trace_kraus_family B) = id_cblinfun\<close>
  using assms
  apply (auto intro!: cblinfun_cinner_eqI simp: kraus_family_bound_from_map trace_kraus_family_is_trace)
  by (metis cinner_complex_def cnorm_eq_1 complex_cnj_one norm_tc_butterfly norm_tc_pos of_real_1 of_real_mult one_cinner_one tc_butterfly_pos)

lemma kraus_family_bound_of_op[simp]: \<open>kraus_family_bound (kraus_family_of_op A) = A* o\<^sub>C\<^sub>L A\<close>
  by (simp add: kraus_family_bound_def kraus_family_of_op.rep_eq infsum_in_finite)

lemma kraus_family_bound_id[simp]: \<open>kraus_family_bound kraus_family_id = id_cblinfun\<close>
  by (simp add: kraus_family_id_def)

lemma kraus_family_norm_trace:
  fixes B :: \<open>'a::{chilbert_space, not_singleton} set\<close>
  assumes \<open>is_onb B\<close>
  shows \<open>kraus_family_norm (trace_kraus_family B) = 1\<close>
  using assms by (simp add: kraus_family_bound_trace kraus_family_norm_def)

lemma kraus_family_bound_partial_trace[simp]:
  assumes \<open>is_onb B\<close>
  shows \<open>kraus_family_bound (kraus_map_partial_trace B) = id_cblinfun\<close>
  using assms
  by (simp add: kraus_map_partial_trace_def kraus_family_map_outcome_bound
      unitary_tensor_ell2_right_CARD_1 kraus_family_bound_comp' kraus_family_bound_tensor
      kraus_family_bound_trace)

lemma kraus_family_norm_partial_trace[simp]:
  assumes \<open>is_onb B\<close>
  shows \<open>kraus_family_norm (kraus_map_partial_trace B) = 1\<close>
  using assms by (simp add: kraus_family_norm_def)

lemma kraus_family_filter_infsum:
  assumes \<open>summable_on_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<EE> a)) A\<close>
  shows \<open>kraus_family_filter P (kraus_map_infsum \<EE> A) 
           = kraus_map_infsum (\<lambda>a. kraus_family_filter (\<lambda>x. P (a,x)) (\<EE> a)) {a\<in>A. \<exists>x. P (a,x)}\<close>
    (is \<open>?lhs = ?rhs\<close>)
proof -
  have summ: \<open>summable_on_in cweak_operator_topology (\<lambda>a. kraus_family_bound (kraus_family_filter (\<lambda>x. P (a, x)) (\<EE> a)))
      {a \<in> A. \<exists>x. P (a, x)}\<close>
  proof (rule summable_wot_boundedI)
    fix F assume \<open>finite F\<close> and F_subset: \<open>F \<subseteq> {a \<in> A. \<exists>x. P (a, x)}\<close>
    have \<open>(\<Sum>a\<in>F. kraus_family_bound (kraus_family_filter (\<lambda>x. P (a, x)) (\<EE> a)))
        \<le> (\<Sum>a\<in>F. kraus_family_bound (\<EE> a))\<close>
      by (meson kraus_family_bound_filter sum_mono)
    also have \<open>\<dots> = infsum_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<EE> a)) F\<close>
      apply (rule infsum_in_finite[symmetric])
      by (auto intro!: \<open>finite F\<close>)
    also have \<open>\<dots> \<le> infsum_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<EE> a)) A\<close>
      apply (rule infsum_mono_neutral_wot)
      using F_subset by (auto intro!:  \<open>finite F\<close> assms intro: summable_on_in_finite simp:)
    finally show \<open>(\<Sum>a\<in>F. kraus_family_bound (kraus_family_filter (\<lambda>x. P (a, x)) (\<EE> a))) \<le> \<dots>\<close>
      by -
  next
    show \<open>0 \<le> kraus_family_bound (kraus_family_filter (\<lambda>y. P (x, y)) (\<EE> x))\<close> for x
      by simp
  qed
  have \<open>Rep_kraus_family ?lhs = Rep_kraus_family ?rhs\<close>
    by (force simp add: kraus_family_filter.rep_eq kraus_map_infsum.rep_eq assms summ)
  then show \<open>?lhs = ?rhs\<close>
    by (simp add: Rep_kraus_family_inject)
qed

lemma kraus_map_infsum_empty[simp]: \<open>kraus_map_infsum \<EE> {} = 0\<close>
  apply transfer' by simp

lemma kraus_map_infsum_singleton[simp]: \<open>kraus_map_infsum \<EE> {a} = kraus_family_map_outcome_inj (\<lambda>x. (a,x)) (\<EE> a)\<close>
  apply (rule Rep_kraus_family_inject[THEN iffD1])
  by (force simp add: kraus_map_infsum.rep_eq summable_on_in_finite kraus_family_map_outcome_inj.rep_eq)

lemma kraus_map_infsum_invalid: 
  assumes \<open>\<not> summable_on_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<EE> a)) A\<close>
  shows \<open>kraus_map_infsum \<EE> A = 0\<close>
  using assms
  apply transfer'
  by simp

lemma kraus_equivalent'_kraus_map_infsum:
  fixes \<EE> \<FF> :: \<open>'a \<Rightarrow> ('b::chilbert_space, 'c::chilbert_space, 'x) kraus_family\<close>
  assumes \<open>\<And>a. a \<in> A \<Longrightarrow> kraus_equivalent' (\<EE> a) (\<FF> a)\<close>
  shows \<open>kraus_equivalent' (kraus_map_infsum \<EE> A) (kraus_map_infsum \<FF> A)\<close>
proof (cases \<open>summable_on_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<EE> a)) A\<close>)
  case True
  then have True': \<open>summable_on_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<FF> a)) A\<close>
    apply (rule summable_on_in_cong[THEN iffD1, rotated])
    by (simp add: kraus_family_bound_welldefined assms kraus_equivalent'_imp_equivalent)
  show ?thesis
  proof (rule kraus_equivalent'I)
    fix ax :: \<open>'a \<times> 'x\<close> and \<rho>
    obtain a x where ax_def: \<open>ax = (a,x)\<close>
      by fastforce
    have *: \<open>{a'. a' = a \<and> a' \<in> A} = (if a\<in>A then {a} else {})\<close>
      by auto
    have \<open>kraus_family_map' {ax} (kraus_map_infsum \<EE> A) \<rho> = (if a\<in>A then kraus_family_map' {x} (\<EE> a) \<rho> else 0)\<close>
      by (simp add: ax_def kraus_family_map'_def True kraus_family_filter_infsum * 
          kraus_family_map_outcome_inj_same_map inj_on_def)
    also from assms have \<open>\<dots> = (if a\<in>A then kraus_family_map' {x} (\<FF> a) \<rho> else 0)\<close>
      by (auto intro!: kraus_family_map'_eqI)
    also have \<open>\<dots> = kraus_family_map' {ax} (kraus_map_infsum \<FF> A) \<rho>\<close>
      by (simp add: ax_def kraus_family_map'_def True' kraus_family_filter_infsum * 
          kraus_family_map_outcome_inj_same_map inj_on_def)
    finally show \<open>kraus_family_map' {ax} (kraus_map_infsum \<EE> A) \<rho> = kraus_family_map' {ax} (kraus_map_infsum \<FF> A) \<rho>\<close>
      by -
  qed
next
  case False
  then have False': \<open>\<not> summable_on_in cweak_operator_topology (\<lambda>a. kraus_family_bound (\<FF> a)) A\<close>
    apply (subst (asm) assms[THEN kraus_equivalent'_imp_equivalent, THEN kraus_family_bound_welldefined, THEN summable_on_in_cong])
    by auto
  show ?thesis
    by (simp add: kraus_map_infsum_invalid False False')
qed

(* lemma
(* TODO Ref: Nielsen Chuang, Th 2.6, generalized to infdim *)
  assumes \<open>((\<lambda>i. tc_butterfly (\<psi> i) (\<psi> i)) has_sum t) X\<close>
  assumes \<open>((\<lambda>i. tc_butterfly (\<phi> i) (\<phi> i)) has_sum t) Y\<close>
  shows \<open>xx\<close>
proof -
  thm butterfly_spectral_dec_vec_tc_has_sum
  have \<open>is_orthogonal \<gamma> (\<psi> i)\<close> if \<open>\<And>k. k \<in> spectral_dec_vecs_tc t \<Longrightarrow> is_orthogonal \<gamma> k\<close> for \<gamma> i
    by x
  have \<open>\<psi> i \<in> closure (cspan (spectral_dec_vecs_tc t))\<close> for i
    by (metis \<open>\<And>i \<gamma>. (\<And>k. k \<in> spectral_dec_vecs_tc t \<Longrightarrow> is_orthogonal \<gamma> k) \<Longrightarrow> is_orthogonal \<gamma> (\<psi> i)\<close> is_orthogonal_sym orthogonal_complementI orthogonal_complement_orthoI orthogonal_complement_orthogonal_complement_closure_cspan)
by -
  then obtain c where \<open>\<psi> i = \<close>

lemma
  assumes \<open>kraus_equivalent \<EE> \<FF>\<close>
  shows \<open>xxx\<close>
proof -


lemma
  assumes \<open>kraus_equivalent \<EE> \<FF>\<close>
  shows \<open>Abstract_Topology.closure_of XXX (fst ` Rep_kraus_family \<EE>) = Abstract_Topology.closure_of XXX (fst ` Rep_kraus_family \<FF>)\<close>
 *)

end
