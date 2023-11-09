theory Temporary_Compact_Op
  imports Tensor_Product.Compact_Operators
    Registers2.Missing_Bounded_Operators
    Tensor_Product.Unsorted_HSTP
begin

(* TODO clean up names *)

fun eigenvalues_of :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> nat \<Rightarrow> complex\<close>
  and eigenvalues_of_E :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> nat \<Rightarrow> 'a ccsubspace\<close>
  and eigenvalues_of_T :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  where \<open>eigenvalues_of a n = largest_eigenvalue (eigenvalues_of_T a n)\<close>
  | \<open>eigenvalues_of_E a n = (if eigenvalues_of a n = 0 then 0 else eigenspace (eigenvalues_of a n) (eigenvalues_of_T a n))\<close>
  | \<open>eigenvalues_of_T a (Suc n) = eigenvalues_of_T a n o\<^sub>C\<^sub>L Proj (- eigenvalues_of_E a n)\<close>
  | \<open>eigenvalues_of_T a 0 = a\<close>

definition eigenvalues_of_P :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close> where
  \<open>eigenvalues_of_P a n = Proj (eigenvalues_of_E a n)\<close>

declare eigenvalues_of.simps[simp del]
declare eigenvalues_of_E.simps[simp del]

lemmas eigenvalues_of_def = eigenvalues_of.simps
lemmas eigenvalues_of_E_def = eigenvalues_of_E.simps

lemma eigenvalues_of_op_selfadj:
  assumes \<open>selfadjoint a\<close>
  shows \<open>selfadjoint (eigenvalues_of_T a n)\<close>
proof (induction n)
  case 0
  with assms show ?case
    by simp
next
  case (Suc n)
  define E T where \<open>E = eigenvalues_of_E a n\<close> and \<open>T = eigenvalues_of_T a n\<close>
  from Suc have \<open>normal_op T\<close>
    by (auto intro!: selfadjoint_imp_normal simp: T_def)
  then have \<open>reducing_subspace E T\<close>
    apply (auto intro!: eigenspace_is_reducing simp: eigenvalues_of_E_def E_def T_def)
    by -
  then have \<open>reducing_subspace (- E) T\<close>
    by simp
  then have *: \<open>Proj (- E) o\<^sub>C\<^sub>L T o\<^sub>C\<^sub>L Proj (- E) = T o\<^sub>C\<^sub>L Proj (- E)\<close>
    by (simp add: invariant_subspace_iff_PAP reducing_subspace_def)
  show ?case
    using Suc
    apply (simp add: flip: T_def E_def * )
    by (simp add: selfadjoint_def adj_Proj cblinfun_compose_assoc)
qed


lemma eigenvalues_of_T_compact:
  assumes \<open>compact_op a\<close>
  shows \<open>compact_op (eigenvalues_of_T a n)\<close>
  apply (induction n)
  by (auto intro!: compact_op_comp_left assms)

lemma eigenvalues_of_eigenvalues_of_T:
  fixes a :: \<open>'a::{chilbert_space, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>eigenvalues_of a n \<in> eigenvalues (eigenvalues_of_T a n)\<close>
  by (auto intro!: largest_eigenvalue_ex eigenvalues_of_T_compact eigenvalues_of_op_selfadj assms
      simp: eigenvalues_of_def)

lemma eigenvalues_of_P_finite_rank: 
  assumes \<open>compact_op a\<close>
  shows \<open>finite_rank (eigenvalues_of_P a n)\<close>
  apply (cases \<open>eigenvalues_of a n = 0\<close>)
  by (auto intro!: finite_rank_Proj_finite_dim compact_op_eigenspace_finite_dim eigenvalues_of_T_compact assms
      simp: eigenvalues_of_P_def eigenvalues_of_E_def)

lemma norm_eigenvalues_of_T:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>norm (eigenvalues_of_T a n) = cmod (eigenvalues_of a n)\<close>
  by (simp add: eigenvalues_of_def cmod_largest_eigenvalue eigenvalues_of_T_compact eigenvalues_of_op_selfadj assms)

lemma eigenvalues_of_T_eigenvectors:
  assumes \<open>n \<ge> m\<close> and \<open>e \<noteq> 0\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>eigenspace e (eigenvalues_of_T a n) \<le> eigenspace e (eigenvalues_of_T a m)\<close>
proof -
  have *: \<open>eigenspace e (eigenvalues_of_T a (Suc n)) \<le> eigenspace e (eigenvalues_of_T a n)\<close> for n
  proof (intro ccsubspace_leI subsetI)
    fix h
    assume asm: \<open>h \<in> space_as_set (eigenspace e (eigenvalues_of_T a (Suc n)))\<close>
    have \<open>orthogonal_spaces (eigenspace e (eigenvalues_of_T a (Suc n))) (kernel (eigenvalues_of_T a (Suc n)))\<close>
      using eigenvalues_of_op_selfadj[of a \<open>Suc n\<close>] \<open>e \<noteq> 0\<close> \<open>selfadjoint a\<close>
      by (auto intro!: eigenspaces_orthogonal selfadjoint_imp_normal eigenvalues_of_op_selfadj
          simp: eigenvalues_of_E_def simp flip: eigenspace_0)
    then have \<open>eigenspace e (eigenvalues_of_T a (Suc n)) \<le> - kernel (eigenvalues_of_T a (Suc n))\<close>
      using orthogonal_spaces_leq_compl by blast 
    also have \<open>\<dots> \<le> - eigenvalues_of_E a n\<close>
      by (auto intro!: ccsubspace_leI kernel_memberI simp: Proj_0_compl)
    finally have \<open>h \<in> space_as_set (- eigenvalues_of_E a n)\<close>
      using asm by (simp add: Set.basic_monos(7) less_eq_ccsubspace.rep_eq)
    then have \<open>eigenvalues_of_T a n h = eigenvalues_of_T a (Suc n) h\<close>
      by (simp add: Proj_fixes_image) 
    also have \<open>\<dots> = e *\<^sub>C h\<close>
      using asm eigenspace_memberD by blast 
    finally show \<open>h \<in> space_as_set (eigenspace e (eigenvalues_of_T a n))\<close>
      by (simp add: eigenspace_memberI) 
  qed
  define k where \<open>k = n - m\<close>
  from * have \<open>eigenspace e (eigenvalues_of_T a (m + k)) \<le> eigenspace e (eigenvalues_of_T a m)\<close>
    apply (induction k)
     apply (auto intro!: simp: simp del: eigenvalues_of_T.simps simp flip: )
    using order_trans_rules(23) by blast 
  then show ?thesis
    using \<open>n \<ge> m\<close> by (simp add: k_def)
qed

lemma not_not_singleton_eigenvalue_of_0:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<not> class.not_singleton TYPE('a)\<close>
  shows \<open>eigenvalues_of a n = 0\<close>
proof -
  from assms have \<open>eigenvalues_of_T a n = 0\<close>
    by (rule not_not_singleton_cblinfun_zero)
  then have \<open>largest_eigenvalue (eigenvalues_of_T a n) = 0\<close>
    by simp
  then show ?thesis
    by (simp add: eigenvalues_of_def)
qed

lemma eigenvalues_of_are_eigenvalues_aux:
(* TODO conway, functional, Thm II.5.1 *)
  fixes a :: \<open>'a::{chilbert_space, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes eigen_neq0: \<open>eigenvalues_of a n \<noteq> 0\<close>
  shows \<open>eigenvalues_of a n \<in> eigenvalues a\<close>
proof -
  define e where \<open>e = eigenvalues_of a n\<close>
  with assms have \<open>e \<noteq> 0\<close>
    by fastforce

  from eigenvalues_of_T_eigenvectors[where m=0 and a=a and n=n, OF _ \<open>e \<noteq> 0\<close> \<open>selfadjoint a\<close>]
  have 1: \<open>eigenspace e (eigenvalues_of_T a n) \<le> eigenspace e a\<close>
    by simp
  have 2: \<open>eigenvalues_of_E a n \<noteq> \<bottom>\<close>
  proof -
    have \<open>eigenvalues_of a n \<in> eigenvalues (eigenvalues_of_T a n)\<close>
      by (simp add: assms(1) assms(2) eigenvalues_of.simps eigenvalues_of_T_compact eigenvalues_of_op_selfadj largest_eigenvalue_ex) 
    then show ?thesis
      using \<open>e \<noteq> 0\<close> by (simp add: eigenvalues_def eigenvalues_of_E.simps e_def)
  qed
  from 1 2 have \<open>eigenspace e a \<noteq> \<bottom>\<close>
    by (auto simp: eigenvalues_of_E_def bot_unique simp flip: e_def simp: \<open>e \<noteq> 0\<close>)
  then show \<open>e \<in> eigenvalues a\<close>
    by (simp add: eigenvalues_def)
qed

lemma eigenvalues_of_are_eigenvalues:
(* TODO conway, functional, Thm II.5.1 *)
  fixes a :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes eigen_neq0: \<open>eigenvalues_of a n \<noteq> 0\<close>
  shows \<open>eigenvalues_of a n \<in> eigenvalues a\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    using chilbert_space_axioms True assms
    by (rule eigenvalues_of_are_eigenvalues_aux[internalize_sort' 'a])
next
  case False
  then have \<open>eigenvalues_of a n = 0\<close>
    by (rule not_not_singleton_eigenvalue_of_0)
  with assms show ?thesis
    by simp
qed

hide_fact eigenvalues_of_are_eigenvalues_aux

lemma eigenvalues_of_decreasing:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes \<open>n \<ge> m\<close>
  shows \<open>cmod (eigenvalues_of a n) \<le> cmod (eigenvalues_of a m)\<close>
proof -
  have \<open>norm (eigenvalues_of_T a (Suc n)) \<le> norm (eigenvalues_of_T a n)\<close> for n
    apply simp
    by (smt (verit) Proj_partial_isometry cblinfun_compose_zero_right mult_cancel_left2 norm_cblinfun_compose norm_le_zero_iff norm_partial_isometry) 
  then have *: \<open>cmod (eigenvalues_of a (Suc n)) \<le> cmod (eigenvalues_of a n)\<close> for n
    by (simp add: cmod_largest_eigenvalue eigenvalues_of_T_compact assms eigenvalues_of_op_selfadj eigenvalues_of_def
        del: eigenvalues_of_T.simps)
  define k where \<open>k = n - m\<close>
  have \<open>cmod (eigenvalues_of a (m + k)) \<le> cmod (eigenvalues_of a m)\<close>
    apply (induction k arbitrary: m)
     apply simp
    by (metis "*" add_Suc_right order_trans_rules(23)) 
  with \<open>n \<ge> m\<close> show ?thesis
    by (simp add: k_def)
qed


lemma eigenvalues_of_distinct_aux:
  fixes a :: \<open>('a::{chilbert_space, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  assumes \<open>n \<noteq> m\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes neq0: \<open>eigenvalues_of a n \<noteq> 0\<close>
  shows \<open>eigenvalues_of a n \<noteq> eigenvalues_of a m\<close>
proof (rule ccontr)
  assume \<open>\<not> eigenvalues_of a n \<noteq> eigenvalues_of a m\<close>
  then have eq: \<open>eigenvalues_of a n = eigenvalues_of a m\<close>
    by blast
  wlog nm: \<open>n > m\<close> goal False generalizing n m keeping eq neq0
    using hypothesis[of n m] negation assms eq neq0
    by auto
  define e where \<open>e = eigenvalues_of a n\<close>
  with neq0 have \<open>e \<noteq> 0\<close>
    by simp

  have \<open>eigenvalues_of_E a n \<noteq> \<bottom>\<close>
  proof -
    have \<open>e \<in> eigenvalues (eigenvalues_of_T a n)\<close>
      by (auto intro!: eigenvalues_of_eigenvalues_of_T assms simp: e_def)
    then show ?thesis
      by (simp add: eigenvalues_of_E_def eigenvalues_def e_def neq0)
  qed
  then obtain h where \<open>norm h = 1\<close> and h_En: \<open>h \<in> space_as_set (eigenvalues_of_E a n)\<close>
    using ccsubspace_contains_unit by blast 
  have T_Sucm_h: \<open>eigenvalues_of_T a (Suc m) h = 0\<close>
  proof -
    have \<open>eigenvalues_of_E a n = eigenspace e (eigenvalues_of_T a n)\<close>
      by (simp add: eigenvalues_of_E_def e_def neq0)
    also have \<open>\<dots> \<le> eigenspace e (eigenvalues_of_T a m)\<close>
      using \<open>n > m\<close> \<open>e \<noteq> 0\<close> assms
      by (auto intro!: eigenvalues_of_T_eigenvectors simp: )
    also have \<open>\<dots> = eigenvalues_of_E a m\<close>
      using neq0 by (simp add: eigenvalues_of_E_def e_def eq)
    finally have \<open>h \<in> space_as_set (eigenvalues_of_E a m)\<close>
      using h_En
      by (simp add: basic_trans_rules(31) less_eq_ccsubspace.rep_eq) 
    then show \<open>eigenvalues_of_T a (Suc m) h = 0\<close>
      by (simp add: Proj_0_compl)
  qed
  have \<open>eigenvalues_of_T a (Suc m + k) h = 0\<close> if \<open>k \<le> n - m - 1\<close> for k
  proof (insert that, induction k)
    case 0
    from T_Sucm_h show ?case
      by simp
  next
    case (Suc k)
    define mk1 where \<open>mk1 = Suc (m + k)\<close>
    from Suc.prems have \<open>mk1 \<le> n\<close>
      using mk1_def by linarith 
    have \<open>eigenspace e (eigenvalues_of_T a n) \<le> eigenspace e (eigenvalues_of_T a mk1)\<close>
      using \<open>mk1 \<le> n\<close> \<open>e \<noteq> 0\<close> \<open>selfadjoint a\<close>
      by (rule eigenvalues_of_T_eigenvectors)
    with h_En have h_mk1: \<open>h \<in> space_as_set (eigenspace e (eigenvalues_of_T a mk1))\<close>
      by (auto simp: e_def eigenvalues_of_E_def less_eq_ccsubspace.rep_eq neq0)
    have \<open>Proj (- eigenvalues_of_E a mk1) *\<^sub>V h = 0 \<or> Proj (- eigenvalues_of_E a mk1) *\<^sub>V h = h\<close>
    proof (cases \<open>e = eigenvalues_of a mk1\<close>)
      case True
      from h_mk1 have \<open>Proj (- eigenvalues_of_E a mk1) h = 0\<close>
        using \<open>e \<noteq> 0\<close> by (simp add: Proj_0_compl True eigenvalues_of_E_def)
      then show ?thesis 
        by simp
    next
      case False
      have \<open>orthogonal_spaces (eigenspace e (eigenvalues_of_T a mk1)) (eigenvalues_of_E a mk1)\<close>
        by (simp add: False assms eigenspaces_orthogonal eigenvalues_of_E.simps eigenvalues_of_op_selfadj selfadjoint_imp_normal) 
      with h_mk1 have \<open>h \<in> space_as_set (- eigenvalues_of_E a mk1)\<close>
        using less_eq_ccsubspace.rep_eq orthogonal_spaces_leq_compl by blast 
      then have \<open>Proj (- eigenvalues_of_E a mk1) h = h\<close>
        by (rule Proj_fixes_image)
      then show ?thesis 
        by simp
    qed
    with Suc show ?case
      by (auto simp: mk1_def)
  qed
  from this[where k=\<open>n - m - 1\<close>]
  have \<open>eigenvalues_of_T a n h = 0\<close>
    using \<open>n > m\<close>
    by (simp del: eigenvalues_of_T.simps)
  moreover from h_En have \<open>eigenvalues_of_T a n h = e *\<^sub>C h\<close>
    by (simp add: neq0 e_def eigenspace_memberD eigenvalues_of_E_def)
  ultimately show False
    using \<open>norm h = 1\<close> \<open>e \<noteq> 0\<close>
    by force
qed

lemma eigenvalues_of_distinct:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>n \<noteq> m\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes neq0: \<open>eigenvalues_of a n \<noteq> 0\<close>
  shows \<open>eigenvalues_of a n \<noteq> eigenvalues_of a m\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    using chilbert_space_axioms True assms
    by (rule eigenvalues_of_distinct_aux[internalize_sort' 'a])
next
  case False
  then have \<open>eigenvalues_of a n = 0\<close>
    by (rule not_not_singleton_eigenvalue_of_0)
  with assms show ?thesis
    by simp
qed

hide_fact eigenvalues_of_distinct_aux

lemma eigenvalues_of_tendsto_0:
  (* In the proof of Conway, Functional, Theorem II.5.1 *)
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>eigenvalues_of a \<longlonglongrightarrow> 0\<close>
proof (cases \<open>\<exists>n. eigenvalues_of a n = 0\<close>)
  case True
  then obtain n where \<open>eigenvalues_of a n = 0\<close>
    by auto
  then have \<open>eigenvalues_of a m = 0\<close> if \<open>m \<ge> n\<close> for m
    using eigenvalues_of_decreasing[OF assms that]
    by simp
  then show \<open>eigenvalues_of a \<longlonglongrightarrow> 0\<close>
    by (auto intro!: tendsto_eventually eventually_sequentiallyI)
next
  case False
  define E where \<open>E = eigenvalues_of a\<close>
  from False have \<open>E n \<in> eigenvalues a\<close> for n
    by (simp add: eigenvalues_of_are_eigenvalues assms E_def)
  then have \<open>eigenspace (E n) a \<noteq> 0\<close> for n
    by (simp add: eigenvalues_def)
  then obtain e where e_E: \<open>e n \<in> space_as_set (eigenspace (E n) a)\<close>
    and norm_e: \<open>norm (e n) = 1\<close> for n
    apply atomize_elim
    using ccsubspace_contains_unit 
    by (auto intro!: choice2)
  then obtain h n where \<open>strict_mono n\<close> and aen_lim: \<open>(\<lambda>j. a (e (n j))) \<longlonglongrightarrow> h\<close>
  proof atomize_elim
    from \<open>compact_op a\<close>
    have compact:\<open>compact (closure (a ` cball 0 1))\<close>
      by (simp add: compact_op_def2)
    from norm_e have \<open>a (e n) \<in> closure (a ` cball 0 1)\<close> for n
      using closure_subset[of \<open>a ` cball 0 1\<close>] by auto
    with compact[unfolded compact_def, rule_format, of \<open>\<lambda>n. a (e n)\<close>]
    show \<open>\<exists>n h. strict_mono n \<and> (\<lambda>j. a (e (n j))) \<longlonglongrightarrow> h\<close>
      by (auto simp: o_def)
  qed
  have ortho_en: \<open>is_orthogonal (e (n j)) (e (n k))\<close> if \<open>j \<noteq> k\<close> for j k
  proof -
    have \<open>n j \<noteq> n k\<close>
      by (simp add: \<open>strict_mono n\<close> strict_mono_eq that)
    then have \<open>E (n j) \<noteq> E (n k)\<close>
      unfolding E_def
      apply (rule eigenvalues_of_distinct)
      using False assms by auto
    then have \<open>orthogonal_spaces (eigenspace (E (n j)) a) (eigenspace (E (n k)) a)\<close>
      apply (rule eigenspaces_orthogonal)
      by (simp add: assms(2) selfadjoint_imp_normal) 
    with e_E show ?thesis
      using orthogonal_spaces_def by blast
  qed
  have aEe: \<open>a (e n) = E n *\<^sub>C e n\<close> for n
    by (simp add: e_E eigenspace_memberD)
  obtain \<alpha> where E_lim: \<open>(\<lambda>n. norm (E n)) \<longlonglongrightarrow> \<alpha>\<close>
    apply (rule_tac decseq_convergent[where X=\<open>\<lambda>n. cmod (E n)\<close> and B=0])
    using eigenvalues_of_decreasing[OF assms]
    by (auto intro!: simp: decseq_def E_def)
  then have \<open>\<alpha> \<ge> 0\<close>
    apply (rule LIMSEQ_le_const)
    by simp
  have aen_diff: \<open>norm (a (e (n j)) - a (e (n k))) \<ge> \<alpha> * sqrt 2\<close> if \<open>j \<noteq> k\<close> for j k
  proof -
    from E_lim and eigenvalues_of_decreasing[OF assms, folded E_def]
    have E_geq_\<alpha>: \<open>cmod (E n) \<ge> \<alpha>\<close> for n
      apply (rule_tac decseq_ge[unfolded decseq_def, rotated])
      by auto
    have \<open>(norm (a (e (n j)) - a (e (n k))))\<^sup>2 = (cmod (E (n j)))\<^sup>2 + (cmod (E (n k)))\<^sup>2\<close>
      by (simp add: polar_identity_minus aEe that ortho_en norm_e)
    also have \<open>\<dots> \<ge> \<alpha>\<^sup>2 + \<alpha>\<^sup>2\<close> (is \<open>_ \<ge> \<dots>\<close>)
      apply (rule add_mono)
      using E_geq_\<alpha> \<open>\<alpha> \<ge> 0\<close> by auto
    also have \<open>\<dots> = (\<alpha> * sqrt 2)\<^sup>2\<close>
      by (simp add: algebra_simps)
    finally show ?thesis
      apply (rule power2_le_imp_le)
      by simp
  qed
  have \<open>\<alpha> = 0\<close>
  proof -
    have \<open>\<alpha> * sqrt 2 < \<epsilon>\<close> if \<open>\<epsilon> > 0\<close> for \<epsilon>
    proof -
      from \<open>strict_mono n\<close> have cauchy: \<open>Cauchy (\<lambda>k. a (e (n k)))\<close>
        using LIMSEQ_imp_Cauchy aen_lim by blast
      obtain k where k: \<open>\<forall>m\<ge>k. \<forall>na\<ge>k. dist (a *\<^sub>V e (n m)) (a *\<^sub>V e (n na)) < \<epsilon>\<close>
        apply atomize_elim
        using cauchy[unfolded Cauchy_def, rule_format, OF \<open>\<epsilon> > 0\<close>]
        by simp
      define j where \<open>j = Suc k\<close>
      then have \<open>j \<noteq> k\<close>
        by simp
      from k have \<open>dist (a (e (n j))) (a (e (n k))) < \<epsilon>\<close>
        by (simp add: j_def)
      with aen_diff[OF \<open>j \<noteq> k\<close>] show \<open>\<alpha> * sqrt 2 < \<epsilon>\<close>
        by (simp add: Cauchy_def dist_norm)
    qed
    with \<open>\<alpha> \<ge> 0\<close> show \<open>\<alpha> = 0\<close>
      by (smt (verit) linordered_semiring_strict_class.mult_pos_pos real_sqrt_le_0_iff)
  qed
  with E_lim show ?thesis
    by (auto intro!: tendsto_norm_zero_cancel simp: E_def)
qed

lemma eigenvalues_of_T_tendsto:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>eigenvalues_of_T a \<longlonglongrightarrow> 0\<close>
  apply (rule tendsto_norm_zero_cancel)
  using eigenvalues_of_tendsto_0[OF assms]
  apply (simp add: norm_eigenvalues_of_T assms)
  using tendsto_norm_zero by blast 

lemma eigenvalues_of_T_eigenvalues_of_P:
  \<open>eigenvalues_of_T a n = a - (\<Sum>i<n. eigenvalues_of a i *\<^sub>C eigenvalues_of_P a i)\<close>
proof (induction n)
  case 0
  show ?case
    by simp
next
  case (Suc n)
  have \<open>eigenvalues_of_T a (Suc n) = eigenvalues_of_T a n o\<^sub>C\<^sub>L Proj (- eigenvalues_of_E a n)\<close>
    by simp
  also have \<open>\<dots> = eigenvalues_of_T a n - eigenvalues_of a n *\<^sub>C eigenvalues_of_P a n\<close> (is \<open>?lhs = ?rhs\<close>)
  proof -
    have \<open>?lhs h = ?rhs h\<close> if \<open>h \<in> space_as_set (eigenvalues_of_E a n)\<close> for h
    proof -
      have \<open>?lhs h = 0\<close>
        by (simp add: Proj_0_compl that) 
      have \<open>eigenvalues_of_T a n *\<^sub>V h = eigenvalues_of a n *\<^sub>C h\<close>
        by (smt (verit, best) Proj_fixes_image \<open>(eigenvalues_of_T a n o\<^sub>C\<^sub>L Proj (- eigenvalues_of_E a n)) *\<^sub>V h = 0\<close> cblinfun_apply_cblinfun_compose complex_vector.scale_eq_0_iff eigenspace_memberD eigenvalues_of_E.elims kernel_Proj kernel_cblinfun_compose kernel_memberD kernel_memberI ortho_involution that) 
      also have \<open>\<dots> = eigenvalues_of a n *\<^sub>C (eigenvalues_of_P a n *\<^sub>V h)\<close>
        by (simp add: Proj_fixes_image eigenvalues_of_P_def that) 
      finally
      have \<open>?rhs h = 0\<close>
        by (simp add: cblinfun.diff_left)
      with \<open>?lhs h = 0\<close> show ?thesis
        by simp
    qed
    moreover have \<open>?lhs h = ?rhs h\<close> if \<open>h \<in> space_as_set (- eigenvalues_of_E a n)\<close> for h
      by (simp add: Proj_0_compl Proj_fixes_image cblinfun.diff_left eigenvalues_of_P_def that) 
    ultimately have \<open>?lhs h = ?rhs h\<close> 
      if \<open>h \<in> space_as_set (eigenvalues_of_E a n \<squnion> - eigenvalues_of_E a n) \<close> for h
      using that by (rule eq_on_ccsubspaces_sup)
    then show \<open>?lhs = ?rhs\<close>
      by (auto intro!: cblinfun_eqI simp add: )
  qed
  also have \<open>\<dots> = a - (\<Sum>i<Suc n. eigenvalues_of a i *\<^sub>C eigenvalues_of_P a i)\<close>
    by (simp add: Suc.IH) 
  finally show ?case
    by -
qed

lemma sequential_tendsto_reorder:
  assumes \<open>inj g\<close>
  assumes \<open>f \<longlonglongrightarrow> l\<close>
  shows \<open>(f o g) \<longlonglongrightarrow> l\<close>
proof (intro lim_explicit[THEN iffD2] impI allI)
  fix S assume \<open>open S\<close> and \<open>l \<in> S\<close>
  with \<open>f \<longlonglongrightarrow> l\<close>
  obtain M where M: \<open>f m \<in> S\<close> if \<open>m \<ge> M\<close> for m
    using tendsto_obtains_N by blast 
  define N where \<open>N = Max (g -` {..<M}) + 1\<close>
  have N: \<open>g n \<ge> M\<close> if \<open>n \<ge> N\<close> for n
  proof -
    from \<open>inj g\<close> have \<open>finite (g -` {..<M})\<close>
      using finite_vimageI by blast 
    then have \<open>N > n\<close> if \<open>n \<in> g -` {..<M}\<close> for n
      using N_def that
      by (simp add: less_Suc_eq_le) 
    then have \<open>N > n\<close> if \<open>g n < M\<close> for n
      by (simp add: that) 
    with that show \<open>g n \<ge> M\<close>
      using linorder_not_less by blast 
  qed
  from N M show \<open>\<exists>N. \<forall>n\<ge>N. (f \<circ> g) n \<in> S\<close>
    by auto
qed




lemma spectral_decomp_tendsto:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>(\<lambda>n. eigenvalues_of a n *\<^sub>C eigenvalues_of_P a n)  sums  a\<close>
proof -
(*   define f where \<open>f n = eigenvalues_of a n *\<^sub>C eigenvalues_of_P a n\<close> for n
  from eigenvalues_of_T_tendsto[OF assms]
  have \<open>f \<longlonglongrightarrow> a\<close>
    by (simp add: tendsto_diff_const_left_rewrite f_def) *)
  from eigenvalues_of_T_tendsto[OF assms]
  have \<open>(\<lambda>n. a - eigenvalues_of_T a n) \<longlonglongrightarrow> a\<close>
    by (simp add: tendsto_diff_const_left_rewrite)
  moreover from eigenvalues_of_T_eigenvalues_of_P[of a]
  have \<open>a - eigenvalues_of_T a n = (\<Sum>i<n. eigenvalues_of a i *\<^sub>C eigenvalues_of_P a i)\<close> for n
    by simp
  ultimately show ?thesis
    by (simp add: sums_def)
qed

lemma eigenvalues_of_real:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>eigenvalues_of a n \<in> \<real>\<close>
  by (metis Reals_0 assms(1) assms(2) eigenvalue_selfadj_real eigenvalues_of_are_eigenvalues) 


(* lemma eigenvalues_of_E_eigenspaces:
  assumes \<open>selfadjoint a\<close>
  assumes \<open>eigenvalues_of a n \<noteq> 0\<close>
  shows \<open>eigenvalues_of_E a n = eigenspace (eigenvalues_of a n) a\<close>
proof (rule antisym)
  define e where \<open>e = eigenvalues_of a n\<close>
  from assms have \<open>e \<noteq> 0\<close>
    by (simp add: e_def) 
  from eigenvalues_of_T_eigenvectors[where m=0 and a=a and n=n, OF _ \<open>e \<noteq> 0\<close> \<open>selfadjoint a\<close>]
  show \<open>eigenvalues_of_E a n \<le> eigenspace e a\<close>
    by (simp add: eigenvalues_of_E_def flip: e_def)
  show \<open>eigenvalues_of_E a n \<ge> eigenspace e a\<close>
  proof (rule ccsubspace_leI_unit)
    fix h assume \<open>h \<in> space_as_set (eigenspace e a)\<close>
    show \<open>h \<in> space_as_set (eigenvalues_of_E a n)\<close>
      by x
  qed
qed *)

lemma eigenvalues_of_E_orthogonal:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes \<open>n \<noteq> m\<close>
  shows \<open>orthogonal_spaces (eigenvalues_of_E a n) (eigenvalues_of_E a m)\<close>
proof (cases \<open>eigenvalues_of a n = 0 \<or> eigenvalues_of a m = 0\<close>)
  case True
  then show ?thesis
    by (auto intro!: simp: eigenvalues_of_E_def)
next
  case False
  have \<open>eigenvalues_of_E a n \<le> eigenspace (eigenvalues_of a n) a\<close>
    using \<open>selfadjoint a\<close>
    by (metis False eigenvalues_of_E.elims eigenvalues_of_T.simps(2) eigenvalues_of_T_eigenvectors zero_le) 
  moreover have \<open>eigenvalues_of_E a m \<le> eigenspace (eigenvalues_of a m) a\<close>
    using \<open>selfadjoint a\<close>
    by (metis False eigenvalues_of_E.elims eigenvalues_of_T.simps(2) eigenvalues_of_T_eigenvectors zero_le) 
  moreover have \<open>orthogonal_spaces (eigenspace (eigenvalues_of a n) a) (eigenspace (eigenvalues_of a m) a)\<close>
    apply (intro eigenspaces_orthogonal selfadjoint_imp_normal assms
        eigenvalues_of_distinct)
    using False by simp
  ultimately show ?thesis
    by (meson order.trans orthocomplemented_lattice_class.compl_mono orthogonal_spaces_leq_compl) 
qed

lemma eigenvalues_of_P_pos: \<open>eigenvalues_of_P a n \<ge> 0\<close>
  apply (auto intro!: simp: eigenvalues_of_P_def)
  by (metis Proj_bot Proj_mono bot.extremum) 

lemma
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows spectral_decomp_tendsto_pos_op: \<open>(\<lambda>n. max 0 (eigenvalues_of a n) *\<^sub>C eigenvalues_of_P a n)  sums  pos_op a\<close>  (is ?thesis1)
    and spectral_decomp_tendsto_neg_op: \<open>(\<lambda>n. - min (eigenvalues_of a n) 0 *\<^sub>C eigenvalues_of_P a n)  sums  neg_op a\<close>  (is ?thesis2)
proof -
  define I J where \<open>I = {n. eigenvalues_of a n \<ge> 0}\<close>
    and \<open>J = {n. eigenvalues_of a n \<le> 0}\<close>
  define R S where \<open>R = (\<Squnion>n\<in>I. eigenvalues_of_E a n)\<close>
    and \<open>S = (\<Squnion>n\<in>J. eigenvalues_of_E a n)\<close>
  define aR aS where \<open>aR = a o\<^sub>C\<^sub>L Proj R\<close> and \<open>aS = - a o\<^sub>C\<^sub>L Proj S\<close>
  have eigenvalues_of_cases: \<open>(0 < eigenvalues_of a n \<Longrightarrow> P) \<Longrightarrow>
    (eigenvalues_of a n < 0 \<Longrightarrow> P) \<Longrightarrow>
    (eigenvalues_of a n = 0 \<Longrightarrow> P) \<Longrightarrow> P\<close> for n P
    apply atomize_elim
    using reals_zero_comparable[OF eigenvalues_of_real[OF assms, of n]]
    by auto
  have PRP: \<open>eigenvalues_of_P a n o\<^sub>C\<^sub>L Proj R = eigenvalues_of_P a n\<close> if \<open>n \<in> I\<close> for n
    by (auto intro!: Proj_o_Proj_subspace_left
        simp add: R_def SUP_upper that eigenvalues_of_P_def)
  have PR0: \<open>eigenvalues_of_P a n o\<^sub>C\<^sub>L Proj R = 0\<close> if \<open>n \<notin> I\<close> for n
    apply (cases rule: eigenvalues_of_cases[of n])
    using that
    by (auto intro!: orthogonal_spaces_SUP_right eigenvalues_of_E_orthogonal assms
        simp: eigenvalues_of_P_def R_def I_def
        simp flip: orthogonal_projectors_orthogonal_spaces)
  have PSP: \<open>eigenvalues_of_P a n o\<^sub>C\<^sub>L Proj S = eigenvalues_of_P a n\<close> if \<open>n \<in> J\<close> for n
    by (auto intro!: Proj_o_Proj_subspace_left
        simp add: S_def SUP_upper that eigenvalues_of_P_def)
  have PS0: \<open>eigenvalues_of_P a n o\<^sub>C\<^sub>L Proj S = 0\<close> if \<open>n \<notin> J\<close> for n
    apply (cases rule: eigenvalues_of_cases[of n])
    using that
    by (auto intro!: orthogonal_spaces_SUP_right eigenvalues_of_E_orthogonal assms
        simp: eigenvalues_of_P_def S_def J_def
        simp flip: orthogonal_projectors_orthogonal_spaces)
  from spectral_decomp_tendsto[OF assms]
  have \<open>(\<lambda>n. (eigenvalues_of a n *\<^sub>C eigenvalues_of_P a n) o\<^sub>C\<^sub>L Proj R) sums aR\<close>
    unfolding aR_def
    apply (rule bounded_linear.sums[rotated])
    by (intro bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left)
  then have sum_aR: \<open>(\<lambda>n. max 0 (eigenvalues_of a n) *\<^sub>C eigenvalues_of_P a n)  sums  aR\<close>
    apply (rule sums_cong[THEN iffD1, rotated])
    by (simp add: I_def PR0 PRP max_def)
  from sum_aR have \<open>aR \<ge> 0\<close>
    apply (rule sums_pos_cblinfun)
    by (auto intro!: eigenvalues_of_P_pos scaleC_nonneg_nonneg simp: max_def)
  from spectral_decomp_tendsto[OF assms]
  have \<open>(\<lambda>n. eigenvalues_of a n *\<^sub>C eigenvalues_of_P a n o\<^sub>C\<^sub>L Proj S) sums - aS\<close>
    unfolding aS_def minus_minus cblinfun_compose_uminus_left
    apply (rule bounded_linear.sums[rotated])
    by (intro bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left)
  then have sum_aS': \<open>(\<lambda>n. min (eigenvalues_of a n) 0 *\<^sub>C eigenvalues_of_P a n)  sums  - aS\<close>
    apply (rule sums_cong[THEN iffD1, rotated])
    by (simp add: J_def PS0 PSP min_def)
  then have sum_aS: \<open>(\<lambda>n. - min (eigenvalues_of a n) 0 *\<^sub>C eigenvalues_of_P a n)  sums  aS\<close>
    using sums_minus by fastforce 
  from sum_aS have \<open>aS \<ge> 0\<close>
    apply (rule sums_pos_cblinfun)
    apply (auto intro!: simp: max_def)
    by (auto intro!: eigenvalues_of_P_pos scaleC_nonpos_nonneg simp: min_def)
  from sum_aR sum_aS'
  have \<open>(\<lambda>n. max 0 (eigenvalues_of a n) *\<^sub>C eigenvalues_of_P a n
           + min (eigenvalues_of a n) 0 *\<^sub>C eigenvalues_of_P a n) sums (aR - aS)\<close>
    using sums_add by fastforce
  then have \<open>(\<lambda>n. eigenvalues_of a n *\<^sub>C eigenvalues_of_P a n) sums (aR - aS)\<close>
  proof (rule sums_cong[THEN iffD1, rotated])
    fix n
    have \<open>max 0 (eigenvalues_of a n) + min (eigenvalues_of a n) 0
          = eigenvalues_of a n\<close>
      apply (cases rule: eigenvalues_of_cases[of n])
      by (auto intro!: simp: max_def min_def)
    then
    show \<open>max 0 (eigenvalues_of a n) *\<^sub>C eigenvalues_of_P a n +
          min (eigenvalues_of a n) 0 *\<^sub>C eigenvalues_of_P a n =
          eigenvalues_of a n *\<^sub>C eigenvalues_of_P a n\<close>
      by (metis scaleC_left.add) 
  qed
  with spectral_decomp_tendsto[OF assms]
  have \<open>aR - aS = a\<close>
    using sums_unique2 by blast 
  have \<open>aR o\<^sub>C\<^sub>L aS = 0\<close>
    by (metis (no_types, opaque_lifting) Proj_idempotent \<open>0 \<le> aR\<close> \<open>aR - aS = a\<close> aR_def add_cancel_left_left add_minus_cancel adj_0 adj_Proj adj_cblinfun_compose assms(2) cblinfun_compose_minus_right comparable_hermitean lift_cblinfun_comp(2) selfadjoint_def uminus_add_conv_diff) 
  have \<open>aR = pos_op a\<close> and \<open>aS = neg_op a\<close>
    by (intro pos_op_neg_op_unique[where b=aR and c=aS]
        \<open>aR - aS = a\<close> \<open>0 \<le> aR\<close> \<open>0 \<le> aS\<close> \<open>aR o\<^sub>C\<^sub>L aS = 0\<close>)+
  with sum_aR and sum_aS
  show ?thesis1 and ?thesis2
    by auto
qed

lemma  spectral_decomp_tendsto_abs_op:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>(\<lambda>n. cmod (eigenvalues_of a n) *\<^sub>R eigenvalues_of_P a n)  sums  abs_op a\<close>
proof -
  from spectral_decomp_tendsto_pos_op[OF assms] spectral_decomp_tendsto_neg_op[OF assms]
  have \<open>(\<lambda>n. max 0 (eigenvalues_of a n) *\<^sub>C eigenvalues_of_P a n
           + - min (eigenvalues_of a n) 0 *\<^sub>C eigenvalues_of_P a n) sums (pos_op a + neg_op a)\<close>
    using sums_add by blast
  then have \<open>(\<lambda>n. cmod (eigenvalues_of a n) *\<^sub>R eigenvalues_of_P a n)  sums  (pos_op a + neg_op a)\<close>
    apply (rule sums_cong[THEN iffD1, rotated])
    using eigenvalues_of_real[OF assms]
    apply (simp add: complex_is_Real_iff cmod_def max_def min_def less_eq_complex_def scaleR_scaleC
        flip: scaleC_add_right)
    by (metis complex_surj zero_complex.code) 
  then show ?thesis
    by (simp add: pos_op_plus_neg_op) 
qed


lift_definition eigenvalues_of_P_tc :: \<open>('a::chilbert_space, 'a) trace_class \<Rightarrow> nat \<Rightarrow> ('a, 'a) trace_class\<close> is
  eigenvalues_of_P
  using finite_rank_trace_class eigenvalues_of_P_finite_rank trace_class_compact by blast

lift_definition eigenvalues_of_tc :: \<open>('a::chilbert_space, 'a) trace_class \<Rightarrow> nat \<Rightarrow> complex\<close> is
  eigenvalues_of.

lemma eigenvalues_of_P_tc_finite_rank: 
  assumes \<open>adj_tc a = a\<close>
  shows \<open>finite_rank_tc (eigenvalues_of_P_tc a n)\<close>
  using assms apply transfer
  by (simp add: eigenvalues_of_P_finite_rank trace_class_compact)


lemma suminf_eqI:
  fixes x :: \<open>_::{comm_monoid_add,t2_space}\<close>
  assumes \<open>f sums x\<close>
  shows \<open>suminf f = x\<close>
  using assms
  by (auto intro!: simp: sums_iff)

lemma suminf_If_finite_set:
  fixes f :: \<open>_ \<Rightarrow> _::{comm_monoid_add,t2_space}\<close>
  assumes \<open>finite F\<close>
  shows \<open>(\<Sum>x\<in>F. f x) = (\<Sum>x. if x\<in>F then f x else 0)\<close>
  by (auto intro!: suminf_eqI[symmetric] sums_If_finite_set simp: assms)

lemma adj_abs_op[simp]: \<open>(abs_op a)* = abs_op a\<close>
  by (simp add: positive_hermitianI) 

lemma abs_op_plus_orthogonal:
  assumes \<open>a* o\<^sub>C\<^sub>L b = 0\<close> and \<open>a o\<^sub>C\<^sub>L b* = 0\<close>
  shows \<open>abs_op (a + b) = abs_op a + abs_op b\<close>
proof (rule abs_opI[symmetric])
  have ba: \<open>b* o\<^sub>C\<^sub>L a = 0\<close>
    apply (rule cblinfun_eqI, rule cinner_extensionality)
    apply (simp add: cinner_adj_right flip: cinner_adj_left)
    by (simp add: assms simp_a_oCL_b') 
  have abs_ab: \<open>abs_op a o\<^sub>C\<^sub>L abs_op b = 0\<close>
  proof -
    have \<open>abs_op b *\<^sub>S \<top> = - kernel (abs_op b)\<close>
      by (simp add: kernel_compl_adj_range positive_hermitianI) 
    also have \<open>\<dots> = - kernel b\<close>
      by simp
    also have \<open>\<dots> = (b*) *\<^sub>S \<top>\<close>
      by (simp add: kernel_compl_adj_range) 
    also have \<open>\<dots> \<le> kernel a\<close>
      apply (auto intro!: cblinfun_image_less_eqI kernel_memberI simp: )
      by (simp add: assms flip: cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots> = kernel (abs_op a)\<close>
      by simp 
    finally show \<open>abs_op a o\<^sub>C\<^sub>L abs_op b = 0\<close>
      by (metis Proj_compose_cancelI cblinfun_compose_Proj_kernel cblinfun_compose_assoc cblinfun_compose_zero_left) 
  qed
  then have abs_ba: \<open>abs_op b o\<^sub>C\<^sub>L abs_op a = 0\<close>
    by (metis abs_op_pos adj_0 adj_cblinfun_compose positive_hermitianI) 
  have \<open>(a + b)* o\<^sub>C\<^sub>L (a + b) = (a*) o\<^sub>C\<^sub>L a + (b*) o\<^sub>C\<^sub>L b\<close>
    by (simp add: cblinfun_compose_add_left cblinfun_compose_add_right adj_plus assms ba)
  also have \<open>\<dots> = (abs_op a + abs_op b)* o\<^sub>C\<^sub>L (abs_op a + abs_op b)\<close>
    by (simp add: cblinfun_compose_add_left cblinfun_compose_add_right adj_plus abs_ab abs_ba flip: abs_op_square)
  finally show \<open>(abs_op a + abs_op b)* o\<^sub>C\<^sub>L (abs_op a + abs_op b) = (a + b)* o\<^sub>C\<^sub>L (a + b)\<close>
    by simp
  show \<open>0 \<le> abs_op a + abs_op b\<close>
    by simp 
qed


lemma trace_norm_plus_orthogonal:
  assumes \<open>trace_class a\<close> and \<open>trace_class b\<close>
  assumes \<open>a* o\<^sub>C\<^sub>L b = 0\<close> and \<open>a o\<^sub>C\<^sub>L b* = 0\<close>
  shows \<open>trace_norm (a + b) = trace_norm a + trace_norm b\<close>
proof -
  have \<open>trace_norm (a + b) = trace (abs_op (a + b))\<close>
    by simp
  also have \<open>\<dots> = trace (abs_op a + abs_op b)\<close>
   by (simp add: abs_op_plus_orthogonal assms)
  also have \<open>\<dots> = trace (abs_op a) + trace (abs_op b)\<close>
    by (simp add: assms trace_plus)
  also have \<open>\<dots> = trace_norm a + trace_norm b\<close>
    by simp
  finally show ?thesis
    using of_real_hom.eq_iff by blast
qed

lemma norm_tc_plus_orthogonal:
  assumes \<open>tc_compose (adj_tc a) b = 0\<close> and \<open>tc_compose a (adj_tc b) = 0\<close>
  shows \<open>norm (a + b) = norm a + norm b\<close>
  using assms apply transfer
  by (auto intro!: trace_norm_plus_orthogonal)

(* lemma trace_class_sum:
  fixes t :: \<open>_ \<Rightarrow> (_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space)\<close>
  assumes \<open>\<And>i. i \<in> F \<Longrightarrow> trace_class (t i)\<close>
  shows \<open>trace_class (\<Sum>i\<in>F. t i)\<close>
  apply (insert assms, induction F rule: infinite_finite_induct)
  byauto
apply (auto intro!: simp: )
try0
sledgehammer [dont_slice]
by - *)


lemma trace_norm_sum_exchange:
  fixes t :: \<open>_ \<Rightarrow> (_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space)\<close>
  assumes \<open>\<And>i. i \<in> F \<Longrightarrow> trace_class (t i)\<close>
  assumes \<open>\<And>i j. i \<in> F \<Longrightarrow> j \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> (t i)* o\<^sub>C\<^sub>L t j = 0\<close>
  assumes \<open>\<And>i j. i \<in> F \<Longrightarrow> j \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> t i o\<^sub>C\<^sub>L (t j)* = 0\<close>
  shows \<open>trace_norm (\<Sum>i\<in>F. t i) = (\<Sum>i\<in>F. trace_norm (t i))\<close>
proof (insert assms, induction F rule:infinite_finite_induct)
  case (infinite A)
  then show ?case
    by simp
next
  case empty
  show ?case
    by simp
next
  case (insert x F)
  have \<open>trace_norm (\<Sum>i\<in>insert x F. t i) = trace_norm (t x + (\<Sum>x\<in>F. t x))\<close>
    by (simp add: insert)
  also have \<open>\<dots> = trace_norm (t x) + trace_norm (\<Sum>x\<in>F. t x)\<close>
  proof (rule trace_norm_plus_orthogonal)
    show \<open>trace_class (t x)\<close>
      by (simp add: insert.prems)
    show \<open>trace_class (\<Sum>x\<in>F. t x)\<close>
      by (simp add: trace_class_sum insert.prems)
    show \<open>t x* o\<^sub>C\<^sub>L (\<Sum>x\<in>F. t x) = 0\<close>
      by (auto intro!: sum.neutral insert.prems simp: cblinfun_compose_sum_right sum_adj insert.hyps)
    show \<open>t x o\<^sub>C\<^sub>L (\<Sum>x\<in>F. t x)* = 0\<close>
      by (auto intro!: sum.neutral insert.prems simp: cblinfun_compose_sum_right sum_adj insert.hyps)
  qed
  also have \<open>\<dots> = trace_norm (t x) + (\<Sum>x\<in>F. trace_norm (t x))\<close>
    apply (subst insert.IH)
    by (simp_all add: insert.prems)
  also have \<open>\<dots> = (\<Sum>i\<in>insert x F. trace_norm (t i))\<close>
    by (simp add: insert)
  finally show ?case
    by -
qed

lemma norm_tc_sum_exchange:
  assumes \<open>\<And>i j. i \<in> F \<Longrightarrow> j \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> tc_compose (adj_tc (t i)) (t j) = 0\<close>
  assumes \<open>\<And>i j. i \<in> F \<Longrightarrow> j \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> tc_compose (t i) (adj_tc (t j)) = 0\<close>
  shows \<open>norm (\<Sum>i\<in>F. t i) = (\<Sum>i\<in>F. norm (t i))\<close>
  using assms apply transfer
  by (auto intro!: trace_norm_sum_exchange)

lemma spectral_decomp_summable_tc:
  assumes \<open>selfadjoint_tc a\<close>
  shows \<open>(\<lambda>n. eigenvalues_of_tc a n *\<^sub>C eigenvalues_of_P_tc a n)  abs_summable_on  UNIV\<close>
proof (intro nonneg_bounded_partial_sums_imp_summable_on norm_ge_zero eventually_finite_subsets_at_top_weakI)
  define a' where \<open>a' = from_trace_class a\<close>
  then have [transfer_rule]: \<open>cr_trace_class a' a\<close>
    by (simp add: cr_trace_class_def)

  have \<open>compact_op a'\<close>
    by (auto intro!: trace_class_compact simp: a'_def)
  have \<open>selfadjoint a'\<close>
    using a'_def assms selfadjoint_tc.rep_eq by blast 
  fix F :: \<open>nat set\<close> assume \<open>finite F\<close>
  define R where \<open>R = (\<Squnion>n\<in>F. eigenvalues_of_E a' n)\<close>
  have \<open>(\<Sum>x\<in>F. norm (eigenvalues_of_tc a x *\<^sub>C eigenvalues_of_P_tc a x))
        = norm (\<Sum>x\<in>F. eigenvalues_of_tc a x *\<^sub>C eigenvalues_of_P_tc a x)\<close>
  proof (rule norm_tc_sum_exchange[symmetric]; transfer; rename_tac n m F)
    fix n m :: nat assume (* \<open>n \<in> F\<close> and \<open>m \<in> F\<close> and *) \<open>n \<noteq> m\<close>
    then have *: \<open>Proj (eigenvalues_of_E a' n) o\<^sub>C\<^sub>L Proj (eigenvalues_of_E a' m) = 0\<close> if \<open>eigenvalues_of a' n \<noteq> 0\<close> and \<open>eigenvalues_of a' m \<noteq> 0\<close>
      by (auto intro!: orthogonal_projectors_orthogonal_spaces[THEN iffD1] eigenvalues_of_E_orthogonal \<open>compact_op a'\<close> \<open>selfadjoint a'\<close>simp: )
    show \<open>(eigenvalues_of a' n *\<^sub>C eigenvalues_of_P a' n)* o\<^sub>C\<^sub>L eigenvalues_of a' m *\<^sub>C eigenvalues_of_P a' m = 0\<close>
      by (auto intro!: * simp: eigenvalues_of_P_def adj_Proj)
    show \<open>eigenvalues_of a' n *\<^sub>C eigenvalues_of_P a' n o\<^sub>C\<^sub>L (eigenvalues_of a' m *\<^sub>C eigenvalues_of_P a' m)* = 0\<close>
      by (auto intro!: * simp: eigenvalues_of_P_def adj_Proj)
  qed
  also have \<open>\<dots> = trace_norm (\<Sum>x\<in>F. eigenvalues_of a' x *\<^sub>C eigenvalues_of_P a' x)\<close>
    by (metis (no_types, lifting) a'_def eigenvalues_of_P_tc.rep_eq eigenvalues_of_tc.rep_eq from_trace_class_sum norm_trace_class.rep_eq scaleC_trace_class.rep_eq sum.cong) 
  also have \<open>\<dots> = trace_norm (\<Sum>x. if x\<in>F then eigenvalues_of a' x *\<^sub>C eigenvalues_of_P a' x else 0)\<close>
    by (simp add: \<open>finite F\<close> suminf_If_finite_set) 
  also have \<open>\<dots> = trace_norm (\<Sum>x. (eigenvalues_of a' x *\<^sub>C eigenvalues_of_P a' x) o\<^sub>C\<^sub>L Proj R)\<close>
  proof -
    have \<open>eigenvalues_of_P a' n = eigenvalues_of_P a' n o\<^sub>C\<^sub>L Proj R\<close> if \<open>n \<in> F\<close> for n
      by (auto intro!: Proj_o_Proj_subspace_left[symmetric] SUP_upper that simp: eigenvalues_of_P_def R_def)
    moreover have \<open>eigenvalues_of_P a' n o\<^sub>C\<^sub>L Proj R = 0\<close> if \<open>n \<notin> F\<close> for n
      using that
      by (auto intro!: orthogonal_spaces_SUP_right eigenvalues_of_E_orthogonal \<open>compact_op a'\<close> \<open>selfadjoint a'\<close>
          simp: eigenvalues_of_P_def R_def
          simp flip: orthogonal_projectors_orthogonal_spaces)
    ultimately show ?thesis
      by (auto intro!: arg_cong[where f=trace_norm] suminf_cong)
  qed
  also have \<open>\<dots> = trace_norm ((\<Sum>x. eigenvalues_of a' x *\<^sub>C eigenvalues_of_P a' x) o\<^sub>C\<^sub>L Proj R)\<close>
    apply (intro arg_cong[where f=trace_norm] bounded_linear.suminf[symmetric] 
        bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left sums_summable)
    using \<open>compact_op a'\<close> \<open>selfadjoint a'\<close> spectral_decomp_tendsto by blast
  also have \<open>\<dots> = trace_norm (a' o\<^sub>C\<^sub>L Proj R)\<close>
    using spectral_decomp_tendsto[OF \<open>compact_op a'\<close> \<open>selfadjoint a'\<close>] sums_unique by fastforce 
  also have \<open>\<dots> \<le> trace_norm a' * norm (Proj R)\<close>
    by (auto intro!: trace_norm_comp_left simp: a'_def)
  also have \<open>\<dots> \<le> trace_norm a'\<close>
    by (simp add: mult_left_le norm_Proj_leq1) 
  finally show \<open>(\<Sum>x\<in>F. norm (eigenvalues_of_tc a x *\<^sub>C eigenvalues_of_P_tc a x)) \<le> trace_norm a'\<close>
    by -
qed

lemma spectral_decomp_has_sum_tc:
  assumes \<open>selfadjoint_tc a\<close>
  shows \<open>((\<lambda>n. eigenvalues_of_tc a n *\<^sub>C eigenvalues_of_P_tc a n)  has_sum  a) UNIV\<close>
proof -
  define a' b b' where \<open>a' = from_trace_class a\<close>
    and \<open>b = (\<Sum>\<^sub>\<infinity>n. eigenvalues_of_tc a n *\<^sub>C eigenvalues_of_P_tc a n)\<close> and \<open>b' = from_trace_class b\<close>
  have [simp]: \<open>compact_op a'\<close>
    by (auto intro!: trace_class_compact simp: a'_def)
  have [simp]: \<open>selfadjoint a'\<close>
    using a'_def assms selfadjoint_tc.rep_eq by blast 
  have [simp]: \<open>trace_class b'\<close>
    by (simp add: b'_def) 
  from spectral_decomp_summable_tc[OF assms]
  have has_sum_b: \<open>((\<lambda>n. eigenvalues_of_tc a n *\<^sub>C eigenvalues_of_P_tc a n)  has_sum  b) UNIV\<close>
    by (metis abs_summable_summable b_def summable_iff_has_sum_infsum) 
  then have \<open>((\<lambda>F. \<Sum>n\<in>F. eigenvalues_of_tc a n *\<^sub>C eigenvalues_of_P_tc a n) \<longlongrightarrow> b) (finite_subsets_at_top UNIV)\<close>
    by (simp add: has_sum_def)
  then have \<open>((\<lambda>F. norm ((\<Sum>n\<in>F. eigenvalues_of_tc a n *\<^sub>C eigenvalues_of_P_tc a n) - b)) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    using LIM_zero tendsto_norm_zero by blast 
  then have \<open>((\<lambda>F. norm ((\<Sum>n\<in>F. eigenvalues_of_tc a n *\<^sub>C eigenvalues_of_P_tc a n) - b)) \<longlongrightarrow> 0) (filtermap (\<lambda>n. {..<n}) sequentially)\<close>
    by (meson filterlim_compose filterlim_filtermap filterlim_lessThan_at_top) 
  then have \<open>((\<lambda>m. norm ((\<Sum>n\<in>{..<m}. eigenvalues_of_tc a n *\<^sub>C eigenvalues_of_P_tc a n) - b)) \<longlongrightarrow> 0) sequentially\<close>
    by (simp add: filterlim_filtermap) 
  then have \<open>((\<lambda>m. trace_norm ((\<Sum>n\<in>{..<m}. eigenvalues_of a' n *\<^sub>C eigenvalues_of_P a' n) - b')) \<longlongrightarrow> 0) sequentially\<close>
    unfolding a'_def b'_def
    by transfer
  then have \<open>((\<lambda>m. norm ((\<Sum>n\<in>{..<m}. eigenvalues_of a' n *\<^sub>C eigenvalues_of_P a' n) - b')) \<longlongrightarrow> 0) sequentially\<close>
    apply (rule tendsto_0_le[where K=1])
    by (auto intro!: eventually_sequentiallyI norm_leq_trace_norm trace_class_minus
        trace_class_sum trace_class_scaleC eigenvalues_of_P_finite_rank
        intro: finite_rank_trace_class)
  then have \<open>(\<lambda>n. eigenvalues_of a' n *\<^sub>C eigenvalues_of_P a' n) sums b'\<close>
    using LIM_zero_cancel sums_def tendsto_norm_zero_iff by blast 
  moreover have \<open>(\<lambda>n. eigenvalues_of a' n *\<^sub>C eigenvalues_of_P a' n) sums a'\<close>
    using \<open>compact_op a'\<close> \<open>selfadjoint a'\<close> by (rule spectral_decomp_tendsto)
  ultimately have \<open>a = b\<close>
    using a'_def b'_def from_trace_class_inject sums_unique2 by blast
  with has_sum_b show ?thesis
    by simp
qed

lemma spectral_decomp_tendsto_tc:
  assumes \<open>selfadjoint_tc a\<close>
  shows \<open>(\<lambda>n. eigenvalues_of_tc a n *\<^sub>C eigenvalues_of_P_tc a n)  sums  a\<close>
  using assms has_sum_imp_sums spectral_decomp_has_sum_tc by blast 


lemma finite_rank_tc_dense: \<open>closure (Collect finite_rank_tc :: ('a::chilbert_space,'a) trace_class set) = UNIV\<close>
proof (intro order_top_class.top_le subsetI)
  fix a :: \<open>('a,'a) trace_class\<close>
  wlog selfadj: \<open>selfadjoint_tc a\<close> goal \<open>a \<in> closure (Collect finite_rank_tc)\<close> generalizing a
  proof -
    define b c where \<open>b = a + adj_tc a\<close> and \<open>c = \<i> *\<^sub>C (a - adj_tc a)\<close>
    have \<open>adj_tc b = b\<close>
      unfolding b_def
      apply transfer
      by (simp add: adj_plus)
    have \<open>adj_tc c = c\<close>
      unfolding c_def
      apply transfer
      apply (simp add: adj_minus)
      by (metis minus_diff_eq scaleC_right.minus)
    have abc: \<open>a = (1/2) *\<^sub>C b + (-\<i>/2) *\<^sub>C c\<close>
      apply (simp add: b_def c_def)
      by (metis (no_types, lifting) cross3_simps(8) diff_add_cancel group_cancel.add2 scaleC_add_right scaleC_half_double)
    have \<open>b \<in> closure (Collect finite_rank_tc)\<close> and \<open>c \<in> closure (Collect finite_rank_tc)\<close>
      using \<open>adj_tc b = b\<close> \<open>adj_tc c = c\<close> hypothesis selfadjoint_tc_def' by auto
    with abc have \<open>a \<in> cspan (closure (Collect finite_rank_tc))\<close>
      by (metis complex_vector.span_add complex_vector.span_clauses(1) complex_vector.span_clauses(4))
    also have \<open>\<dots> \<subseteq> closure (cspan (Collect finite_rank_tc))\<close>
      by (simp add: closure_mono complex_vector.span_minimal complex_vector.span_superset)
    also have \<open>\<dots> = closure (Collect finite_rank_tc)\<close>
      by (metis Set.basic_monos(1) complex_vector.span_minimal complex_vector.span_superset csubspace_finite_rank_tc subset_antisym)
    finally show ?thesis
      by -
  qed
  then have \<open>(\<lambda>n. eigenvalues_of_tc a n *\<^sub>C eigenvalues_of_P_tc a n)  sums  a\<close>
    by (simp add: spectral_decomp_tendsto_tc)
  moreover from selfadj 
  have \<open>finite_rank_tc (\<Sum>i<n. eigenvalues_of_tc a i *\<^sub>C eigenvalues_of_P_tc a i)\<close> for n
    apply (induction n)
     by (auto intro!: finite_rank_tc_plus eigenvalues_of_P_tc_finite_rank finite_rank_tc_scale
        simp: selfadjoint_tc_def')
  ultimately show \<open>a \<in> closure (Collect finite_rank_tc)\<close>
    unfolding sums_def closure_sequential
    apply (auto intro!: simp: sums_def closure_sequential)
    by meson
qed

lemma finite_rank_tc_def': \<open>finite_rank_tc A \<longleftrightarrow> A \<in> cspan (Collect rank1_tc)\<close>
  apply transfer
  apply (auto simp: finite_rank_def)
   apply (metis (no_types, lifting) Collect_cong rank1_trace_class)
  by (metis (no_types, lifting) Collect_cong rank1_trace_class)


end
